{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           GHC.TypeLits
import           Control.Concurrent.Chan
import           Control.Concurrent.MVar
import           Control.Concurrent
import           Control.Monad (mapM_)
import           Data.Proxy
import qualified Crypto.Poker as Poker
import           Crypto.Random
import           Basement.Imports ((<>))
import           Basement.Bounded
import qualified Basement.Terminal.ANSI as Term
import           Basement.From
import           Basement.Terminal
import           Foundation hiding ((<>))
import           Foundation.Collection (nonEmpty_)
import qualified Prelude (getLine)

type ChannelContent = Poker.Event Poker.Operation
type ServerChan = Chan ChannelContent

type FSCPlayer = (Poker.PlayerIdentity, Poker.VerifyKey, Poker.PublicBroadcast)

type Logging = MVar ()

red = Term.sgrForeground (zn64 1) True
green = Term.sgrForeground (zn64 2) False
yellow = Term.sgrForeground (zn64 3) True
blue = Term.sgrForeground (zn64 4) True
purple = Term.sgrForeground (zn64 5) True
reset = Term.sgrReset

newLogging :: IO Logging
newLogging = newMVar ()

output :: Logging -> String -> IO ()
output lg s = withMVar lg $ \() -> putStrLn s

getLine :: IO String
getLine = fromList <$> Prelude.getLine

input :: Logging -> String -> IO String
input lg s = withMVar lg $ \() -> do
    putStrLn s
    putStr "> " >> getLine

-- | Registration of poker player number and their information
newtype FSC = FSC (MVar [(Poker.PlayerNumber, FSCPlayer)])

newFSC :: IO FSC
newFSC = FSC <$> newMVar []

registerFSC :: FSC
            -> Poker.PlayerIdentity
            -> Poker.VerifyKey
            -> Poker.PublicBroadcast
            -> IO Poker.PlayerNumber
registerFSC (FSC var) playerId vrf pub = do
    modifyMVar var $ \l -> do
        let newId = case l of
                        [] -> 1
                        _  -> 1 + (maximum $ nonEmpty_ $ fmap fst l)
        pure ((newId, fscPlayer) : l, newId)
  where
    fscPlayer = (playerId, vrf, pub)

findByIdentity :: FSC -> Poker.PlayerIdentity -> IO (Maybe Poker.PlayerNumber)
findByIdentity (FSC var) idy = withMVar var $ \l ->
    case filter (\(_, (x, _, _)) -> idy == x) l of
        [(n,_)] -> pure $ Just n
        []      -> pure Nothing
        _       -> error "duplicate identity"

player :: Logging
       -> FSC
       -> ServerChan
       -> Poker.PlayerIdentity
       -> IO ()
player lg fsc servChan myIdentity = do
    chan <- dupChan servChan
    rng <- drgNew
    priv <- Poker.generatePrivateInformation
    processResult chan (Poker.pokerStart (Poker.run @4 priv 10 100) (Poker.initialGameST 100 rng))
  where
    getQualifier myIdentity =
        maybe ("identity(" <> show myIdentity <> ")") show <$> findByIdentity fsc myIdentity
    -- This is the main loop used to route and dispatch messages
    processResult :: Chan (Poker.Event Poker.Operation)
                  -> Poker.Result Poker.Operation Poker.GameST n a
                  -> IO ()
    processResult ch r =
         case r of
            Poker.Failed s -> output lg (purple <> "failed: " <> red <> s <> reset)
            Poker.Ok _st _a  -> output lg "ok"
            Poker.Debug st x next  -> do
                myId <- getQualifier myIdentity
                output lg (blue <> myId <> ": " <> x <> reset)
                processResult ch (next st ())
            Poker.Broadcast st op next -> do
                myId <- getQualifier myIdentity
                playerId <- maybe (error ("no identity registered for " <> show myIdentity)) id <$> findByIdentity fsc myIdentity
                output lg (red <> "broadcast: " <> green <> myId <> reset <> " : " <> show op)
                writeChan servChan (Poker.Event playerId op)
                processResult ch (next st ())
            Poker.FSC st vrf pub next -> do
                pid <- registerFSC fsc myIdentity vrf pub
                output lg ("registered: identity " <> show myIdentity <> " <==> player number " <> show pid)
                processResult ch (next st pid)
            Poker.Next st reason next -> do
                myId <- getQualifier myIdentity
                output lg (yellow <> myId <> red <> ": next: " <> reset <> reason)
                c <- readChan ch
                -- output lg ("next : got : " <> show myIdentity <> " " <> show c)
                processResult ch (next st c)
            Poker.Input st s next -> do
                myId <- getQualifier myIdentity
                action <- input lg (myId <> ": " <> s)
                processResult ch (next st action)

server :: Logging -> ServerChan -> [Poker.PlayerIdentity] -> IO ()
server lg servChan _identities = loop
  where
    loop = do
        --output lg "[SERVER] WAITING"
        -- read the next content and broadcast it to every client
        ev <- readChan servChan
        --output lg ("[SERVER] " <> show pid <> " : " <> show op)
        loop

main :: IO ()
main = do
    let identity = [ 10, 20, 30, 40 ]
        nbPlayers = length identity

    -- Pedersen commitment key generated by a trusted 3rd party.
    -- TODO move to a coin flipping protocol
    lg  <- newLogging
    fsc <- newFSC

    case someNatVal (into @Integer nbPlayers) of
        Just (SomeNat (Proxy :: Proxy n)) -> do
            servChan <- newChan
            mapM_ (forkIO . player lg fsc servChan) $ identity
            server lg servChan identity

        Nothing                           ->
            error "cannot run with this number"
