{-# LANGUAGE StaticPointers, FlexibleInstances #-}
import Haste.App
import Haste.DOM
import Haste.Events
import System.Directory

instance Node Server

-- A log entry data-type
data LogEntry = LogEntry { Date :: Int,
                           Originator :: String,
                           Type :: String,
                           Status :: String,
                           Comments :: String,
                           Doc :: FilePath
                         }

-- A log header
data LogHeader = LogHeader { ProjName :: String,
                             Author :: String,
                             Members :: [String]
                           }
                           
-- `appendChildren parent children` adds a list of children to a parent element
appendChildren :: Elem -> [Elem] -> Client ()
appendChildren parent children = sequence_ [appendChild parent c | c <- children]

-- Server sanity-check function: Prints to CLI
greet :: RemotePtr (String -> Server ())
greet = static (native $ remote $ liftIO . putStrLn)

-- Get log files from the server
getFiles :: RemotePtr (String -> Server [FilePath])
getFiles = static (remote $ liftIO . listDirectory)

-- File name extension slicing
sliceExt :: FilePath -> String
sliceExt filename = takeWhile (/='.') filename

-- sanitize input filepaths server-side to prevent malicious access
sanitizeFilepath :: RemotePtr (FilePath -> Server FilePath)
sanitizeFilepath = static (remote $ return . sanitize)

-- Helper sanitize function
sanitize :: FilePath -> FilePath
sanitize [] = []
sanitize (x:[]) = if x == '.' then "?" else x:[] 
sanitize (x:y:xs) = if (x == '.' && y == '.') then "?" else x:(sanitize (y:xs))

-- Put files retrieved from the server into the browser
putFiles :: [FilePath] -> Client ()
putFiles [] = return ()
putFiles (file:filelist) = do
  withElem "list" $ \list -> do
    li <- newElem "li" `with` [ attr "class" =: "list-item", prop "innerHTML" =: (sliceExt file ++ "   ") ]
    add <- newElem "a" `with` [ attr "href" =: "#", prop "innerHTML" =: "Add" ]
    spacing <- newElem "span" `with` [ prop "innerHTML" =: "     " ]
    -- Remember to change this to a .pdf relative file path once features are implemented!
    dl <- newElem "a" `with` [ attr "href" =: ("./data/" ++ file) , prop "innerHTML" =: "Download" ]
    appendChild list li
    appendChildren li [add, spacing, dl]
    putFiles filelist

-- Takes a filename, and creates a log entry form
-- appendForm :: String -> Client ()

-- Takes a filename, a list of log headers, and creates a new latex project log file
-- This is (obviously) done server-side. Also, pdflatex should be run
-- after appending (temporarily for now, as this is not so efficient)
-- createLog :: RemotePtr (String -> [String] -> Server ()) 

-- Takes a filepath, a list of log entries, and appends to the latex project log file
-- Also done server-side
-- appendLog :: RemotePtr (FilePath -> [String] -> Server ())

-- Run the application
main = runApp [start (Proxy :: Proxy Server)] $ do
  -- fetch stored tex files. Sanitize the input first!
  name <- dispatch sanitizeFilepath "../ExpenseApp"
  files <- dispatch getFiles name
  putFiles files
  withElem "btn" $ \btn -> do
    btn `onEvent` Click $ \_ -> do
      alert (toJSString $ "ok")
      
  return ()
{-
main :: IO ()
main = do
  ul <- elemsByQS document "ul#demo-list"
  case ul of
    (el:_) -> mapQS_ document "#demo-list li" (handleRemove el)
    _      -> error "Element 'ul#demo-list' not found"

handleRemove :: Elem -> Elem -> IO HandlerInfo
handleRemove ul li = do
  onEvent li Click $ \_ -> do
    deleteChild ul li
-}