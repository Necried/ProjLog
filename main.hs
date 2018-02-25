{-# LANGUAGE StaticPointers, FlexibleInstances #-}
import Haste.App
import Haste.DOM
import Haste.Events
import System.Directory

instance Node Server

-- `appendChildren parent children` adds a list of children to a parent element
appendChildren :: Elem -> [Elem] -> Client ()
appendChildren parent children = sequence_ [appendChild parent c | c <- children]

-- Server sanity-check function
greet :: RemotePtr (String -> Server ())
greet = static (native $ remote $ liftIO . putStrLn)

-- Get log files from the server
getFiles :: RemotePtr (String -> Server [FilePath])
getFiles = static (remote $ liftIO . listDirectory)

-- Put files retrieved from the server into the browser
putFiles :: [FilePath] -> Client ()
putFiles [] = do
  withElem "list" $ \list -> do
    submit <- newElem "input" `with` [ attr "type" =: "submit",
                                       attr "name" =: "Submit",
                                       attr "value" =: "Edit selected file" ]
    download <- newElem "input" `with` [ attr "type" =: "submit",
                                       attr "name" =: "Download",
                                       attr "value" =: "Download selected file" ]
    break <- newElem "br"
    appendChildren list [break, submit, download]
putFiles (file:filelist) = do
  withElem "list" $ \list -> do
    identifier <- newElem "span" `with` [ prop "innerHTML" =: file ]
    radio <- newElem "input" `with` [ attr "type"  =: "radio",
                                         attr "value" =: file,
                                         attr "name"  =: "filetype",
                                         prop "innerHTML" =: file ]
    break <- newElem "br"
    appendChildren list [radio, identifier, break]
    putFiles filelist

main = runApp [start (Proxy :: Proxy Server)] $ do
  -- fetch stored tex files
  files <- dispatch getFiles "./data"
  putFiles files
  withElem "Download" $ \dl -> do
    dl `onEvent` Click $ \_ -> do
      filename <- getValue dl "value"
      dispatch greet filename
  withElem "btn" $ \btn -> do
    btn `onEvent` Click $ \_ -> do
      alert (toJSString $ "ok")
  return ()

