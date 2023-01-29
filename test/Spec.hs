import ArithSpec
import Test.Hspec

main :: IO ()
main =
  hspec $ do
    ArithSpec.spec
