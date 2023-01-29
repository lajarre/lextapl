module ArithSpec where

import Arith
import Test.Hspec

spec :: Spec
spec = do
  describe "Arith Evaluating bs" $ do
    it "yolo" $ do 0 `shouldBe` 0
