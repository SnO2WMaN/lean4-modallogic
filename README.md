# Formalization of Modal Logic in Lean 4

## Disclaimer

現時点で，[iehality/lean4-logic](https://github.com/iehality/lean4-logic)にてこのプロジェクト（様相論理の形式化）は遂行中です．
詳しくは当該リポジトリの`Logic/Modal`ディレクトリを参照して下さい．

## Contents

### `ModalLogic.PropositionalLogic`

- `ModalLogic.PropositionalLogic.DeductionSystem`
  - 自然演繹の体系

### `ModalLogic.Arithmetic`

理想的な性質を満たした算術の体系における不完全性の証明など．

- `ModalLogic.Arithmetic.GoedelSentenceUnprovability`
  - Hilbert-Bernays 無矛盾なら Gödel 文は証明不能である．
- `ModalLogic.Arithmetic.GoedelSentenceUnrefutability`
  - $Σ_1$健全なら Gödel 文は反証不能である．
- `ModalLogic.Arithmetic.equiv_LConsistencyOf_GoedelSentence`
  - 全ての Gödel 文は Löb 無矛盾文と同値である．
- `ModalLogic.Arithmetic.LConsistencyOfUnprovablility_of_HBConsistent`
  - Hilbert-Bernays 無矛盾なら Löb 無矛盾文は証明不能である．
- `ModalLogic.Arithmetic.LConsistencyOfUnrefutability_of_Soundness`
  - $Σ_1$健全なら Löb 無矛盾文は反証不能である．
- `ModalLogic.Arithmetic.Loeb_with_IT2`
  - 第 2 不完全性定理を用いた Löb の定理の証明．
- `ModalLogic.Arithmetic.Loeb_without_IT2`
  - 第 2 不完全性定理を用いない Löb の定理の証明．
- `ModalLogic.Arithmetic.LConsistencyofUnprovability_of_LConsistent`
  - Löb 無矛盾なら Löb 無矛盾文は証明不能である．
- `ModalLogic.Arithmetic.HenkinSentenceProvablility`
  - Henkin 文は証明可能である．

## License

[![GitHub](https://img.shields.io/github/license/sno2wman/lean4-modallogic?style=flat-square)](https://github.com/SnO2WMaN/lean4-modallogic/blob/main/LICENSE)
