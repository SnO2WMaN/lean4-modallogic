# Formalization of Modal Logic in Lean 4 

## Contents

### `ModalLogic.PropositionalLogic`

- `ModalLogic.PropositionalLogic.DeductionSystem`
    - 自然演繹の体系

### `ModalLogic.Arithmetic`

理想的な性質を満たした算術の体系における不完全性の証明など．

- `ModalLogic.Arithmetic.GoedelSentenceUnprovability`
    - Hilbert-Bernays無矛盾ならGödel文は証明不能である．
- `ModalLogic.Arithmetic.GoedelSentenceUnrefutability`
    - $Σ_1$健全ならGödel文は反証不能である．
- `ModalLogic.Arithmetic.equiv_LConsistencyOf_GoedelSentence`
    - 全てのGödel文はLöb無矛盾文と同値である．
- `ModalLogic.Arithmetic.LConsistencyOfUnprovablility_of_HBConsistent`
    - Hilbert-Bernays無矛盾ならLöb無矛盾文は証明不能である．
- `ModalLogic.Arithmetic.LConsistencyOfUnrefutability_of_Soundness`
    - $Σ_1$健全ならLöb無矛盾文は反証不能である．
- `ModalLogic.Arithmetic.Loeb_with_IT2`
    - 第2不完全性定理を用いたLöbの定理の証明．
- `ModalLogic.Arithmetic.Loeb_without_IT2`
    - 第2不完全性定理を用いないLöbの定理の証明．
- `ModalLogic.Arithmetic.HenkinSentenceProvablility`
    - Henkin文は証明可能である．

## License

[![GitHub](https://img.shields.io/github/license/sno2wman/lean4-modallogic?style=flat-square)](https://github.com/SnO2WMaN/lean4-modallogic/blob/main/LICENSE)
