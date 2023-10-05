# Formalization of Modal Logic in Lean 4 

## Contents

- `/ModalLogic`
    - `/Arithmetic`: 理想的な性質を満たした算術の体系における不完全性の証明など
        - `/IT1.lean`: Gödelの第1不完全性定理
            - `GoedelSentenceUnprovability`: Hilbert-Bernays無矛盾ならGödel文は証明不能である．
            - `GoedelSentenceUnprovability`: $Σ_1$健全ならGödel文は証明不能である．
        - `/IT2.lean`: Gödelの第2不完全性定理
            - `equiv_LConsistencyOf_GoedelSentence`: 全てのGödel文はLöb無矛盾文と内で同値である．
            - `LConsistencyOfUnprovablility_of_HBConsistent`: Hilbert-Bernays無矛盾ならLöb無矛盾文は証明不能である．
            - `LConsistencyOfUnprovablility_of_HBConsistent`: $Σ_1$健全ならLöb無矛盾文は反証不能である．
        - `/Loeb_with_IT2.lean`: 第2不完全性定理を用いたLöbの定理の証明
        - `/Loeb_without_IT2.lean`: 第2不完全性定理を用いないLöbの定理の証明
            - `HenkinSentenceProvablility`: Henkin文は証明可能である
        - `/Notation.lean`: 算術の体系，無矛盾性，導出可能性条件などの定義
    - `/PropositionalLogic`: 命題論理
        - `/DeductionSystem`: 自然演繹の体系


## License

[![GitHub](https://img.shields.io/github/license/sno2wman/lean4-modallogic?style=flat-square)](https://github.com/SnO2WMaN/lean4-modallogic/blob/main/LICENSE)
