# Basic Commands

- rw [`lemma`]: Substitutes `lemma` to the current goal (dk what happens when there are many)
- nth_rw k [`lemma`]: Substitutes only the k^th occurrence of `lemma`
- rw [\l `lemma`]: Substitutes `lemma` in reverse
- ring: Tries to finish off the proof using ring theorems/lemmas

Theorem Declaration:

theorem name_of_theorem (variable1 variable2 : type) : theorem_statement := proof

theorem name_of_theorem {variable1 variable2 : type} (assumptions) : theorem_statement := proof
