module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Representatives.Data

/-!
# Prospective Rudvalis double-coset representatives

The 847 explicit standard-generator words define elements of the actual
Rudvalis model. Their point maps use at most eight certified max4 letter
maps and twenty standard letter maps, without expanding the long max4 words
at every point. The inverse maps reverse the factors and invert the words.
Both action comparisons are proved in Lean from the certified letter maps.

This is the data interface for the separate double-coset coverage and
normalization-or-generation checks. Neither obligation is asserted here.
The candidate subgroup is exactly `sylowImage fixedSylow`, by the imported
`Generation.FixedSylow`. No max4/max6 cardinality bound is assumed.

Discovery method and reproducible source data are in `Representatives.Data`.
Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher, *Overgroups of Sylow subgroups in sporadic groups* (1986), no.343.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.Representatives

/-- The actual group elements represented by the finite word family. -/
@[expose] public def representative (i : Index) : Model :=
  wordValue (representativeWords i)

/-- Point evaluation using existing kernel-certified letter tables. -/
@[expose] public def representativeMap (i : Index) (x : Fin 4060) : Fin 4060 :=
  localMap (localWords (coordinates i).1) (wordMap (sectorWords (coordinates i).2) x)

/-- The inverse point action, with the two factors in reverse order. -/
@[expose] public def representativeInverseMap (i : Index) (x : Fin 4060) : Fin 4060 :=
  wordMap (inverseWord (sectorWords (coordinates i).2))
    (localMap (inverseWord (localWords (coordinates i).1)) x)

public theorem card_index : Fintype.card Index = 847 := Fintype.card_fin _

/-- The local/sector factorization agrees with the explicit standard word. -/
public theorem representative_factorization (i : Index) :
    representative i = localValue (localWords (coordinates i).1) *
      wordValue (sectorWords (coordinates i).2) := by
  simp only [representative, representativeWords, wordValue_append, expandLocalWord_value,
    localValue]

/-- The exported forward map is the action of the actual model element. -/
public theorem representative_smul (i : Index) (x : Fin 4060) :
    representative i • x = representativeMap i x := by
  rw [representative_factorization, mul_smul, wordValue_smul, localValue_smul]
  rfl

/-- The exported inverse map is the action of the actual inverse element. -/
public theorem representative_inv_smul (i : Index) (x : Fin 4060) :
    (representative i)⁻¹ • x = representativeInverseMap i x := by
  rw [representative_factorization, mul_inv_rev, mul_smul,
    ← wordValue_inverseWord, ← localValue_inverseWord, localValue_smul, wordValue_smul]
  rfl

public theorem representativeWords_zero : representativeWords 0 = [] := by
  decide +kernel

public theorem representative_zero : representative 0 = 1 := by
  change wordValue (representativeWords 0) = 1
  rw [representativeWords_zero]
  simp only [wordValue, List.map_nil, List.prod_nil]

end Rudvalis.SylowOvergroups.TwoCore.Generation.Representatives
