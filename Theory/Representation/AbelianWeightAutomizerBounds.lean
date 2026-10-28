module
public import Theory.Representation.AbelianWeightNormalizerSolvable
public import Theory.GroupTheory.PerfectPairOrder
public import Theory.Quasithin.Rank
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Small-degree bounds for abelian subgroup automizers

Faithfulness on an abelian subgroup makes its normalizer automizer act
faithfully on the occurring character weights. Scalar extension therefore
embeds that automizer into a symmetric group of degree at most the
representation degree. In degree at most eight, its odd prime ranks other
than the three-rank are at most one, by the order of the symmetric group.

This extends `AbelianWeightNormalizerSolvable` to representations faithful
only on the chosen subgroup. The application is the component exclusion
in Aschbacher--Smith 4.4.3 and 10.2.3(2), printed pp.622 and 745.
-/

public section
namespace Representation
variable {E G V : Type*} [Field E] [IsAlgClosed E] [Group G]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Faithfulness on the abelian subgroup suffices for faithfulness on its weights. -/
theorem automizerWeightPerm_injective_of_restriction
    (ρ : Representation E G V) (Q : Subgroup G) [IsMulCommutative Q]
    (hf : Function.Injective (ρ.comp Q.subtype))
    (ho : (Nat.card Q : E) ≠ 0) :
    Function.Injective (automizerWeightPerm ρ Q) := by
  intro a b hab
  apply Subtype.ext
  suffices a.val.symm = b.val.symm by
    simpa using congrArg MulEquiv.symm this
  apply MulEquiv.ext
  intro q
  apply eq_of_characterWeight_values (ρ.comp Q.subtype) hf ho
  intro χ
  exact congrArg (fun π : Equiv.Perm (CharacterWeight (ρ.comp Q.subtype)) =>
    (π χ).val q) hab

/-- The automizer embeds into permutations of at most the representation degree. -/
theorem automizer_embeds_perm_of_faithful_restriction
    (ρ : Representation E G V) (Q : Subgroup G) [IsMulCommutative Q]
    (hf : Function.Injective (ρ.comp Q.subtype))
    (ho : (Nat.card Q : E) ≠ 0) (n : ℕ) (hd : Module.finrank E V ≤ n) :
    ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin n),
      Function.Injective j := by
  classical
  obtain ⟨hfinite,hcard⟩ := characterWeight_card_le (ρ.comp Q.subtype) ho
  let := hfinite
  let := Fintype.ofFinite (CharacterWeight (ρ.comp Q.subtype))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := CharacterWeight (ρ.comp Q.subtype)) (β := Fin n)
    (by simpa only [←Nat.card_eq_fintype_card,Nat.card_fin] using hcard.trans hd)
  exact ⟨(Equiv.Perm.viaEmbeddingHom e).comp (automizerWeightPerm ρ Q),
    (Equiv.Perm.viaEmbeddingHom_injective e).comp
      (automizerWeightPerm_injective_of_restriction ρ Q hf ho)⟩

end Representation

namespace Representation
open Subgroup Theory.GroupTheory
variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- In degree at most eight, odd automizer ranks other than the three-rank are at most one. -/
theorem automizer_odd_rank_le_one_of_degree_eight
    (ρ : Representation F G V) (Q : Subgroup G) [IsMulCommutative Q] [Finite Q]
    (hf : Function.Injective (ρ.comp Q.subtype))
    (ho : (Nat.card Q : F) ≠ 0) (hd : Module.finrank F V ≤ 8)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (h3 : p ≠ 3) :
    primeRank p Q.normalizerMonoidHom.range ≤ 1 := by
  let E := AlgebraicClosure F
  let σ := ρ.extendScalars E
  have hf' : Function.Injective (σ.comp Q.subtype) :=
    (extendScalars_faithful_iff E (ρ.comp Q.subtype)).mp hf
  have ho' : (Nat.card Q : E) ≠ 0 := by
    intro h
    apply ho
    apply (algebraMap F E).injective
    simpa using h
  obtain ⟨j,hj⟩ := automizer_embeds_perm_of_faithful_restriction σ Q hf' ho' 8
    (by simpa only [Module.finrank_baseChange] using hd)
  apply (_root_.primeRank_le_of_injective p j hj).trans
  apply primeRank_le_one_of_card_dvd_two_prime_squarefree
    (Equiv.Perm (Fin 8)) (q := 3) (a := 7) (b := 2) (c := 35)
    Nat.prime_three hp h3
  · exact (Nat.squarefree_mul (show Nat.Coprime 5 7 by decide)).mpr
      ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
        (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩
  · norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

end Representation
