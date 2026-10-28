module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# Sylow index of the symplectic field fixed group

A Sylow two-subgroup of Sp₄(F) has order |F|⁴. Its intersection with the
field fixed group injects into a Sylow two-subgroup of Sp₄(K), of order |K|⁴.
Since |F| = |K|², the intersection has index at least |K|⁴, hence greater
than two. The ambient Sylow subgroup need not be invariant under the field
automorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the field case 16.1.7(3)(a) in the Sylow-index
comparison of Lemma 16.1.8, printed pp.1172–1173.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open Subgroup
variable {F : Type*} [Field F] [Finite F]

private theorem sylow_card {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 (Sp F)) : Nat.card P = (Nat.card F)^4 := by
  exact (Nat.card_congr (P.equiv (unipotentSylow hF hn)).toEquiv).trans card_unipotent

variable [CharP F 2]

/-- The intersection with the fixed group has at most the order of a Sylow
subgroup over the fixed field. No invariance of the ambient Sylow is assumed. -/
theorem card_fixed_intersection_le {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m)) (P : Sylow 2 (Sp F)) :
    Nat.card ((representative (F := F) m).fixedSubgroup.subgroupOf P) ≤ (2 ^ m)^4 := by
  let H := (representative (F := F) m).fixedSubgroup
  let A := H.subgroupOf P
  let e := fixedEquiv ((frobeniusEquiv F 2)^m)
  let f : A →* Sp (halfField (F := F) m) := e.toMonoidHom.comp {
    toFun x := ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    have hv := congrArg (fun z : H => (z : Sp F)) (e.injective h)
    exact Subtype.ext (Subtype.ext hv)
  have hp : IsPGroup 2 f.range :=
    (P.isPGroup'.to_subgroup A).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  let j : A → Q := fun x => ⟨f x, hQ ⟨x, rfl⟩⟩
  have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
  calc
    Nat.card A ≤ Nat.card Q := Nat.card_le_card_of_injective j hj
    _ = (Nat.card (halfField (F := F) m))^4 := sylow_card hm (card_halfField hm hF) Q
    _ = (2 ^ m)^4 := by rw [card_halfField hm hF]

/-- The Sylow index is at least the full two-part over the fixed field. -/
theorem fixed_index_lower_bound {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m)) (P : Sylow 2 (Sp F)) :
    (2 ^ m)^4 ≤ ((representative (F := F) m).fixedSubgroup.subgroupOf P).index := by
  let A := (representative (F := F) m).fixedSubgroup.subgroupOf P
  have hb := card_fixed_intersection_le hm hF P
  change Nat.card A ≤ (2 ^ m)^4 at hb
  have hp := A.card_mul_index
  have hq : Nat.card P = ((2 ^ m)^4)^2 := by
    rw [sylow_card (by omega) hF P, hF]
    simp only [← pow_mul]
    congr 1
    omega
  rw [hq] at hp
  have hmul := Nat.mul_le_mul_right A.index hb
  have hpos : 0 < (2 ^ m)^4 := by positivity
  change (2 ^ m)^4 ≤ A.index
  nlinarith

/-- The strict index comparison used for the field case of source 16.1.8. -/
theorem two_lt_fixed_index {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m)) (P : Sylow 2 (Sp F)) :
    2 < ((representative (F := F) m).fixedSubgroup.subgroupOf P).index := by
  have htwo : 2 ≤ 2 ^ m := by
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm)
  have hfour := Nat.pow_le_pow_left htwo 4
  exact lt_of_lt_of_le (by norm_num at hfour; omega) (fixed_index_lower_bound hm hF P)

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
