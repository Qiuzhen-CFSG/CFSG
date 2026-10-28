module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# A proper cubic fixed-line overgroup

Let X be a nine-group in the normal three-core, and let B and C be cubics,
with B outside X and normalizing C. If a two-group S normalizes both cubics,
then CBS cannot be the whole group. Otherwise CB is normal with two-group
quotient, so it contains the three-core. Its order is at most nine, forcing
X = CB and contradicting B outside X. All normality is in the displayed
ambient group, without replacing the actual three-core by a model.

Source: Aschbacher–Smith, the proper-centralizer step in 14.7.27,
printed pp.1054–1055, refs/quasithin.pdf. ThreeCoreMinimal applies this
calculation through the original quotient by O₂(J).
-/

public section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- Two normalized cubics cannot generate the whole ambient group together
with a two-group when a normal three-core contains a distinct nine-group. -/
theorem cubic_fixed_line_join_ne_top
    (X B C S : Subgroup D)
    (hX : Nat.card X = 9) (hXP : X ≤ pCore 3 D)
    (hB : Nat.card B = 3) (hC : Nat.card C = 3)
    (hBC : B ≤ normalizer (C : Set D)) (hout : ¬ B ≤ X)
    (hS : IsPGroup 2 S)
    (hSB : S ≤ normalizer (B : Set D)) (hSC : S ≤ normalizer (C : Set D)) :
    C ⊔ B ⊔ S ≠ ⊤ := by
  intro he
  let A := C ⊔ B
  have hSA : S ≤ normalizer (A : Set D) :=
    (le_inf hSC hSB).trans (normalizer_inf_normalizer_le_normalizer_sup C B)
  have hAn : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←he]
    exact sup_le A.le_normalizer hSA))
  let := hAn
  have hquot : IsPGroup 2 (D ⧸ A) := isPGroup_quotient_of_sup_eq_top A S hS he
  have hPA : pCore 3 D ≤ A := by
    let q := QuotientGroup.mk' A
    have hz : (pCore 3 D).map q = ⊥ := by
      have hd := ((pCore_isPGroup (p := 3) (G := D)).map q).disjoint_of_coprime
        (hquot.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
      simpa using hd.eq_bot
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hBC
  have hpos := Nat.card_pos (α := (C ⊓ B : Subgroup D))
  have hle : Nat.card A ≤ 9 := by
    change Nat.card (C ⊔ B : Subgroup D) ≤ 9
    rw [hC,hB] at hc
    nlinarith
  have heXA : X = A := eq_of_le_of_card_ge (hXP.trans hPA) (by rwa [hX])
  exact hout (le_sup_right.trans heXA.ge)

end Subgroup
