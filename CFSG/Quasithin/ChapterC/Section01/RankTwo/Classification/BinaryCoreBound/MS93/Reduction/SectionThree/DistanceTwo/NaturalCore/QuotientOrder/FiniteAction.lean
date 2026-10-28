module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.Representation.SL2SevenCentralProductOffenders.GroupBounds
public import Theory.GroupAction.CyclicCommutatorTransport
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# An order-eight bound from one small involution displacement

For a finite elementary abelian two-group with a faithful, fully moving
SL3(2)-action, an involution displacement of order at most two forces
order eight. Three conjugates of any nonidentity involution generate
SL3(2), so their three displacement subgroups generate the module and
bound its order by 2³. Faithfulness excludes orders one, two and four
by the faithful permutation action. No irreducible-module catalogue or
semisimplicity assertion is needed.

The three-conjugate generation theorem is transported through the proved
matrix isomorphism PSL2(7) ≃ SL3(2); its SL2(7) source uses explicit checked
matrix words. Thus no group-family identification is assumed.

This is the binary finite-action calculation for |V| = q⁶ in
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), natural branch of (3.6), printed p.870. The source geometry that
produces the small displacement is proved separately in Action.lean.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.QuotientOrder
private abbrev S := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private theorem three_conjugates (t : S) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    ∃ g h : S, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔
      zpowers (h * t * h⁻¹) = ⊤ := by
  let : IsSimpleGroup S := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hp : pCore 2 S = ⊥ := by
    rcases (pCore_normal (p := 2) (G := S)).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := S)).exists_card_eq
      rw [h, Nat.card_congr (topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv,
        Atlas.Comparisons.Exceptional.sl3Two_card] at hn
      have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 168)
      have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hd
      norm_num at this
  let e := Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two
  let f : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) →* S :=
    e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfr : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hz : (pCore 2 S).comap f =
      center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
    rw [hp]
    change f.ker = _
    exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  obtain ⟨g, h, hgen⟩ :=
    Representation.BinaryOffender.SL2SevenCentralProduct.three_conjugates_range_le
      f (by rw [hp, commutator_bot_left]) (by rw [hfr, sup_top_eq]) hz t ht
      (by simpa only [hp, mem_bot] using hne)
  exact ⟨g, h, top_unique (hfr ▸ hgen)⟩

private def displacementFixer {E : Type*} [Group E] (H : Subgroup E) :
    Subgroup (MulAut E) where
  carrier := {a | ∀ x, x⁻¹ * a x ∈ H}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    have hh := H.mul_mem (hb x) (ha (b x))
    simpa only [mul_assoc, mul_inv_cancel_left, MulAut.mul_apply] using hh
  inv_mem' := by
    intro a ha x
    have hh := H.inv_mem (ha (a⁻¹ x))
    simpa only [MulAut.apply_inv_self, mul_inv_rev, inv_inv] using hh

private theorem commutator_le_iff {E : Type*} [Group E]
    (A : Subgroup (MulAut E)) (H : Subgroup E) :
    commutatorAction A E ≤ H ↔ A ≤ displacementFixer H := by
  rw [commutatorAction_eq_closure, closure_le]
  constructor
  · intro h a ha x
    exact h ⟨⟨a, ha⟩, x, rfl⟩
  · rintro h _ ⟨a, x, rfl⟩
    exact h a.property x

private theorem conjugate_displacement_card {E : Type*} [Group E]
    (a g : MulAut E) :
    Nat.card (commutatorAction (zpowers (g * a * g⁻¹)) E) =
      Nat.card (commutatorAction (zpowers a) E) := by
  have hh := Nat.card_congr
    (Theory.GroupAction.OddCommutatorImage.cyclicCommutatorEquiv g a ⊤).toEquiv
  have he : MulAut.congr g a = g * a * g⁻¹ := by ext x; rfl
  have hmap : (⊤ : Subgroup E).map g.toMonoidHom = ⊤ :=
    (MonoidHom.range_eq_map _).symm.trans (MonoidHom.range_eq_top.mpr g.surjective)
  rw [he, hmap] at hh
  exact hh.symm

private theorem card_sup_le {E : Type*} [Group E] [Finite E] [IsMulCommutative E]
    (A B : Subgroup E) : Nat.card (A ⊔ B : Subgroup E) ≤ Nat.card A * Nat.card B := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B le_normalizer_of_normal
  have hp : 0 < Nat.card (A ⊓ B : Subgroup E) := Nat.card_pos
  nlinarith

/-- A faithful, fully moving binary SL3(2)-action with an involution moving
at most one binary dimension acts on exactly eight elements. -/
theorem card_eq_eight_of_small_displacement {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E]
    (a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* MulAut E)
    (hinj : Function.Injective a) (hfull : commutatorAction a.range E = ⊤)
    (t : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (ht : t ^ 2 = 1) (htne : t ≠ 1)
    (hsmall : Nat.card (commutatorAction (zpowers (a t)) E) ≤ 2) :
    Nat.card E = 8 := by
  obtain ⟨g, h, hgen⟩ := three_conjugates t ht htne
  let A := commutatorAction (zpowers (a t)) E
  let B := commutatorAction (zpowers (a (g * t * g⁻¹))) E
  let C := commutatorAction (zpowers (a (h * t * h⁻¹))) E
  have hB : Nat.card B ≤ 2 := by
    dsimp only [B]
    rw [map_mul, map_mul, map_inv, conjugate_displacement_card]
    exact hsmall
  have hC : Nat.card C ≤ 2 := by
    dsimp only [C]
    rw [map_mul, map_mul, map_inv, conjugate_displacement_card]
    exact hsmall
  have hcover : A ⊔ B ⊔ C = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply (commutator_le_iff _ _).mpr
    have hg : (⊤ : Subgroup S) ≤ (displacementFixer (A ⊔ B ⊔ C)).comap a := by
      rw [← hgen]
      apply sup_le (sup_le ?_ ?_) ?_
      · apply zpowers_le.mpr
        exact (commutator_le_iff (zpowers (a t)) _).mp
          (le_sup_left.trans le_sup_left) (mem_zpowers _)
      · apply zpowers_le.mpr
        exact (commutator_le_iff (zpowers (a (g * t * g⁻¹))) _).mp
          (le_sup_right.trans le_sup_left) (mem_zpowers _)
      · apply zpowers_le.mpr
        exact (commutator_le_iff (zpowers (a (h * t * h⁻¹))) _).mp
          le_sup_right (mem_zpowers _)
    rintro _ ⟨s, rfl⟩
    exact hg (mem_top s)
  have hle : Nat.card E ≤ 8 := by
    have hAB := card_sup_le A B
    have hABC := card_sup_le (A ⊔ B) C
    have htop : Nat.card (A ⊔ B ⊔ C : Subgroup E) = Nat.card E := by
      rw [hcover]
      exact Nat.card_congr topEquiv.toEquiv
    rw [htop] at hABC
    change Nat.card A ≤ 2 at hsmall
    nlinarith
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [← hn] using hle)
  have hperm : Function.Injective (fun s : S => (a s).toEquiv) := by
    intro s t he
    apply hinj
    exact MulEquiv.toEquiv_injective he
  have hsize := Nat.card_le_card_of_injective _ hperm
  rw [Atlas.Comparisons.Exceptional.sl3Two_card, Nat.card_perm, hn] at hsize
  interval_cases n <;> norm_num at hsize
  simpa only [Nat.reducePow] using hn

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.QuotientOrder
