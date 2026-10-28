module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RootSpan

/-!
# Constructing the literal radical action on the swapped module

Conjugation on U kills O₂(IT). Whole-module coordinates therefore extend
across I O₂(IT), and faithfulness of the symplectic matrix action proves the
homomorphism laws. Geometric representatives in the original plane radical
then give the range bound. The paired-flag construction must still supply
those representatives; no action or homomorphism is part of that input.

Source: Aschbacher--Smith 11.4.1(2), p.776, using the shared plane in the
proof of 11.1.2(3), pp.762--764.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) {F : BinaryField}

/-- Extend the actual symplectic action across O₂(IT), which centralizes U.
No action map on R is assumed: it is constructed from the literal inclusion
R ≤ I O₂(IT) and the original quotient marking. -/
theorem exists_symplectic_action (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (R : Subgroup G)
    (hR : R ≤ I ⊔ (I ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ (hRU : R ≤ normalizer (U : Set G)) (α : R →* Sp F.Carrier),
      ∀ (a : R) (u : U),
        (symplecticEquiv D hfix m
          ⟨a.val * u.val * a.val⁻¹,
            (mem_normalizer_iff.mp (hRU a.property) u.val).mp u.property⟩).toAdd =
          α a • (symplecticEquiv D hfix m u).toAdd := by
  classical
  let Q := (I ⊔ (T : Subgroup G)).pCoreIn 2
  let e := symplecticEquiv D hfix m
  have hIQ : I ≤ normalizer (Q : Set G) :=
    (le_sup_left : I ≤ I ⊔ (T : Subgroup G)).trans
      ((I ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hRU : R ≤ normalizer (U : Set G) := hR.trans
    (sup_le D.normalizes (D.core_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
  let β : R →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hRU)
  have hex (a : R) : ∃ b : Sp F.Carrier, ∀ u : U,
      (e (β a u)).toAdd = b • (e u).toAdd := by
    have ha : (a : G) ∈ (I : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right I Q hIQ]
      exact hR a.property
    obtain ⟨i, hi, q, hq, he⟩ := ha
    refine ⟨m.groupEquiv (QuotientGroup.mk' (pCore 2 I) ⟨i, hi⟩), ?_⟩
    intro u
    have hc : β a u =
        ⟨i * u.val * i⁻¹,
          (mem_normalizer_iff.mp (D.normalizes hi) u.val).mp u.property⟩ := by
      apply Subtype.ext
      change a.val * u.val * a.val⁻¹ = _
      rw [← he, mul_inv_rev]
      have hqu : q * u.val = u.val * q :=
        ((mem_centralizer_iff.mp (D.core_centralizes hq)) u.val u.property).symm
      calc
        i * q * u.val * (q⁻¹ * i⁻¹) = i * (q * u.val) * q⁻¹ * i⁻¹ := by group
        _ = i * u.val * i⁻¹ := by rw [hqu]; group
    rw [hc]
    exact symplecticEquiv_conj D hfix m ⟨i, hi⟩ u
  choose a ha using hex
  have hext (x y : Sp F.Carrier)
      (h : ∀ u : U, x • (e u).toAdd = y • (e u).toAdd) : x = y := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Vector F.Carrier)
    intro v
    obtain ⟨u, hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have hh := h u
    rw [hu] at hh
    exact hh
  let α : R →* Sp F.Carrier := {
    toFun := a
    map_one' := by
      apply hext
      intro u
      rw [← ha, map_one, MulAut.one_apply, one_smul]
    map_mul' := by
      intro r s
      apply hext
      intro u
      calc
        a (r * s) • (e u).toAdd = (e (β (r * s) u)).toAdd := (ha _ _).symm
        _ = (e (β r (β s u))).toAdd := by rw [map_mul]; rfl
        _ = a r • (e (β s u)).toAdd := ha _ _
        _ = (a r * a s) • (e u).toAdd := by rw [ha, mul_smul] }
  exact ⟨hRU, α, ha⟩

/-- The geometric placement still required from the paired source flags.
Every original radical element has a representative in the same component
whose matrix lies in the plane radical; the error lies in the actual O₂(IT).
This is a subgroup-placement specification, not an assumed action map. -/
@[expose] def HasPlaneRadicalLifts
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (R : Subgroup G) : Prop :=
  ∀ a : R, ∃ (i : I) (q : (I ⊔ (T : Subgroup G)).pCoreIn 2),
    a.val = i.val * q.val ∧
      m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i) ∈ Plane.radical.map planeLocal.subtype

/-- Geometric radical representatives construct the action and prove its
range bound. In particular no representation of the original radical is
assumed in this implication. -/
theorem exists_plane_radical_action
    (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (R : Subgroup G) (hlift : HasPlaneRadicalLifts D m R) :
    ∃ (hRU : R ≤ normalizer (U : Set G)) (α : R →* Sp F.Carrier),
      (∀ (a : R) (u : U),
        (symplecticEquiv D hfix m
          ⟨a.val * u.val * a.val⁻¹,
            (mem_normalizer_iff.mp (hRU a.property) u.val).mp u.property⟩).toAdd =
          α a • (symplecticEquiv D hfix m u).toAdd) ∧
      α.range ≤ Plane.radical.map planeLocal.subtype := by
  have hR : R ≤ I ⊔ (I ⊔ (T : Subgroup G)).pCoreIn 2 := by
    intro a ha
    obtain ⟨i, q, he, _⟩ := hlift ⟨a, ha⟩
    change a = i.val * q.val at he
    rw [he]
    exact mul_mem (mem_sup_left i.property) (mem_sup_right q.property)
  obtain ⟨hRU, α, hα⟩ := exists_symplectic_action D hfix m R hR
  refine ⟨hRU, α, hα, ?_⟩
  rintro _ ⟨a, rfl⟩
  obtain ⟨i, q, he, hm⟩ := hlift a
  have heq : α a = m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i) := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Vector F.Carrier)
    intro v
    obtain ⟨u, hu⟩ := (symplecticEquiv D hfix m).surjective (Multiplicative.ofAdd v)
    have hc :
        (⟨a.val * u.val * a.val⁻¹,
          (mem_normalizer_iff.mp (hRU a.property) u.val).mp u.property⟩ : U) =
        ⟨i.val * u.val * i.val⁻¹,
          (mem_normalizer_iff.mp (D.normalizes i.property) u.val).mp u.property⟩ := by
      apply Subtype.ext
      change a.val * u.val * a.val⁻¹ = i.val * u.val * i.val⁻¹
      rw [he, mul_inv_rev]
      have hqu : q.val * u.val = u.val * q.val :=
        ((mem_centralizer_iff.mp (D.core_centralizes q.property)) u.val u.property).symm
      calc
        i.val * q.val * u.val * (q.val⁻¹ * i.val⁻¹) =
            i.val * (q.val * u.val) * q.val⁻¹ * i.val⁻¹ := by group
        _ = i.val * u.val * i.val⁻¹ := by rw [hqu]; group
    have hh := (hα a u).symm.trans
      ((congrArg (fun w => (symplecticEquiv D hfix m w).toAdd) hc).trans
        (symplecticEquiv_conj D hfix m i u))
    rw [hu] at hh
    exact hh
  exact heq ▸ hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
