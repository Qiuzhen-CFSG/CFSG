module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import GorensteinWalter.PGL2InnerAction
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Projective action and generation transport for the PGL₂ shadow

The outer-action predicate equates conjugation by the actual element of R,
transported through an isomorphism L ≃ PSL₂(F), with conjugation by a
projective matrix outside the canonical PSL₂ image. The faithful PGL₂ action
identifies this with an outer automorphism of order two.

Mapping fixed subgroups back into G turns intrinsic generation calculations
into C_L(r), C_L(i) generation. Tight embedding then proves R₀ = 1 whenever
those calculations hold for the involutions of the genuine subgroup R₀.
The model generation identities and R = R₀⟨r⟩ remain explicit premises here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.4.6,
printed p.1184. This module does not assert the source exclusion theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow
open Subgroup GorensteinWalter

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The actual conjugation action is induced by a projective matrix outside PSL₂. -/
def InducesOuterPGL (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (e : L ≃* PSL2 F) : Prop :=
  ∃ A : PGL2 F,
    A ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
    ∀ x : L, Matrix.ProjectiveSpecialLinearGroup.toPGL (e (involutionAction h hr x)) =
      A * Matrix.ProjectiveSpecialLinearGroup.toPGL (e x) * A⁻¹

/-- Equivalent formulation through the faithful matrix conjugation homomorphism. -/
theorem inducesOuterPGL_iff (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (e : L ≃* PSL2 F) (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) :
    InducesOuterPGL h hr e ↔ ∃ A : PGL2 F,
      A ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
      MulAut.congr e (involutionAction h hr) = pgl2InnerAutPSL2 F hF hcard A := by
  constructor
  · rintro ⟨A, hA, ha⟩
    refine ⟨A, hA, ?_⟩
    ext x
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (e (involutionAction h hr (e.symm x))) = _
    rw [ha, e.apply_symm_apply, toPGL_pgl2InnerAutPSL2_apply]
  · rintro ⟨A, hA, ha⟩
    refine ⟨A, hA, fun x => ?_⟩
    have he : e (involutionAction h hr x) = pgl2InnerAutPSL2 F hF hcard A (e x) := by
      have hh := DFunLike.congr_fun ha (e x)
      change e (involutionAction h hr (e.symm (e x))) = _ at hh
      simpa only [e.symm_apply_apply] using hh
    rw [he, toPGL_pgl2InnerAutPSL2_apply]

/-- Faithfulness of R on L preserves the involution order in the projective model. -/
theorem projective_witness_order (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hfaith : R ⊓ centralizer (L : Set G) = ⊥)
    (e : L ≃* PSL2 F) (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (A : PGL2 F)
    (ha : MulAut.congr e (involutionAction h hr) = pgl2InnerAutPSL2 F hF hcard A) :
    orderOf A = 2 := by
  calc
    orderOf A = orderOf (pgl2InnerAutPSL2 F hF hcard A) :=
      (orderOf_injective _ (pgl2InnerAutPSL2_injective F hF hcard) A).symm
    _ = orderOf (MulAut.congr e (involutionAction h hr)) := by rw [ha]
    _ = orderOf (involutionAction h hr) := (MulAut.congr e).orderOf_eq _
    _ = 2 := involutionAction_order h hfaith hr hr2

/-- A matrix outside the PSL₂ image cannot induce an inner automorphism. -/
theorem not_inner_of_inducesOuterPGL (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h hr e) :
    ¬ ∃ x : L, involutionAction h hr = MulAut.conj x := by
  obtain ⟨A, hA, ha⟩ := (inducesOuterPGL_iff h hr e hF hcard).mp hout
  rintro ⟨x, hx⟩
  rw [hx, MulAut.congr_conj] at ha
  apply hA
  refine ⟨e x, ?_⟩
  apply pgl2InnerAutPSL2_injective F hF hcard
  rw [pgl2InnerAutPSL2_toPGL]
  exact ha

omit [Finite F] in
/-- Fixed points map onto the actual embedded centralizer C_L(r). -/
theorem model_fixed_map (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (e : L ≃* PSL2 F) :
    (MulAut.congr e (involutionAction h hr)).fixedSubgroup.map
      (L.subtype.comp e.symm.toMonoidHom) = L ⊓ involutionCentralizer r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(e.symm x).property, ?_⟩
    apply (ComponentTransfer.Intrinsic.mem_fixed_action
      (h.sylow_normalizes (h.le_sylow hr)) (e.symm x)).mp
    rw [MulAut.mem_fixedSubgroup]
    apply e.injective
    have hh := (MulAut.mem_fixedSubgroup _ _).mp hx
    change e (involutionAction h hr (e.symm x)) = x at hh
    simpa only [e.apply_symm_apply] using hh
  · intro hy
    change y ∈ L ∧ y ∈ involutionCentralizer r at hy
    refine ⟨e ⟨y, hy.1⟩, ?_, ?_⟩
    · apply (MulAut.mem_fixedSubgroup _ _).mpr
      change e (involutionAction h hr (e.symm (e ⟨y, hy.1⟩))) = e ⟨y, hy.1⟩
      rw [e.symm_apply_apply]
      congr 1
      exact (MulAut.mem_fixedSubgroup _ _).mp
        ((ComponentTransfer.Intrinsic.mem_fixed_action
          (h.sylow_normalizes (h.le_sylow hr)) ⟨y, hy.1⟩).mpr hy.2)
    · change (e.symm (e ⟨y, hy.1⟩) : G) = y
      rw [e.symm_apply_apply]

omit [Finite F] in
/-- A pair of model fixed subgroups generating PSL₂ generates L after transport. -/
theorem centralizers_generate_of_model_fixed
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) {i : G} (hi : i ∈ R)
    (e : L ≃* PSL2 F)
    (hgen : (MulAut.congr e (involutionAction h hr)).fixedSubgroup ⊔
      (MulAut.congr e (involutionAction h hi)).fixedSubgroup = ⊤) :
    (L ⊓ involutionCentralizer r) ⊔ (L ⊓ involutionCentralizer i) = L := by
  have hh := congrArg (fun D : Subgroup (PSL2 F) =>
    D.map (L.subtype.comp e.symm.toMonoidHom)) hgen
  rw [Subgroup.map_sup, model_fixed_map, model_fixed_map, ← MonoidHom.range_eq_map] at hh
  have he : (L.subtype.comp e.symm.toMonoidHom).range = L := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.symm a).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, by
        change (e.symm (e ⟨x, hx⟩) : G) = x
        rw [e.symm_apply_apply]⟩
  exact hh.trans he

omit [Finite F] in
/-- The opening R₀ = 1 deduction, conditional on the intrinsic pair calculations
and the genuine complement identity for R₀. -/
theorem eq_zpowers_of_model_pair_generation
    (h : IntersectionSetup T z L g R)
    (hnot : ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hr : r ∈ R) (hr2 : orderOf r = 2) (e : L ≃* PSL2 F)
    (R₀ : Subgroup G) (hR₀ : R₀ ≤ R) (hR : R = R₀ ⊔ zpowers r)
    (hgen : ∀ i : G, (hi : i ∈ R₀) → orderOf i = 2 →
      (MulAut.congr e (involutionAction h hr)).fixedSubgroup ⊔
      (MulAut.congr e (involutionAction h (hR₀ hi))).fixedSubgroup = ⊤) :
    R = zpowers r ∧ Nat.card R = 2 := by
  have hbot : R₀ = ⊥ := two_subgroup_eq_bot_of_pair_generation h hnot hr hr2 hR₀
    (fun i hi hi2 => centralizers_generate_of_model_fixed h hr (hR₀ hi) e (hgen i hi hi2))
  have he : R = zpowers r := by simpa only [hbot, bot_sup_eq] using hR
  exact ⟨he, by rw [he, Nat.card_zpowers, hr2]⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow
