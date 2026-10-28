module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CPU
public import CFSG.Quasithin.ChapterC.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Intrinsic hypotheses and action quotient for C.2.7

The input records contain exactly C.2.3 and the additional hypotheses of
C.2.7. The conjugate-generated Sylow clause is identified with the normal
closure inside M_H. The source group KR, intersection M_K, omega-center
module and centralizer quotient are defined intrinsically, with their
actual subgroup images retained.

A C-component stays one in KR. Its established R-invariance gives normality,
and F*(K)=O₂(K) passes to KR because KR/K is a two-group. These deductions
prepare the component calculation without asserting any of the block or
FF-module alternatives of C.2.7.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Hypothesis C.2.3 and Lemma C.2.7, printed pp.144–147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.ComponentInputs
universe u
variable {H : Type u} [Group H]

/-- Source Hypothesis C.2.3, with all subgroups intrinsic to H.
The Sylow clause is equivalent to the canonical normal-closure formulation below. -/
structure PushingUpHypotheses (κ : GroupClass.{u}) (R M : Subgroup H) : Prop where
  sqtk : IsSQTK κ H
  nontrivial : R ≠ ⊥
  two_group : IsPGroup 2 R
  radical : (normalizer (R : Set H)).pCoreIn 2 = R
  characteristic_control : characteristicNormalizerClosure R ≤ M
  sylow : ∃ P : Sylow 2 (conjugateModule M R),
    (P : Subgroup (conjugateModule M R)).map (conjugateModule M R).subtype = R

/-- The conjugate-generated subgroup is the image of the intrinsic normal closure. -/
theorem normalClosure_map_eq_conjugateModule (R M : Subgroup H) (hRM : R ≤ M) :
    (normalClosure (R.subgroupOf M : Set M)).map M.subtype = conjugateModule M R := by
  let D := conjugateModule M R
  have hRD : R ≤ D := by
    intro r hr
    exact (le_iSup (fun m : M => R.map (MulAut.conj (m : H)).toMonoidHom) 1)
      ⟨r, hr, by simp⟩
  let _ : (D.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_iSup_conjugates R M)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (normalClosure_le_normal (show (R.subgroupOf M : Set M) ⊆ D.subgroupOf M from
      fun r hr => hRD hr)) hx
  · apply iSup_le
    intro m
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨m * ⟨r, hRM hr⟩ * m⁻¹,
      (normalClosure_normal (s := (R.subgroupOf M : Set M))).conj_mem
        ⟨r, hRM hr⟩ (le_normalClosure hr) m, rfl⟩

/-- The Sylow clause is literally Sylow membership in the normal closure in M. -/
theorem PushingUpHypotheses.sylow_normalClosure {κ : GroupClass.{u}} {R M : Subgroup H}
    (h : PushingUpHypotheses κ R M) : ChapterC.IsSylowInNormalClosure R M := by
  have hRM : R ≤ M := R.le_normalizer.trans
    ((normalizer_le_characteristicNormalizerClosure_self R h.nontrivial).trans
      h.characteristic_control)
  have hs : Chapter1.IsSylowIn 2 ((R.subgroupOf M).map M.subtype)
      ((normalClosure (R.subgroupOf M : Set M)).map M.subtype) := by
    rw [map_subgroupOf_eq_of_le hRM, normalClosure_map_eq_conjugateModule R M hRM]
    exact h.sylow
  obtain ⟨P, hP⟩ := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mp hs
  exact ⟨P, by rw [hP, map_subgroupOf_eq_of_le hRM]⟩

/-- Every hypothesis of C.2.7. The ambient group is H; the product LR and
its action quotient below are the groups defined in the conclusion of C.2.7. -/
structure Hypotheses (κ : GroupClass.{u}) (R M L : Subgroup H) : Prop where
  pushing_up : PushingUpHypotheses κ R M
  component : L.IsCComponent
  quasisimple : IsQuasisimple (L ⧸ pCore 2 L)
  characteristic_two : generalizedFitting L = pCore 2 L
  outside : ¬ L ≤ M
  invariant : R ≤ normalizer (L : Set H)

/-- The source KR, generated inside H. -/
def localProduct (L R : Subgroup H) : Subgroup H := L ⊔ R

/-- The source M_K=M_H∩K, viewed inside KR. -/
def localIntersection (L R M : Subgroup H) : Subgroup (localProduct L R) :=
  (M ⊓ L).subgroupOf (localProduct L R)

/-- The literal V=Ω₁(Z(O₂(KR))) used in C.2.7. -/
noncomputable def omegaModule (L R : Subgroup H) : Subgroup (localProduct L R) :=
  omegaOneCenterAmbient (pCore 2 (localProduct L R))

/-- The intrinsic module is characteristic in KR. -/
instance omegaModule_characteristic (L R : Subgroup H) : (omegaModule L R).Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro e
  change (omegaOneCenterAmbient (pCore 2 (localProduct L R))).map e.toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective, pCore_map_iso]
  rfl

/-- C_KR(V), rather than the two-core or a centralizer in the original G. -/
def actionKernel (L R : Subgroup H) : Subgroup (localProduct L R) :=
  centralizer (omegaModule L R : Set (localProduct L R))

/-- Characteristicness of V makes its centralizer a valid quotient kernel. -/
instance actionKernel_normal (L R : Subgroup H) : (actionKernel L R).Normal := by
  unfold actionKernel
  infer_instance

/-- The source (KR)* with its actual centralizer kernel. -/
abbrev ActionQuotient (L R : Subgroup H) := localProduct L R ⧸ actionKernel L R

/-- K* inside the actual action quotient. -/
def componentImage (L R : Subgroup H) : Subgroup (ActionQuotient L R) :=
  (L.subgroupOf (localProduct L R)).map (QuotientGroup.mk' (actionKernel L R))

/-- R* inside the actual action quotient. -/
def radicalImage (L R : Subgroup H) : Subgroup (ActionQuotient L R) :=
  (R.subgroupOf (localProduct L R)).map (QuotientGroup.mk' (actionKernel L R))

/-- M_K* inside the actual action quotient. -/
def intersectionImage (L R M : Subgroup H) : Subgroup (ActionQuotient L R) :=
  (localIntersection L R M).map (QuotientGroup.mk' (actionKernel L R))

/-- The intrinsic M_K has the claimed image in H. -/
theorem localIntersection_map (L R M : Subgroup H) :
    (localIntersection L R M).map (localProduct L R).subtype = M ⊓ L :=
  map_subgroupOf_eq_of_le (inf_le_right.trans le_sup_left)

/-- The source omega-center is an elementary abelian two-group. -/
theorem omegaModule_elementary (L R : Subgroup H) : IsElementaryAbelian 2 (omegaModule L R) :=
  omegaOneCenterAmbient_elementaryAbelian _

/-- The selected C-component remains a C-component in KR. -/
theorem Hypotheses.local_component {κ : GroupClass.{u}} {R M L : Subgroup H}
    (h : Hypotheses κ R M L) : (L.subgroupOf (localProduct L R)).IsCComponent :=
  h.component.subgroupOf le_sup_left

/-- The proved R-invariance makes the selected component normal in KR. -/
theorem Hypotheses.local_normal {κ : GroupClass.{u}} {R M L : Subgroup H}
    (h : Hypotheses κ R M L) : (L.subgroupOf (localProduct L R)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer h.invariant)

/-- The generated group KR is the literal set product, by the proved
normalization; no replacement of the source product by a larger join occurs. -/
theorem Hypotheses.localProduct_coe {κ : GroupClass.{u}} {R M L : Subgroup H}
    (h : Hypotheses κ R M L) :
    (localProduct L R : Set H) = (L : Set H) * (R : Set H) :=
  coe_mul_of_right_le_normalizer_left L R h.invariant

/-- The intrinsic two-core quotient in KR is quasisimple. -/
theorem Hypotheses.local_quasisimple {κ : GroupClass.{u}} {R M L : Subgroup H}
    (h : Hypotheses κ R M L) :
    IsQuasisimple ((L.subgroupOf (localProduct L R)) ⧸
      pCore 2 (L.subgroupOf (localProduct L R))) := by
  let e := (subgroupOfEquivOfLe (show L ≤ localProduct L R from le_sup_left)).symm
  let _ := h.quasisimple
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

variable [Finite H]

/-- Characteristic two passes to KR through its normal component and
two-group quotient. Neither relative subnormality nor this equality is assumed. -/
theorem Hypotheses.local_characteristic_two {κ : GroupClass.{u}} {R M L : Subgroup H}
    (h : Hypotheses κ R M L) :
    generalizedFitting (localProduct L R) = pCore 2 (localProduct L R) := by
  let D := localProduct L R
  let A := L.subgroupOf D
  let B := R.subgroupOf D
  let _ : A.Normal := h.local_normal
  have hF : generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_twoCore_of_equiv (subgroupOfEquivOfLe le_sup_left) h.characteristic_two
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_le_of_normal_pGroup_quotient A
  · rw [← hF]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  · apply isPGroup_quotient_of_sup_eq_top A B h.pushing_up.two_group.comap_subtype
    change L.subgroupOf (L ⊔ R) ⊔ R.subgroupOf (L ⊔ R) = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.ComponentInputs
