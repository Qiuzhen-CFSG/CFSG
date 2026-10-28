module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Kernel
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The faithful quotient retained in the exceptional MS preparation

Put M = LR, K = L inside M, Q = O₂(M), and let E be the original
central extension kernel. The component C in M/Q is the full generalized
Fitting subgroup, so E/Q is exactly its centralizer. Perfectness lifts
centralizers through E/Q and proves that the component in M/E has trivial
centralizer. Component dichotomy then removes O₂(M/E).

The actual quotient acts faithfully on the marked A₆, with component
elements acting by the corresponding inner automorphisms. These are the
faithfulness and core-free facts needed for weak-BN preparation. Preservation
of the parabolic types and construction of the parabolics remain separate
proof obligations; no core-exhaustion premise is used here.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136;
Meierfrankenfeld--Stellmacher (1993), Hypothesis (A), printed pp.828--829.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "C" => componentImage L R

/-- The actual component modulo Q is the full generalized Fitting subgroup. -/
theorem coreQuotient_generalizedFitting (h : SmallMSPair κ L R) (e : CentralMarking L) :
    generalizedFitting (M ⧸ Q) = C := by
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  let q := QuotientGroup.mk' Q
  let : (C).Normal := (inferInstance : (K).Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component)
  have hsup : C ⊔ (R.subgroupOf (L ⊔ R)).map q = ⊤ := by
    rw [← Subgroup.map_sup, (codisjoint_subgroupOf_sup L R).eq_top]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  exact generalizedFitting_eq_of_quasisimple_two_quotient C
    (isPGroup_quotient_of_sup_eq_top C ((R.subgroupOf (L ⊔ R)).map q)
      (h.relative_radical.isPGroup.map q) hsup) (pCore_quotient_pCore_eq_bot 2)

/-- E/Q is exactly the full centralizer of the component in M/Q. -/
theorem extensionKernel_image_eq_centralizer
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    (extensionKernel h).map (QuotientGroup.mk' Q) = centralizer (C : Set (M ⧸ Q)) := by
  rw [extensionKernel_image h]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
  · have hc : centralizer (C : Set (M ⧸ Q)) ≤ C := by
      rw [← coreQuotient_generalizedFitting h e]
      exact centralizer_generalizedFitting_le _
    intro x hx
    refine ⟨⟨x, hc hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hx y y.property)

/-- The same identity pulled back through the literal core quotient. -/
theorem extensionKernel_eq_comap_centralizer
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    extensionKernel h = (centralizer (C : Set (M ⧸ Q))).comap (QuotientGroup.mk' Q) := by
  rw [← extensionKernel_image_eq_centralizer h e, comap_map_eq, QuotientGroup.ker_mk',
    sup_of_le_left (show Q ≤ extensionKernel h from le_sup_right)]

/-- The component of the actual source quotient M/E has trivial centralizer.
Perfectness is essential when lifting centralizers through E/Q. -/
theorem extensionQuotient_component_centralizer
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    centralizer ((K).map (QuotientGroup.mk' (extensionKernel h)) :
      Set (M ⧸ extensionKernel h)) = ⊥ := by
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component)
  let q := QuotientGroup.mk' Q
  let π := QuotientGroup.mk' (extensionKernel h)
  let f := QuotientGroup.lift Q π (by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mpr (show x ∈ extensionKernel h from mem_sup_right hx))
  have hf : f.comp q = π := rfl
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (extensionKernel h) x
    exact ⟨q m, rfl⟩
  have hk : f.ker = centralizer (C : Set (M ⧸ Q)) := by
    apply comap_injective (QuotientGroup.mk'_surjective Q)
    rw [MonoidHom.comap_ker, hf, QuotientGroup.ker_mk']
    exact extensionKernel_eq_comap_centralizer h e
  have him : (C).map f = (K).map π := by
    change ((K).map q).map f = _
    rw [map_map, hf]
  apply comap_injective hsurj
  rw [← him, comap_centralizer_map_eq_of_perfect f C hk.le]
  exact hk.symm

/-- The actual source quotient has no residual normal two-group. This is the
core-free premise needed in the weak-BN preparation. -/
theorem extensionQuotient_twoCore (h : SmallMSPair κ L R) (e : CentralMarking L) :
    pCore 2 (M ⧸ extensionKernel h) = ⊥ := by
  let := h.relative_normal
  let π := QuotientGroup.mk' (extensionKernel h)
  let D := (K).map π
  let : D.Normal := (inferInstance : (K).Normal).map π (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (alternatingGroup (Fin 6)) :=
    GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 1
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv (extensionKernel_component_equiv h e).symm
  have hD : IsComponent (M ⧸ extensionKernel h) D :=
    ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  rcases hD.normal_dichotomy (pCore 2 (M ⧸ extensionKernel h)) with hle | hcomm
  · let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    let : Group.IsNilpotent D := (pCore_isPGroup.to_le hle).isNilpotent
    exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
  · apply bot_unique
    rw [commutator_comm] at hcomm
    exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (extensionQuotient_component_centralizer h e).le

/-- The original quotient acts on the actual marked A₆ by conjugation. -/
@[expose] def extensionQuotientAction (h : SmallMSPair κ L R) (e : CentralMarking L) :
    (M ⧸ extensionKernel h) →* MulAut (alternatingGroup (Fin 6)) := by
  let := h.relative_normal
  let : ((K).map (QuotientGroup.mk' (extensionKernel h))).Normal :=
    (inferInstance : (K).Normal).map _ (QuotientGroup.mk'_surjective _)
  exact (MulAut.congr (extensionKernel_component_equiv h e)).toMonoidHom.comp MulAut.conjNormal

/-- Triviality of the centralizer makes that specific action faithful. -/
theorem extensionQuotientAction_injective
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    Function.Injective (extensionQuotientAction h e) := by
  let := h.relative_normal
  let : ((K).map (QuotientGroup.mk' (extensionKernel h))).Normal :=
    (inferInstance : (K).Normal).map _ (QuotientGroup.mk'_surjective _)
  exact (MulAut.congr (extensionKernel_component_equiv h e)).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _
      (extensionQuotient_component_centralizer h e))

/-- Component elements act by the inner automorphism with the same marking. -/
theorem extensionQuotientAction_component
    (h : SmallMSPair κ L R) (e : CentralMarking L) (k : K) :
    extensionQuotientAction h e (QuotientGroup.mk' (extensionKernel h) k) =
      MulAut.conj (extensionKernel_component_equiv h e
        ((QuotientGroup.mk' (extensionKernel h)).subgroupMap K k)) := by
  let := h.relative_normal
  let : ((K).map (QuotientGroup.mk' (extensionKernel h))).Normal :=
    (inferInstance : (K).Normal).map _ (QuotientGroup.mk'_surjective _)
  change MulAut.congr (extensionKernel_component_equiv h e)
    (MulAut.conjNormal
      (((QuotientGroup.mk' (extensionKernel h)).subgroupMap K k).val)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
