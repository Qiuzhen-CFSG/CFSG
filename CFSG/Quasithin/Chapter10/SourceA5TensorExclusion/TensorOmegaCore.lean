module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Cohomology
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.Representation.FirstCohomologyAutomorphism.FixedSupplement

/-!
# The Omega-center and cohomology steps of source 9.2.2

Put Q = O₂(L₀T). The original tensor module V is contained in Ω₁Z(Q).
If [Ω₁Z(Q),L₀] ≤ V, vanishing first cohomology for the actual quotient
L₀/O₂(L₀) splits Ω₁Z(Q) as V times its L₀-fixed subgroup. The center-free
conclusion of source 3.1.8(3) makes that fixed subgroup trivial.
Characteristic two then gives Ω₁Z(S) = C_V(S) for every Q ≤ S ≤ T.

The numerical assertion excluding commutator movement beyond V, and the
center-free source conclusion, remain explicit inputs. A bound only on V
is not a bound on the larger Omega module. The proofs below do not assume
that the action kernel O₂(L₀) equals V.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
9.2.2, printed p.730; 3.1.8(3) and 3.2.10(9), printed pp.576 and 583.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original tensor module lies in the actual central omega of O₂(L₀T). -/
theorem fullModule_le_omegaCenter_core :
    D.fullModule ≤ omegaCenterIn ((localJoin T L).pCoreIn 2) := by
  let := m.fullModule_elementary
  have hVQ : D.fullModule ≤ (localJoin T L).pCoreIn 2 := by
    rw [← m.module_eq]
    exact D.module_le_core
  have hQC : (localJoin T L).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
    rw [← m.module_eq]
    exact D.core_centralizes_module
  intro v hv
  apply (mem_omegaCenterIn_iff _ _).mpr
  exact ⟨hVQ hv, fun q hq => (hQC hq v hv).symm,
    elemPow_eq_one_of_isElementaryAbelian v hv⟩

omit m in
/-- The join has characteristic two, using its actual nontrivial core. -/
theorem localJoin_mem_He (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    localJoin T L ∈ Chapter1.He G := by
  apply Chapter1.lemma_1_1_4_6 T (D.simpleQTKE.evenCharacteristic T)
  refine ⟨?_,fun _ hx => (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) hx⟩
  intro he
  exact D.module_ne_bot (bot_unique (D.module_le_core.trans_eq he))

omit m in
/-- The second assertion of 9.2.2 follows from its first assertion and He. -/
theorem omegaCenter_eq_fullModule_inf_of_core_eq
    (hV : D.fullModule = omegaCenterIn ((localJoin T L).pCoreIn 2))
    (S : Subgroup G) (hQS : (localJoin T L).pCoreIn 2 ≤ S)
    (hST : S ≤ (T : Subgroup G)) :
    omegaCenterIn S = D.fullModule ⊓ centralizer (S : Set G) := by
  rw [hV]
  apply omegaCenterIn_eq_inf_of_center_le _ S hQS
  intro s hs
  exact localJoin_mem_He D ⟨(show (T : Subgroup G) ≤ localJoin T L from le_sup_right)
    (hST hs.1),centralizer_le hQS hs.2⟩

/-- The H¹ step of 9.2.2 uses the literal quotient L₀/O₂(L₀), whose kernel
centralizes Ω₁Z(Q), even when that kernel is larger than V. -/
theorem omegaCenter_core_eq_sup_fixed_of_commutator_le
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤
      D.fullModule) :
    omegaCenterIn ((localJoin T L).pCoreIn 2) = D.fullModule ⊔
      (omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓ centralizer (localOrbit T L : Set G)) := by
  classical
  let := m.coreQuotient_subsingleton_H1
  let c : D.fullModule ≃* Multiplicative Binary.V :=
    MulEquiv.ofBijective m.sectionData.coordinates
      ⟨m.coordinates_injective, m.sectionData.onto⟩
  apply OneCohomology.eq_sup_inf_centralizer_of_H1_zero (localOrbit T L)
    D.fullModule (omegaCenterIn ((localJoin T L).pCoreIn 2))
    D.fullModule_le_orbit m.fullModule_le_omegaCenter_core
    (QuotientGroup.mk' (pCore 2 (localOrbit T L))) (QuotientGroup.mk'_surjective _)
    c m.coreQuotientAction ?_ ?_ hcomm
  · intro g w
    let v := c.symm (Multiplicative.ofAdd w)
    let v' : D.fullModule := ⟨g * v * (g : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized g.property) v).mp v.property⟩
    change (c.symm _ : G) = (v' : G)
    apply congrArg Subtype.val
    apply c.injective
    rw [c.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    have ha := m.coreQuotientAction_coordinates g v
    have hv : m.sectionData.coordinates v = Multiplicative.ofAdd w := c.apply_symm_apply _
    rw [hv] at ha
    exact ha.symm
  · have hcore : (localOrbit T L).pCoreIn 2 ≤ (localJoin T L).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
    intro x hx
    have hxcore : x ∈ (localOrbit T L).pCoreIn 2 := by
      simpa only [QuotientGroup.ker_mk', pCoreIn] using hx
    intro u hu
    exact ((mem_omegaCenterIn_iff _ _).mp hu |>.2.1 x (hcore hxcore)).symm

omit m in
/-- The center-free conclusion of source 3.1.8(3) kills the fixed subgroup
in Ω₁Z(Q), using the actual normal Sylow supplement L₀. -/
theorem omegaCenter_core_fixed_eq_bot_of_center_eq_bot
    (hcenter : center (localJoin T L) = ⊥) :
    omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓
      centralizer (localOrbit T L : Set G) = ⊥ := by
  let J := localJoin T L
  let X := (localOrbit T L).subgroupOf J
  let S : Sylow 2 J := T.subtype le_sup_right
  have hnX : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let := hnX
  have hcover : X ⊔ (S : Subgroup J) = ⊤ := by
    change (localOrbit T L).subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hc : pCore 2 J ⊓ centralizer (X : Set J) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S X (pCore 2 J)
      hcover pCore_isPGroup hcenter
  apply le_bot_iff.mp
  rintro x ⟨hx,hxc⟩
  have hxQ := ((mem_omegaCenterIn_iff _ _).mp hx).1
  change x ∈ (pCore 2 J).map J.subtype at hxQ
  obtain ⟨xJ,hxJ,rfl⟩ := hxQ
  have hxC : xJ ∈ pCore 2 J ⊓ centralizer (X : Set J) := by
    refine ⟨hxJ,?_⟩
    intro y hy
    exact Subtype.ext (hxc y hy)
  exact congrArg J.subtype (mem_bot.mp (hc ▸ hxC))

/-- The cohomology and center-free parts of 9.2.2 identify V with Ω₁Z(Q)
once the numerical argument excludes extra commutator movement. -/
theorem fullModule_eq_omegaCenter_core_of_commutator_le
    (hcenter : center (localJoin T L) = ⊥)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤
      D.fullModule) :
    D.fullModule = omegaCenterIn ((localJoin T L).pCoreIn 2) := by
  simpa only [omegaCenter_core_fixed_eq_bot_of_center_eq_bot hcenter, sup_bot_eq]
    using (m.omegaCenter_core_eq_sup_fixed_of_commutator_le hcomm).symm

/-- Actual interval consumer: the same source inputs give 9.2.2(2) for
all original ambient subgroups Q ≤ S ≤ T. -/
theorem omegaCenter_eq_fullModule_inf_of_commutator_le
    (hcenter : center (localJoin T L) = ⊥)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤
      D.fullModule)
    (S : Subgroup G) (hQS : (localJoin T L).pCoreIn 2 ≤ S)
    (hST : S ≤ (T : Subgroup G)) :
    omegaCenterIn S = D.fullModule ⊓ centralizer (S : Set G) :=
  omegaCenter_eq_fullModule_inf_of_core_eq
    (m.fullModule_eq_omegaCenter_core_of_commutator_le hcenter hcomm) S hQS hST

/-- With the source fixed-center vanishing, a larger omega module must have
commutator movement beyond V. This is the input to the section-ratio argument. -/
theorem omegaCenter_core_not_commutator_le_of_ne
    (hfixed : omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓
      centralizer (localOrbit T L : Set G) = ⊥)
    (hne : D.fullModule ≠ omegaCenterIn ((localJoin T L).pCoreIn 2)) :
    ¬ ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule := by
  intro hc
  apply hne
  simpa only [hfixed,sup_bot_eq] using
    (m.omegaCenter_core_eq_sup_fixed_of_commutator_le hc).symm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
