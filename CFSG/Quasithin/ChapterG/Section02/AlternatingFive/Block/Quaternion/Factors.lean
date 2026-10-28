module
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Quaternion.Core
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Theory.GroupTheory.QuaternionCentralProductQuotient

/-!
# Actual quaternion factors for the closure in G.2.4(8)

An element of Z(U) fixes the seed hyperplane, so its starred image is trivial
and the collapsed kernel puts it in V_L∩U=V. Local irreducibility then gives
C_V(U)=V₁ and hence Z(U)=V₁. The G.2.2 Frattini bound makes the quotient by
this actual center elementary abelian. Together with |U|=32 and the normal
elementary seed of order eight, this supplies every premise of the intrinsic
extraspecial recognition theorem. Its two quaternion subgroups give the
literal diagonal-quotient isomorphism, with no block-recognition premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335, using the central-product convention E.2.16.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Quaternion
open Setup Block
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Local irreducibility makes C_V(U) exactly V₁: otherwise U would fix the
whole orthogonal hyperplane, contradicting its nontrivial starred image. -/
theorem seed_centralizer (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) :
    D.V ⊓ centralizer (D.U : Set G) = D.V₁ := by
  let C := D.V ⊓ centralizer (D.U : Set G)
  have hpoint : D.V₁ ≤ C := le_inf d.setup.point_le
    (le_centralizer_iff.mp d.setup.U_le_centralizer_point)
  have hn : D.L₁ ⊔ D.T ≤ normalizer (C : Set G) :=
    (le_inf d.setup.local_normalizes_V
      ((d.setup.local_le.trans (le_normalizer_conjugateSpanBy D.V D.H)).trans
        (normalizer_le_normalizer_centralizer D.U))).trans inf_normalizer_le_normalizer_inf
  rcases d.setup.irreducible C hpoint inf_le_left hn with he | he
  · exact he
  · apply False.elim
    apply d.star_U_ne_bot
    apply bot_unique
    rintro _ ⟨u, hu, rfl⟩
    have hcent : (u : G) ∈ centralizer (D.V : Set G) := by
      intro v hv
      have hvC : v ∈ C := he.symm ▸ hv
      exact (hvC.2 u hu).symm
    exact congrArg Subtype.val (starProjection_eq_one_of_centralizes_seed d c
      ⟨u, closure_le_L d hfull hu⟩ hcent)

/-- The center of the original closure, embedded in G, is the original point. -/
theorem closure_center_map (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hS : D.S g = D.VL) : (center D.U).map D.U.subtype = D.V₁ := by
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    have hcent : (u : G) ∈ centralizer (D.V : Set G) := by
      intro v hv
      exact congrArg Subtype.val (mem_center_iff.mp hu ⟨v, hVU hv⟩)
    have hstar := starProjection_eq_one_of_centralizes_seed d c
      ⟨u, closure_le_L d hfull u.property⟩ hcent
    have hfirst := mem_first_of_starProjection_eq_one c hS
      ⟨u, closure_le_L d hfull u.property⟩ hstar
    have hv : (u : G) ∈ D.V := c.orthogonal_intersection ▸ ⟨hfirst,u.property⟩
    rw [← seed_centralizer d c hfull]
    exact ⟨hv, fun v hv => congrArg Subtype.val (mem_center_iff.mp hu ⟨v,hv⟩)⟩
  · intro z hz
    refine ⟨⟨z,hVU (d.setup.point_le hz)⟩, mem_center_iff.mpr ?_, rfl⟩
    intro u
    exact Subtype.ext ((d.setup.U_le_centralizer_point u.property z hz).symm)

/-- The corresponding equality is in the intrinsic subgroup lattice of U. -/
theorem closure_center (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hS : D.S g = D.VL) : center D.U = D.V₁.subgroupOf D.U := by
  have hpoint : D.V₁ ≤ D.U := d.setup.point_le.trans (le_conjugateSpanBy _ _)
  apply map_injective D.U.subtype_injective
  rw [closure_center_map d c hfull hS,
    map_subgroupOf_eq_of_le hpoint]

/-- G.2.2 gives an elementary quotient by the actual center; the center has
order two and the given collapse makes U have order 32. -/
theorem closure_extraspecial (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hS : D.S g = D.VL) : IsExtraspecial 2 D.U := by
  let : Fact (IsPGroup 2 D.U) := ⟨d.setup.U_isPGroup⟩
  have hZ := closure_center d c hfull hS
  have hpoint : D.V₁ ≤ D.U := d.setup.point_le.trans (le_conjugateSpanBy _ _)
  have hZcard : Nat.card (center D.U) = 2 := by
    rw [hZ, Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv, d.point_card]
  have hphi : frattini D.U ≤ center D.U := by
    rw [hZ]
    intro u hu
    exact d.setup.frattini_U_le_point (mem_map_of_mem D.U.subtype hu)
  refine ⟨hZcard, ?_, ?_⟩
  · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center D.U)).mpr
        ((commutator_le_frattini_of_isPGroup (p := 2)).trans hphi)
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro q
      induction q using QuotientGroup.induction_on with
      | H u =>
        exact (QuotientGroup.eq_one_iff (u ^ 2)).mpr
          (hphi (pth_power_mem_frattini_of_isPGroup (p := 2) u))
  · apply QuotientGroup.nontrivial_iff.mpr
    intro he
    have hcard : Nat.card (center D.U) = Nat.card D.U := by
      rw [he, Nat.card_congr topEquiv.toEquiv]
    rw [hZcard, Hypothesis.closure_card_of_core_eq_first c hS] at hcard
    omega

/-- Genuine commuting quaternion factors in U, meeting in their common
central involution and generating U. -/
theorem closure_quaternion_factors (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hS : D.S g = D.VL) : Nonempty (QuaternionCentralProductData D.U) := by
  let := closure_extraspecial d c hfull hS
  let E := D.V.subgroupOf D.U
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hVU).mpr
    (d.setup.U_normal_in_T.1.trans d.setup.T_normalizes_V)
  let := d.setup.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hE : Nat.card E = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans c.seed_card
  have hZE : center D.U ≤ E := by
    rw [closure_center d c hfull hS]
    exact comap_mono d.setup.point_le
  obtain ⟨B,C,hB,hC,hspan,hmeet,hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary
      (Hypothesis.closure_card_of_core_eq_first c hS) E hE hZE
  exact ⟨⟨B,C,hB,hC,hmeet,hcomm,hspan⟩⟩

/-- The factors identify U with the literal diagonal quotient Q₈∘Q₈. -/
theorem closure_quaternion_model (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hS : D.S g = D.VL) : Nonempty (D.U ≃* QuaternionCentralProduct.Model) := by
  obtain ⟨q⟩ := closure_quaternion_factors d c hfull hS
  exact q.nonempty_model_equiv

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Quaternion
