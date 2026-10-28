module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstruction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.Source318
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.SLThreeCentralExtension.ChiefCohomology

/-!
# The fixed supplement after the reduced-module commutator calculation

For the original chosen nonsplit four-space, T-invariance identifies
Q = C_T(V) with O₂(LT). The marked action computes the kernel on L, and
the two-group quotient computes the kernel on LT. The proved normalizer
action then gives LT = LQ. These facts identify Ω₁Z(Q) with the literal
R₂(LT), and its L-fixed subgroup with Ω₁Z(T) ∩ C_G(L).

The four-dimensional central cover has zero first cohomology. Applied to
the actual conjugation section V/1, cocycle correction supplies the fixed
supplement whenever [Ω₁Z(Q), L] ≤ V. The original chosen module supplies
the reverse commutator inclusion.

The B.5.1 displacement bound remains the explicit source obligation
`OmegaCommutatorCalculation`. The final theorem connects its conditional
supplement to the original local geometry constructor; it does not claim
the source theorem before that bound is proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 12.4.5,
printed pp.813–814, using 1.4.1(4), B.5.1(1), and B.4.8(4), pp.91–92.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- T-invariance collapses the source orbit centralizer to the original Q. -/
theorem centralizer_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have he : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  simpa only [he] using D.orbit_centralizer h.toHypothesis1221

omit [Finite G] in
/-- The whole original elementary module lies in the central omega subgroup. -/
theorem chosen_le_omega_center :
    V ≤ omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
  let _ := D.elementary
  intro v hv
  apply (mem_omegaCenterIn_iff _ _).mpr
  exact ⟨⟨D.le_sylow hv, V.le_centralizer hv⟩,
    (le_centralizer_iff.mp (show (T : Subgroup G) ⊓ centralizer (V : Set G) ≤
      centralizer (V : Set G) from inf_le_right)) hv,
    elemPow_eq_one_of_isElementaryAbelian v hv⟩

/-- Faithfulness of the marked natural quotient computes the kernel on L. -/
theorem component_centralizer_eq_core (E : SLThreeExtension D) :
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  let _ := D.elementary
  apply le_antisymm
  · rintro x ⟨hxL,hxC⟩
    let l : L := ⟨x,hxL⟩
    have he : E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
      apply SLThreeCommutatorSource.action_injective E
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [E.conjugation, map_one]
      exact mul_inv_eq_iff_eq_mul.mpr (hxC _ v.toMul.property).symm
    have hk : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
      (E.quotientEquiv.injective (he.trans E.quotientEquiv.map_one.symm))
    exact mem_map_of_mem L.subtype hk
  · have hc : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      let : (L.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
        normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer D.sylow_normalizes_component)
      exact pCoreAmbient_mono_of_isSubnormalIn L _ 2 le_sup_left
        (inferInstance : (L.subgroupOf (L ⊔ (T : Subgroup G))).Normal).isSubnormal
    exact le_inf (pCoreIn_le 2 L) (hc.trans D.core_centralizes)

/-- The kernel on LT is a two-group, since its intersection with L is O₂(L). -/
theorem join_centralizer_eq_core (E : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let C := H ⊓ centralizer (V : Set G)
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hp : IsPGroup 2 (H ⧸ A) := by
    apply isPGroup_quotient_of_sup_eq_top A ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hC : IsPGroup 2 C := by
    intro c
    let x : H := ⟨c,c.property.1⟩
    obtain ⟨i,hi⟩ := hp (QuotientGroup.mk' A x)
    have hiL : (c : G) ^ 2 ^ i ∈ L := by
      have ha := (QuotientGroup.eq_one_iff (x ^ 2 ^ i)).mp (by
        change (QuotientGroup.mk' A) (x ^ 2 ^ i) = 1
        rwa [map_pow])
      exact ha
    have hic : (c : G) ^ 2 ^ i ∈ L.pCoreIn 2 :=
      (component_centralizer_eq_core D E).le ⟨hiL, (centralizer (V : Set G)).pow_mem c.property.2 _⟩
    obtain ⟨j,hj⟩ := (isPGroup_pCoreIn 2 L) ⟨_,hic⟩
    refine ⟨i+j, Subtype.ext ?_⟩
    have hh := congrArg Subtype.val hj
    simpa only [coe_pow, coe_one, pow_add, pow_mul] using hh
  have hn : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer
      ((sup_le D.normalizes hTV).trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  exact le_antisymm (le_pCoreIn_of_normalizes hC inf_le_left hn)
    (le_inf (pCoreIn_le 2 H) D.core_centralizes)

/-- The full normalizer action leaves no extra actor in LT/O₂(LT). -/
theorem join_eq_component_sup_core (E : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    L ⊔ (T : Subgroup G) = L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm
  · apply sup_le le_sup_left
    intro t ht
    obtain ⟨l,hl,he⟩ := SLThreeCommutatorSource.same_action_of_common_normalizer E
      t (hTV ht) (D.sylow_normalizes_component ht)
    have hc : l⁻¹ * t ∈ centralizer (V : Set G) := by
      intro v hv
      have hh := he v hv
      change t * v * t⁻¹ = l * v * l⁻¹ at hh
      apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
      calc
        (l⁻¹ * t) * v * (l⁻¹ * t)⁻¹ = l⁻¹ * (t * v * t⁻¹) * l := by group
        _ = v := by rw [hh]; group
    have hk : l⁻¹ * t ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      (join_centralizer_eq_core D E hTV).le
        ⟨(L ⊔ (T : Subgroup G)).mul_mem (mem_sup_left (L.inv_mem hl)) (mem_sup_right ht),hc⟩
    have hh := (L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
      (mem_sup_left hl) (mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le le_sup_left (pCoreIn_le 2 _)

/-- The fixed vectors of the larger omega-center are already central in T. -/
theorem omega_fixed_eq_sylow_fixed (E : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊓ centralizer (L : Set G) =
      omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hQ := centralizer_eq_core D h hTV
  ext x
  constructor
  · rintro ⟨hx,hxL⟩
    obtain ⟨hxQ,hxc,hxs⟩ := (mem_omegaCenterIn_iff Q x).mp hx
    have hLH : L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer ({x} : Set G) := by
      apply sup_le
      · intro l hl
        exact mem_centralizer_singleton_iff.mpr (hxL l hl)
      · intro q hq
        exact mem_centralizer_singleton_iff.mpr (hxc q (hQ.ge hq))
    rw [← join_eq_component_sup_core D E hTV] at hLH
    refine ⟨(mem_omegaCenterIn_iff _ x).mpr ⟨hxQ.1, ?_, hxs⟩, hxL⟩
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hLH (mem_sup_right ht))
  · rintro ⟨hx,hxL⟩
    obtain ⟨hxT,hxc,hxs⟩ := (mem_omegaCenterIn_iff (T : Subgroup G) x).mp hx
    exact ⟨(mem_omegaCenterIn_iff Q x).mpr
      ⟨⟨hxT,centralizer_le D.le_sylow hxc⟩,centralizer_le inf_le_left hxc,hxs⟩,hxL⟩

/-- The literal 1.4.1(4) identification in this marked source branch. -/
theorem omega_center_eq_reduced (E : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype := by
  let H := L ⊔ (T : Subgroup G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let R := omegaCenterIn Q
  have hQ : Q = H.pCoreIn 2 := centralizer_eq_core D h hTV
  have hRH : R ≤ H := (map_subtype_le _).trans (hQ.le.trans (pCoreIn_le 2 H))
  have hRN : H ≤ normalizer (R : Set G) := by
    apply (show H ≤ normalizer (Q : Set G) from ?_).trans
      (normalizer_le_normalizer_omegaCenterIn Q)
    rw [hQ]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  let A := R.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer hRN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hRH
  have hc : centralizer (A : Set H) = pCore 2 H := by
    apply le_antisymm
    · intro x hx
      have hxC : (x : G) ∈ centralizer (V : Set G) := by
        intro v hv
        exact congrArg Subtype.val (hx ⟨v,hRH (chosen_le_omega_center D hv)⟩
          (chosen_le_omega_center D hv))
      have hxQ := (join_centralizer_eq_core D E hTV).le ⟨x.property,hxC⟩
      obtain ⟨q,hq,hqx⟩ := hxQ
      exact (Subtype.ext hqx : q = x) ▸ hq
    · intro x hx a ha
      have hxQ : (x : G) ∈ Q := hQ.ge (mem_map_of_mem H.subtype hx)
      have haR : (a : G) ∈ R := ha
      exact Subtype.ext (((mem_omegaCenterIn_iff Q a).mp haR).2.1 x hxQ).symm
  have hr : IsPReduced 2 A := by
    refine ⟨inferInstance,inferInstance,?_⟩
    let e := QuotientGroup.quotientMulEquivOfEq hc
    have hp := pCore_map_iso 2 e.symm
    rw [pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at hp
    exact hp.symm
  apply le_antisymm
  · change R ≤ (ReducedModule H).map H.subtype
    rw [← map_subgroupOf_eq_of_le hRH]
    exact map_mono hr.le_reducedPSubgroup
  · rintro x ⟨a,ha,rfl⟩
    apply (mem_omegaCenterIn_iff Q _).mpr
    refine ⟨hQ.ge (mem_map_of_mem H.subtype (reducedPSubgroup_le_pCore 2 H ha)), ?_, ?_⟩
    · intro q hq
      obtain ⟨b,hb,rfl⟩ := hQ.le hq
      exact congrArg Subtype.val ((reducedPSubgroup_le_centralizer_pCore 2 H ha) b hb)
    · exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian a ha)


/-- B.4.8(4) on the original four-space: its first cohomology vanishes. -/
theorem extension_H1_subsingleton (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) : letI := D.elementary
    Subsingleton (H1 E.action) := by
  let _ := D.elementary
  exact SLThreeCentralExtension.H1_subsingleton_of_four_dimensional_cover E.action
    E.projection (isCover_of_indecomposable E.projection E.surjective E.kernel.le
      SLThreeCentralExtension.commutator_eq_top E.indecomposable)
    (SLThreeCommutatorSource.module_finrank_four E hne)

/-- The larger module splits over the whole original V once its L-displacements
lie in V. The action kernel and the fixed subgroup in T are derived here. -/
theorem fixed_supplement_of_commutator_le (E : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hcomm : ⁅omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)), L⁆ ≤ V) :
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V := by
  let _ := D.elementary
  let := extension_H1_subsingleton D E hne
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let R := omegaCenterIn Q
  let π : L →* BinaryLinearThree.Group :=
    E.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := E.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  let coords : V →* Multiplicative (Additive V) := {
    toFun := fun v => Multiplicative.ofAdd (Additive.ofMul v)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let d : BinaryConjugationSection L V ⊥ (E.action.comp π) := {
    section_le := D.le_component
    kernel_le := bot_le
    normalized := D.normalizes
    coordinates := coords
    onto := fun v => ⟨v.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext v
      change v = 1 ↔ (v : G) = 1
      exact Subtype.ext_iff
    equivariant := by
      intro l v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (E.conjugation l (Additive.ofMul v)).symm }
  have hc : ⁅L,R⁆ ≤ V := by rwa [commutator_comm]
  have hk : ∀ l ∈ π.ker, ∀ x ∈ R, ⁅(l : G),x⁆ ∈ (⊥ : Subgroup G) := by
    intro l hl x hx
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
      (E.quotientEquiv.injective ((show E.quotientEquiv
        (QuotientGroup.mk' (pCore 2 L) l) = 1 from hl).trans E.quotientEquiv.map_one.symm))
    have hlC : (l : G) ∈ centralizer (V : Set G) :=
      ((component_centralizer_eq_core D E).ge (mem_map_of_mem L.subtype hlcore)).2
    have hlQ : (l : G) ∈ Q := (centralizer_eq_core D h hTV).ge
      ((join_centralizer_eq_core D E hTV).le ⟨mem_sup_left l.property,hlC⟩)
    apply mem_bot.mpr
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (((mem_omegaCenterIn_iff Q x).mp hx).2.1 l hlQ)
  have he := d.sup_fixedPreimage_eq π hπ R (chosen_le_omega_center D) le_normalizer_of_normal hc hk
  have hf : commutatorPreimage R L ⊥ = R ⊓ centralizer (L : Set G) := by
    ext x
    rw [mem_commutatorPreimage_iff R L ⊥ le_normalizer_of_normal]
    simp only [mem_inf, mem_bot, commutatorElement_eq_one_iff_mul_comm,
      mem_centralizer_iff]
    exact and_congr_right (fun _ => forall_congr' fun l => forall_congr' fun _ => eq_comm)
  rw [hf, omega_fixed_eq_sylow_fixed D E h hTV] at he
  exact he

/-- The exact remaining B.5.1(1) source step, with all subgroup conventions fixed.
The reverse inclusion follows from the original chosen-module commutator identity. -/
def OmegaCommutatorCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ⁅omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)), L⁆ ≤ V

omit D in
/-- Supply the B.5.1 displacement bound to the proved cohomological supplement.
This is a conditional assembly; OmegaCommutatorCalculation still needs its source proof. -/
theorem fixedSupplement_of_omegaCommutator
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (moved : OmegaCommutatorCalculation.{u}) : FixedSupplementCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  exact fixed_supplement_of_commutator_le D E h ((structural G T L h).2.2 V D).1
    hne (moved G T L V h D hmodel hne)

omit D in
/-- Actual local geometry consumer of the proved supplement implication. -/
theorem localCalculations_of_omegaCommutator
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (moved : OmegaCommutatorCalculation.{u}) : LocalCalculations.{u} :=
  localCalculations_of_fixedSupplement structural marked
    (fixedSupplement_of_omegaCommutator structural marked moved)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
