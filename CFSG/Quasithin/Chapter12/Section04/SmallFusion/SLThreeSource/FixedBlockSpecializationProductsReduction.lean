module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationBlock
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlock
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionBase
public import Theory.GroupTheory.FixedSupplementCentralizer

/-!
# Reduction of the marked MS centralizer products

Write Q = C_T(V) = O₂(LR) and P = O₂(L). The commutator
[P,Q] is contained in the original fixed line: the three-subgroups lemma
proves this bound, but does not make it trivial. Once P centralizes Q,
vanishing H¹ of the original four-dimensional module corrects each element
of Q by a vector, proving Q = V C_T(L).

The second product follows from two independent facts about the literal
residual O²(C_L(E)): its centralizer in R fixes V, and its fixed subgroup
in V is E. These facts and kernel centralization remain explicit here.
The final theorem applies both products to the existing Frattini consumer;
only that application assumes N_G(R) normalizes the residual.

Source: Aschbacher--Smith, 12.4.6, printed p.814; C.1.34(5), pp.136--137,
and B.4.8(4), pp.91--92. This module proves a conditional reduction,
not the source specialization before its three premises are discharged.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The obstruction to kernel fixation lies in the original fixed line.
The three-subgroups lemma supplies centralization by L, not vanishing. -/
theorem ms_kernel_commutator_le_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hQ : msQ L d.R = V) :
    ⁅L.pCoreIn 2, (T : Subgroup G) ⊓ centralizer (V : Set G)⁆ ≤ fixedSubgroup L V := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let P := L.pCoreIn 2
  have hPL : P ≤ L := pCoreIn_le 2 L
  have hPQ : P ≤ Q := by
    change P ≤ (T : Subgroup G) ⊓ centralizer (V : Set G)
    rw [← d.ms_core_eq ext h hTV]
    exact pCoreAmbient_mono_of_isSubnormalIn L (L ⊔ d.R) 2 le_sup_left
      d.ms_relative_normal.isSubnormal
  have hQL : ⁅Q,L⁆ = V := by
    have hh : ⁅(L ⊔ d.R).pCoreIn 2,L⁆ = V := hQ
    rwa [d.ms_core_eq ext h hTV] at hh
  have hVC : V ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mpr (show Q ≤ centralizer (V : Set G) from inf_le_right)
  have hLP : ⁅L,P⁆ ≤ V := by
    rw [←hQL, commutator_comm Q L]
    exact commutator_mono le_rfl hPQ
  have hcentral : ⁅⁅P,Q⁆,L⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
    (by
      rw [hQL]
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (hVC.trans (centralizer_le hPQ)))
    (commutator_eq_bot_iff_le_centralizer.mpr (hLP.trans hVC))
  exact le_inf ((commutator_mono hPL le_rfl).trans_eq
    ((commutator_comm L Q).trans hQL))
    (commutator_eq_bot_iff_le_centralizer.mp hcentral)

omit [Finite G] in
/-- Both source products have the expected inclusion without any kernel
or residual-action calculation. -/
theorem ms_products_lower_bounds :
    V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ≤
      d.R ⊓ centralizer (d.L₁ : Set G) := by
  let _ := D.elementary
  have hEL : d.E ≤ centralizer (d.L₁ : Set G) :=
    le_centralizer_iff.mpr (d.lineResidual_le.trans inf_le_right)
  have hCL : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      centralizer (d.L₁ : Set G) :=
    inf_le_right.trans (centralizer_le (d.lineResidual_le.trans inf_le_left))
  refine ⟨sup_le (le_inf D.le_sylow V.le_centralizer)
    (inf_le_inf_left _ (centralizer_le D.le_component)), ?_⟩
  apply sup_le
  · exact le_inf (le_inf (d.le_module.trans D.le_sylow)
      ((d.le_module.trans V.le_centralizer).trans (centralizer_le d.le_module))) hEL
  · exact le_inf (inf_le_inf_left _
      (centralizer_le (d.le_module.trans D.le_component))) hCL

/-- Correct the actual core elements using the original four-space. The
quotient-action kernel must centralize the entire core, not just V. -/
theorem ms_core_product_of_core_centralization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥) (hQ : msQ L d.R = V)
    (hkernel : L.pCoreIn 2 ≤
      centralizer (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let _ := D.elementary
  let := extension_H1_subsingleton D ext hne
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let π : L →* BinaryLinearThree.Group :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  let coords : V →* Multiplicative (Additive V) := {
    toFun := fun v => Multiplicative.ofAdd (Additive.ofMul v)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let c : BinaryConjugationSection L V ⊥ (ext.action.comp π) := {
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
      exact (ext.conjugation l (Additive.ofMul v)).symm }
  have hc : ⁅L,Q⁆ ≤ V := by
    have hh : ⁅(L ⊔ d.R).pCoreIn 2,L⁆ = V := hQ
    rw [d.ms_core_eq ext h hTV,commutator_comm] at hh
    exact hh.le
  have hk : ∀ l ∈ π.ker, ∀ x ∈ Q, ⁅(l : G),x⁆ ∈ (⊥ : Subgroup G) := by
    intro l hl x hx
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
      (ext.quotientEquiv.injective ((show ext.quotientEquiv
        (QuotientGroup.mk' (pCore 2 L) l) = 1 from hl).trans ext.quotientEquiv.map_one.symm))
    exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      ((hkernel (mem_map_of_mem L.subtype hlcore)) x hx).symm)
  have he := c.sup_fixedPreimage_eq π hπ Q
    (le_inf D.le_sylow V.le_centralizer) le_normalizer_of_normal hc hk
  have hf : commutatorPreimage Q L ⊥ = Q ⊓ centralizer (L : Set G) := by
    ext x
    rw [mem_commutatorPreimage_iff Q L ⊥ le_normalizer_of_normal]
    simp only [mem_inf, mem_bot, commutatorElement_eq_one_iff_mul_comm,
      mem_centralizer_iff]
    exact and_congr_right (fun _ => forall_congr' fun l => forall_congr' fun _ => eq_comm)
  have hfix : Q ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (L : Set G) := by
    change ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊓ centralizer (L : Set G) = _
    rw [inf_assoc, inf_eq_right.mpr (centralizer_le D.le_component)]
  rw [hf,hfix,sup_comm] at he
  exact he

omit [Finite G] in
/-- Restrict the first product to the centralizer of the literal residual. -/
theorem ms_residual_centralizer_of_geometry
    (hproduct : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (himage : d.R ⊓ centralizer (d.L₁ : Set G) ≤ centralizer (V : Set G))
    (hfixed : V ⊓ centralizer (d.L₁ : Set G) = d.E) :
    d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hQR : Q ≤ d.R := inf_le_inf_left _ (centralizer_le d.le_module)
  have he : d.R ⊓ centralizer (d.L₁ : Set G) = Q ⊓ centralizer (d.L₁ : Set G) := by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) himage) inf_le_right
    · exact inf_le_inf_right _ hQR
  have hCV : C ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le D.le_component)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCL₁ : C ≤ centralizer (d.L₁ : Set G) :=
    inf_le_right.trans (centralizer_le (d.lineResidual_le.trans inf_le_left))
  rw [he, show Q = V ⊔ C from hproduct, sup_comm V C,
    inf_centralizer_sup_of_centralizing C V d.L₁ hCV hCL₁, hfixed, sup_comm]

/-- Assemble both actual products from the core-fixation and residual-action
calculations. Neither product is a premise of this theorem. -/
theorem ms_identities_of_core_and_residual_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥) (hQ : msQ L d.R = V)
    (hkernel : L.pCoreIn 2 ≤
      centralizer (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
    (himage : d.R ⊓ centralizer (d.L₁ : Set G) ≤ centralizer (V : Set G))
    (hfixed : V ⊓ centralizer (d.L₁ : Set G) = d.E) : FixedBlockIdentities d := by
  have hp := d.ms_core_product_of_core_centralization h ext hTV hne hQ hkernel
  exact ⟨hp, d.ms_residual_centralizer_of_geometry hp himage hfixed⟩

/-- The existing fixed-residual consumer, retaining its separate normalizer
hypothesis only at this final application. -/
theorem ms_selfCentralizing_of_core_and_residual_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hQ : msQ L d.R = V)
    (hkernel : L.pCoreIn 2 ≤
      centralizer (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
    (himage : d.R ⊓ centralizer (d.L₁ : Set G) ≤ centralizer (V : Set G))
    (hfixed : V ⊓ centralizer (d.L₁ : Set G) = d.E) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = V ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = fixedSubgroup L V := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have b := d.ms_identities_of_core_and_residual_geometry h ext
    ((structural G T L h).2.2 V D).1 hne hQ hkernel himage hfixed
  exact fixedBlock_selfCentralizing h structural marked hmodel hne d hescape hline
    b.product b.residual_centralizer

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
