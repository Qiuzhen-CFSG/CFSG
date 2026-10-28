module

public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.MSReduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.GroupTheory.PResidual.CentralizerCorrection

/-!
# The original natural-point centralizer in the binary MS argument

An MS commutator core contains the original natural three-space in its center.
If the central commutator has order eight, it is exactly that three-space.
Odd-index averaging then corrects every Sylow-central element by a vector fixed
by the whole Sylow subgroup. The original point radical forces that vector
onto its marked point. Consequently the omega-center centralizer is the literal
point parabolic, whose two-core is the original radical.

A nonzero Sylow-fixed vector also proves that the Sylow omega-center cannot
be central in the whole group. ClassificationExclusions applies these facts
to cases (3)--(5) of C.1.34 on the actual Baumann MS pair.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, especially the
natural-point exclusion on p.143; C.1.34, pp.136--137.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open ChapterB Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
universe u
variable {G : Type u} [Group G] [Finite G] {V : Subgroup G} [V.Normal]
  [IsElementaryAbelian 2 V]
namespace NaturalAction
variable (d : NaturalAction V)

include d in
/-- The original natural module has no residual-fixed nonidentity vector. -/
theorem fixed_residual_bot : V ⊓ centralizer (pResidual 2 G : Set G) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [d.fixed_card, d.residual_image]
  exact PointOffenders.top_fixed_card

include d in
omit [Finite G] in
/-- The original elementary normal module lies in the ambient two-core. -/
theorem module_le_core : V ≤ pCore 2 G := by
  rw [← d.kernel, d.kernel_centralizer]
  exact V.le_centralizer

include d in
/-- A nontrivial Sylow-fixed point prevents a central Sylow omega-center. -/
theorem omega_not_central (S : Sylow 2 G) :
    ¬ Subgroup.omegaCenterIn (S : Subgroup G) ≤ center G := by
  intro hc
  have hV : V ≠ ⊥ := by
    intro he
    have hh := d.module_card
    rw [he, Subgroup.card_bot] at hh
    omega
  have hn := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (S : Subgroup G)
    (d.module_le_core.trans (pCore_isPGroup.le_sylow_of_normal S)) S.isPGroup'
    (by rw [normalizer_eq_top]; exact le_top) hV
  apply hn
  apply bot_unique
  apply le_trans _ d.fixed_residual_bot.le
  exact inf_le_inf_left _ (hc.trans (by
    intro x hx l _
    exact mem_center_iff.mp hx l))


private theorem fixed_point_coordinates (v : Geometry.Vector)
    (hv : ∀ a ∈ pointV, a • v = v) : v 1 = 0 ∧ v 2 = 0 := by
  have h1 := hv (PointOffenders.row (Multiplicative.ofAdd (1,0)))
    (PointOffenders.row_range ▸ ⟨_,rfl⟩)
  have h2 := hv (PointOffenders.row (Multiplicative.ofAdd (0,1)))
    (PointOffenders.row_range ▸ ⟨_,rfl⟩)
  have he : ∀ v : Geometry.Vector,
      PointOffenders.row (Multiplicative.ofAdd (1,0)) • v = v →
      PointOffenders.row (Multiplicative.ofAdd (0,1)) • v = v →
      v 1 = 0 ∧ v 2 = 0 := by decide +kernel
  exact he v h1 h2

private theorem point_vectors (v : Geometry.Vector) (h1 : v 1 = 0) (h2 : v 2 = 0) :
    v = 0 ∨ v = flagPoint.val := by
  have he : ∀ v : Geometry.Vector, v 1 = 0 → v 2 = 0 →
      v = 0 ∨ v = flagPoint.val := by decide +kernel
  exact he v h1 h2

private theorem parabolic_fixes (g : SL) (hg : g ∈ pointParabolicSL)
    (v : Geometry.Vector) (hv : v 1 = 0 ∧ v 2 = 0) : g • v = v := by
  rcases point_vectors v hv.1 hv.2 with rfl | rfl
  · exact map_zero (BinaryLinearThree.W g)
  · rw [← Fano.stabilizer_flagPoint_SL] at hg
    exact congrArg Subtype.val (show g • flagPoint = flagPoint from hg)

private theorem parabolic_of_fixes (g : SL) (v : Geometry.Vector)
    (hv : v 1 = 0 ∧ v 2 = 0) (hne : v ≠ 0) (hg : g • v = v) :
    g ∈ pointParabolicSL := by
  have he := (point_vectors v hv.1 hv.2).resolve_left hne
  rw [← Fano.stabilizer_flagPoint_SL]
  apply Subtype.ext
  change g.val.mulVec flagPoint.val = flagPoint.val
  change g.val.mulVec v = v at hg
  rwa [he] at hg

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem coordinates_fixed (A : Subgroup G) (v : V)
    (hv : (v : G) ∈ centralizer (A : Set G)) :
    ∀ a ∈ A.map d.q, a • (d.coordinates v).toAdd = (d.coordinates v).toAdd := by
  rintro _ ⟨a,ha,rfl⟩
  apply (d.action a v).symm.trans
  congr 2
  apply Subtype.ext
  change a * (v : G) * a⁻¹ = v
  rw [hv a ha, mul_inv_cancel_right]

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem fixes_of_coordinates (g : G) (v : V)
    (h : d.q g • (d.coordinates v).toAdd = (d.coordinates v).toAdd) :
    (v : G) * g = g * (v : G) := by
  have he : MulAut.conjNormal g v = v :=
    d.coordinates.injective (Multiplicative.toAdd.injective ((d.action g v).trans h))
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm


include d in
/-- Correct a Sylow-central element in the original natural module; uniqueness makes the correction Sylow-fixed. -/
theorem sylow_fixed_correction
    {κ : GroupClass.{u}} {K R : Subgroup G} (h : BinaryMS.Input κ K R)
    (hZ : ⁅(center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype,K⁆ ≤ V)
    (S : Sylow 2 G) (z : G) (hz : z ∈ centralizer (S : Set G)) :
    ∃ q ∈ V ⊓ centralizer (S : Set G), q⁻¹ * z ∈ centralizer (K : Set G) := by
  let := h.component_normal
  have hf : V ⊓ centralizer (K : Set G) = ⊥ := by
    rw [← h.residual_eq]
    exact d.fixed_residual_bot
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPm : (P : Subgroup K).map K.subtype ≤ (S : Subgroup G) := by
    rintro _ ⟨p,hp,rfl⟩
    rw [hP] at hp
    exact hp
  have hp : IsPPerfect 2 K := by rw [← h.residual_eq]; exact isPPerfect_pResidual 2
  obtain ⟨q,hq,hc⟩ := fixed_correction_of_center_commutator K (pCore 2 G) V
    hp pCore_isPGroup le_normalizer_of_normal le_normalizer_of_normal
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) hZ P z
    (h.core_selfCentralizing (centralizer_le (pCore_isPGroup.le_sylow_of_normal S) hz))
    (centralizer_le ((commutator_le_left _ _).trans (pCore_isPGroup.le_sylow_of_normal S)) hz)
    (centralizer_le hPm hz)
  refine ⟨q,⟨hq.1,?_⟩,hc⟩
  intro s hs
  let q' : G := s * q * s⁻¹
  let c : G := q⁻¹ * z
  let c' : G := s * c * s⁻¹
  have hq' : q' ∈ V := (inferInstance : V.Normal).conj_mem q hq.1 s
  have hc' : c' ∈ centralizer (K : Set G) :=
    (inferInstance : (centralizer (K : Set G)).Normal).conj_mem c hc s
  have hprod : q' * c' = q * c := by
    calc
      q' * c' = s * (q * c) * s⁻¹ := by dsimp [q',c']; group
      _ = s * z * s⁻¹ := by simp only [c,mul_inv_cancel_left]
      _ = z := by rw [hz s hs,mul_inv_cancel_right]
      _ = q * c := (mul_inv_cancel_left q z).symm
  have hd : q⁻¹ * q' = c * c'⁻¹ := by
    calc
      q⁻¹ * q' = q⁻¹ * (q' * c') * c'⁻¹ := by group
      _ = q⁻¹ * (q * c) * c'⁻¹ := by rw [hprod]
      _ = c * c'⁻¹ := by group
  have hone : q⁻¹ * q' = 1 := by
    apply show q⁻¹ * q' ∈ (⊥ : Subgroup G) → q⁻¹ * q' = 1 from id
    rw [← hf]
    refine ⟨V.mul_mem (V.inv_mem hq.1) hq',?_⟩
    rw [hd]
    exact (centralizer _).mul_mem hc ((centralizer _).inv_mem hc')
  have heq : q' = q := (inv_mul_eq_one.mp hone).symm
  exact mul_inv_eq_iff_eq_mul.mp heq

/-- The centralizer is the literal point parabolic, under the original action and radical marking. -/
theorem omega_centralizer_eq_point_of_center_commutator
    {κ : GroupClass.{u}} {K R : Subgroup G} (h : BinaryMS.Input κ K R)
    (hZ : ⁅(center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype,K⁆ ≤ V)
    (hR : R = d.P.pCoreIn 2) (himage : R.map d.q = pointV)
    (S : Sylow 2 G) (hRS : R ≤ (S : Subgroup G)) :
    centralizer (Subgroup.omegaCenterIn (S : Subgroup G) : Set G) = d.P := by
  have hRP : R ≤ d.P := hR ▸ pCoreIn_le 2 d.P
  have hRC : R ≤ centralizer (Subgroup.omegaCenterIn (S : Subgroup G) : Set G) := by
    intro r hr z hz
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1 r (hRS hr) |>.symm
  have hfixed (v : V) (hv : (v : G) ∈ centralizer (S : Set G)) :
      (d.coordinates v).toAdd 1 = 0 ∧ (d.coordinates v).toAdd 2 = 0 := by
    apply fixed_point_coordinates
    rw [← himage]
    exact d.coordinates_fixed R v (centralizer_le hRS hv)
  apply le_antisymm
  · intro g hg
    have hn : V ≠ ⊥ := by
      intro hz
      have hc := d.module_card
      rw [hz, Subgroup.card_bot] at hc
      omega
    obtain ⟨v,hv,hv1⟩ := (V ⊓ Subgroup.omegaCenterIn (S : Subgroup G)).bot_or_exists_ne_one.resolve_left
      (inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (S : Subgroup G)
        (d.module_le_core.trans (pCore_isPGroup.le_sylow_of_normal S)) S.isPGroup'
        (by rw [normalizer_eq_top]; exact le_top) hn)
    let vV : V := ⟨v,hv.1⟩
    apply parabolic_of_fixes (d.q g) (d.coordinates vV).toAdd
      (hfixed vV ((mem_omegaCenterIn_iff _ _).mp hv.2).2.1)
    · intro hz
      apply hv1
      exact congrArg Subtype.val (d.coordinates.map_eq_one_iff.mp
        (show d.coordinates vV = 1 from hz))
    · apply (d.action g vV).symm.trans
      congr 2
      apply Subtype.ext
      change g * v * g⁻¹ = v
      rw [← hg v hv.2, mul_inv_cancel_right]
  · intro p hp
    obtain ⟨l,hl,r,hr,rfl⟩ := h.product p
    have hlP : l ∈ d.P := (mul_mem_cancel_right (hRP hr)).mp hp
    apply mul_mem _ (hRC hr)
    intro z hz
    obtain ⟨q,hq,hqc⟩ := d.sylow_fixed_correction h hZ S z
      ((mem_omegaCenterIn_iff _ _).mp hz).2.1
    have hqV : q ∈ V := hq.1
    have hlq : q * l = l * q := d.fixes_of_coordinates l ⟨q,hqV⟩
      (parabolic_fixes (d.q l) hlP _ (hfixed ⟨q,hqV⟩ hq.2))
    calc
      z * l = (q * (q⁻¹ * z)) * l := by rw [mul_inv_cancel_left]
      _ = q * ((q⁻¹ * z) * l) := mul_assoc _ _ _
      _ = q * (l * (q⁻¹ * z)) := by rw [← hqc l hl]
      _ = (q * l) * (q⁻¹ * z) := (mul_assoc _ _ _).symm
      _ = (l * q) * (q⁻¹ * z) := by rw [hlq]
      _ = l * z := by rw [mul_assoc, mul_inv_cancel_left]


include d in
/-- The original natural module embeds in the center of the actual MS commutator core. -/
theorem module_le_center_core {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) :
    V ≤ (center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype := by
  have hVQ : V ≤ BinaryMS.commutatorCore K := by
    rw [← h.residual_eq]
    exact d.module_le_commutator.trans (commutator_mono d.module_le_core le_rfl)
  intro v hv
  refine ⟨⟨v,hVQ hv⟩,mem_center_iff.mpr (fun q => Subtype.ext ?_),rfl⟩
  have hqc : (q : G) ∈ centralizer (V : Set G) := by
    rw [← d.kernel_centralizer, d.kernel]
    exact commutator_le_left _ _ q.property
  exact (hqc v hv).symm

include d in
/-- The order-eight central commutator is the original natural module. -/
theorem center_commutator_eq_module_of_card {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R)
    (hc : Nat.card (⁅(center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype,K⁆ : Subgroup G) = 8) :
    ⁅(center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype,K⁆ = V := by
  apply (Subgroup.eq_of_le_of_card_ge (H := V) ?_ ?_).symm
  · have he := d.module_commutator
    rw [h.residual_eq] at he
    exact he.symm.le.trans (commutator_mono (d.module_le_center_core h) le_rfl)
  · rw [hc,d.module_card]

include d in
/-- An order-eight center is the original natural module. -/
theorem center_eq_module_of_card {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R)
    (hc : Nat.card ((center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype) = 8) :
    (center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype = V := by
  apply (Subgroup.eq_of_le_of_card_ge (d.module_le_center_core h) ?_).symm
  rw [hc,d.module_card]

end NaturalAction
end CFSG.Quasithin.ChapterC.NaturalPointControl
