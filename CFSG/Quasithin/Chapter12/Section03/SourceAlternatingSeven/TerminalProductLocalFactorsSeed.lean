module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsOmega
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductSeed
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientUniqueness
public import Theory.Representation.BinarySevenCode.WeightSixDisplacement
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The weight-two seed in the literal terminal local residual

A Sylow-central weight-six vector is moved by O²(C_L(e)). Every nontrivial
displacement of that vector has weight two, giving an original point in
[Z,L_e]. Its ambient centralizer is therefore contained in N_G(L), so the
selected escaping K cannot fix this seed.

The quotient-action kernel is normal in N_G(K); hence the literal L₂ is
normal in L_e. Once the remaining local product L_e=L₁L₂ is established,
L₁'s defining centralization of Z gives [Z,L_e]=[Z,L₂] and supplies the
weight-two fields of both terminal analyses. The local product and natural
marking remain with qt-d-1231-terminal-product; they are not assumed to be
source theorems here.

Source: Aschbacher--Smith, completion of 12.3.1, printed pp.811--812.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- Displacing any weight-six vector by the actual local residual produces
an original weight-two vector in its cyclic-seed commutator. -/
theorem exists_weight_two_in_cyclic_Le_commutator (f : V)
    (hf : weight (D.model.coordinates f).toAdd.val = 6) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ ⁅zpowers (f : G),P.Le⁆ := by
  obtain ⟨x,hx,hxc⟩ := Set.not_subset.mp (P.Le_not_le_weight_six_centralizer f hf)
  have hxL : x ∈ L := (map_subtype_le (pResidual 2 (L ⊓ P.pointCentralizer : Subgroup G)) hx).1
  let n : normalizer (V : Set G) := ⟨x,S.chosen.normalizes hxL⟩
  let v : V := V.normalizerMonoidHom n f * f⁻¹
  have he : (D.model.coordinates (V.normalizerMonoidHom n f)).toAdd =
      evenRepresentation (S.projection ⟨x,hxL⟩).val (D.model.coordinates f).toAdd := by
    simpa only [n,D.component_action ⟨x,hxL⟩] using D.model.equivariant n f
  have hmove : evenRepresentation (S.projection ⟨x,hxL⟩).val
      (D.model.coordinates f).toAdd ≠ (D.model.coordinates f).toAdd := by
    intro h
    have hfix := D.model.coordinates.injective (Multiplicative.toAdd.injective (he.trans h))
    exact hxc (mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix)))
  have hv : weight (D.model.coordinates v).toAdd.val = 2 := by
    change weight (D.model.coordinates (V.normalizerMonoidHom n f * f⁻¹)).toAdd.val = 2
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,← sub_eq_add_neg,he]
    exact weight_six_displacement _ _ hf hmove
  refine ⟨v,?_,hv,?_⟩
  · intro h
    rw [h,map_one] at hv
    have hzero : weight (0 : Word) = 0 := by decide
    exact (by decide : (0 : ℕ) ≠ 2) (hzero.symm.trans hv)
  · change ⁅x,(f : G)⁆ ∈ ⁅zpowers (f : G),P.Le⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hx (mem_zpowers (f : G))

/-- The literal Sylow omega seed has a weight-two displacement under L_e. -/
theorem exists_weight_two_in_Le_commutator
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ ⁅P.Z,P.Le⁆ := by
  obtain ⟨f,hf,hfT⟩ := D.naturalCoordinates.central_representative_weight structural
    (n := 6) (Or.inr (Or.inr rfl))
  have hfZ : (f : G) ∈ P.Z := by
    let := S.chosen.elementary
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow f.property,hfT,
      elemPow_eq_one_of_isElementaryAbelian _ f.property⟩
  obtain ⟨v,hv,hvw,hvm⟩ := P.exists_weight_two_in_cyclic_Le_commutator f hf
  exact ⟨v,hv,hvw,commutator_mono (zpowers_le.mpr hfZ) le_rfl hvm⟩

/-- Source 12.3.8 controls the centralizer of this actual moved seed. -/
theorem Le_commutator_centralizer_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    centralizer (⁅P.Z,P.Le⁆ : Subgroup G) ≤ normalizer (L : Set G) := by
  obtain ⟨v,hv,hvw,hvm⟩ := P.exists_weight_two_in_Le_commutator structural
  exact (centralizer_le (Set.singleton_subset_iff.mpr hvm)).trans
    (D.pointCentralizers v hv (Or.inl hvw))

/-- The selected escaping K cannot fix the whole L_e seed. -/
theorem residual_not_centralizes_Le_commutator
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ¬ P.K ≤ centralizer (⁅P.Z,P.Le⁆ : Subgroup G) := by
  intro h
  exact P.residual_escape structural (h.trans (P.Le_commutator_centralizer_le structural))

/-- The entire normalizer of K normalizes the literal quotient-action kernel. -/
theorem quotientCentralizer_normalized :
    normalizer (P.K : Set G) ≤ normalizer (P.quotientCentralizer : Set G) := by
  have h := P.quotientAction.ker.le_normalizer_map (normalizer (P.K : Set G)).subtype
  simpa only [quotientCentralizer,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using h

/-- Relative normality of the second residual inside the actual L_e. -/
theorem Le_normalizes_L2 (C : P.ComponentAnalysis) :
    P.Le ≤ normalizer (P.L2 : Set G) := by
  have h := (le_inf P.Le.le_normalizer
    ((P.Le_le_pointCentralizer.trans C.normalizes).trans P.quotientCentralizer_normalized)).trans
      inf_normalizer_le_normalizer_inf
  exact h.trans (normalizer_le_normalizer_characteristic_image
    (P.Le ⊓ P.quotientCentralizer) (pResidual 2 (P.Le ⊓ P.quotientCentralizer : Subgroup G)))

/-- The first residual fixes the original omega center by its definition. -/
theorem L1_centralizes_Z : P.L1 ≤ centralizer (P.Z : Set G) :=
  (map_subtype_le _).trans inf_le_right

/-- The local product identity is sufficient to identify its full moved seed
with that of the literal second factor. -/
theorem Le_commutator_eq_L2_of_product (C : P.ComponentAnalysis)
    (hproduct : P.Le = P.L1 ⊔ P.L2) : ⁅P.Z,P.Le⁆ = ⁅P.Z,P.L2⁆ := by
  have hL1 : P.L1 ≤ P.Le := hproduct ▸ le_sup_left
  have hn : P.L1 ≤ normalizer (⁅P.Z,P.L2⁆ : Subgroup G) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    let f := (MulAut.conj x).toMonoidHom
    have hZ : P.Z.map f = P.Z :=
      mem_normalizer_iff_map_conj_eq.mp ((P.L1_centralizes_Z.trans
        (Subgroup.centralizer_le_normalizer _)) hx)
    have hL2 : P.L2.map f = P.L2 :=
      mem_normalizer_iff_map_conj_eq.mp (P.Le_normalizes_L2 C (hL1 hx))
    have hm : (⁅P.Z,P.L2⁆ : Subgroup G).map f = ⁅P.Z,P.L2⁆ := by
      rw [map_commutator,hZ,hL2]
    exact hm ▸ mem_map_of_mem f hy
  apply le_antisymm ?_ (commutator_mono le_rfl P.L2_le_Le)
  rw [hproduct,commutator_comm P.Z]
  apply commutator_sup_le_of_relative_normal (P.L1 ⊔ P.L2) P.L1 P.L2 P.Z
    ⁅P.Z,P.L2⁆ (sup_le hn (normalizer_commutator_ge_right P.Z P.L2))
    le_sup_left le_sup_right
  · rw [commutator_eq_bot_iff_le_centralizer.mpr P.L1_centralizes_Z]
    exact bot_le
  · exact (commutator_comm P.L2 P.Z).le

/-- Actual application to the weight-two field of LocalFactorAnalysis and
ProductAnalysis; the local product remains the separate geometric obligation. -/
theorem exists_weight_two_in_L2_commutator_of_product
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) (hproduct : P.Le = P.L1 ⊔ P.L2) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ ⁅P.Z,P.L2⁆ := by
  simpa only [P.Le_commutator_eq_L2_of_product C hproduct] using
    P.exists_weight_two_in_Le_commutator structural

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
