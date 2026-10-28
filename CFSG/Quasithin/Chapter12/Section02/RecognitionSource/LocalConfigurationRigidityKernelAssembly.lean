module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelD3
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelResidual
/-!
# Centralizer consequences of both literal cohomology branches

The fixed-involution exclusion in dimension three and H1 vanishing in
dimensions four and five give the same kernel split. Multiplication in G
then supplies both direct products, the Sylow product, centrality and the
order-two bound in every dimension. The final record application retains
exactly the still-undischarged Sylow-factor disjointness premise. Its proof
and the unconditional record remain with qt-d-12225-common-centralizers;
final source-theorem assembly belongs to qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, original 12.2.25, printed pp.804--805.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- Both dimensional arguments split the original kernel. -/
theorem source_kernel_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  by_cases hd : d = 3
  · exact three_kernel_split h D structural A C hnone hd
  · exact higher_kernel_split D A C (by have := A.dimension.1; omega)

/-- The multiplication map identifies the actual kernel with V × C_T(L). -/
theorem source_kernel_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) (hnone : NoEscape L V) :
    ∃ e : V × ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (V : Set G)),
      ∀ v z, (e (v,z) : G) = (v : G) * (z : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) (kernel_disjoint D A)
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le D.le_component)))
  exact ⟨e.trans (MulEquiv.subgroupCongr (source_kernel_split h D structural A C hnone).symm),he⟩

/-- The second literal centralizer decomposition in (*) in every dimension. -/
theorem source_centralizer_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  centralizer_split_of_kernel_split h D structural A C hnone (source_kernel_split h D structural A C hnone)

/-- Both decompositions in (*) use the original multiplication maps. -/
theorem source_centralizer_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ e : U × ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (U : Set G)),
      ∀ u z, (e (u,z) : G) = (u : G) * (z : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) (core_disjoint_component_centralizer D A C)
    (le_centralizer_iff.mp (component_centralizer_le_core_centralizer D A C))
  exact ⟨e.trans (MulEquiv.subgroupCongr (source_centralizer_split h D structural A C hnone).symm),he⟩

/-- The two elementary central factors have the same order, as used in the
source's subsequent rank bound. No order-two bound is assumed. -/
theorem source_central_factors_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) =
      Nat.card ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  obtain ⟨e,_⟩ := source_centralizer_directProduct h D structural A C hnone
  obtain ⟨f,_⟩ := chosen_centralizer_core_directProduct h D structural A C hnone
  have hc := Nat.card_congr (e.trans f.symm).toEquiv
  rw [Nat.card_prod, Nat.card_prod] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- The literal hyperplane split, re-exported with the common centralizers. -/
theorem source_hyperplane_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      U ⊔ V ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) :=
  hyperplane_pair_split h D structural A C hnone

/-- The source Sylow product over C_T(L), in every dimension. -/
theorem source_sylow_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have he := sylow_split_over_kernel h D structural A
  rw [source_kernel_split h D structural A C hnone, ← sup_assoc,
    sup_eq_left.mpr (le_inf D.le_sylow D.le_component)] at he
  exact he

/-- The component's Sylow centralizer is central in T, after the literal
kernel split. Elementarity of R supplies its own internal commutativity. -/
theorem source_component_centralizer_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ centralizer (T : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary h D structural A C hnone
  have hZR : Z ≤ R := le_inf inf_le_left (component_centralizer_le_core_centralizer D A C)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hZR
  apply le_centralizer_iff.mp
  conv_lhs => rw [source_sylow_split h D structural A C hnone]
  exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le inf_le_right)))
    (le_centralizer Z)

/-- The second central factor is central in T as well: its T-commutator
lies both in U and in the disjoint factor C_T(I). -/
theorem source_pair_centralizer_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) ≤ centralizer (T : Set G) := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZU := component_centralizer_le_core_centralizer D A C
  have hZT := source_component_centralizer_central h D structural A C hnone
  have hER : E ≤ (T : Subgroup G) ⊓ centralizer (U : Set G) :=
    le_inf inf_le_left (inf_le_right.trans
      (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  rw [← disjoint_iff.mp C.core_disjoint_sylow_pair_centralizer]
  refine le_inf ?_ (le_normalizer_iff_commutator_le_left.mp (sylow_normalizes_pair_centralizer C))
  apply commutator_le.mpr
  intro x hx t ht
  have hprod : x ∈ (U : Set G) * (Z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U Z (hZU.trans (Subgroup.centralizer_le_normalizer _)),
      ← source_centralizer_split h D structural A C hnone]
    exact hER hx
  obtain ⟨u,hu,z,hz,rfl⟩ := hprod
  have hc : ⁅z,t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZT hz t ht).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hc, mul_one, mul_inv_cancel, one_mul]
  exact (le_normalizer_iff_commutator_le_left.mp C.sylow_normalizes_core)
    (commutator_mem_commutator hu ht)

/-- The hyperplane product equivalence uses multiplication in G. -/
theorem source_hyperplane_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ e : ↥(U ⊔ V) × ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)),
      ∀ x z, (e (x,z) : G) = (x : G) * (z : G) :=
  hyperplane_pair_directProduct h D structural A C hnone

/-- The source's order-two bound for the two common central factors in the
all-dimensional calculation. -/
theorem source_component_centralizer_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≤ 2 := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let F := V ⊓ centralizer (T : Set G)
  have hZT : Z ≤ centralizer (T : Set G) := source_component_centralizer_central h D structural A C hnone
  have hET : E ≤ centralizer (T : Set G) := source_pair_centralizer_central h D structural A C hnone
  have hEZ : Disjoint E Z := disjoint_iff.mpr (by rw [inf_comm]; exact common_trivial h D C)
  have hFZ : Disjoint F Z := (kernel_disjoint D A).mono_left inf_le_left
  have hZE : Z ≤ normalizer (E : Set G) :=
    ((le_centralizer_iff.mp hET).trans' inf_le_left).trans (Subgroup.centralizer_le_normalizer _)
  have hZF : Z ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp ((inf_le_left.trans D.le_sylow).trans (le_centralizer_iff.mp hZT))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEQ : E ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    le_inf inf_le_left (hET.trans (centralizer_le D.le_sylow))
  have hEZF : E ≤ Z ⊔ F := by
    have hh : E ≤ (Z ⊔ V) ⊓ centralizer (T : Set G) := by
      rw [sup_comm Z V, ← source_kernel_split h D structural A C hnone]
      exact le_inf hEQ hET
    change E ≤ (Z ⊔ V) ⊓ centralizer (((T : Subgroup G) : Set G)) at hh
    rwa [inf_centralizer_sup_of_centralizing Z V (T : Subgroup G)
      (hZT.trans (centralizer_le D.le_sylow) |>.trans (Subgroup.centralizer_le_normalizer _)) hZT] at hh
  have hcard : Nat.card E * Nat.card Z ≤ Nat.card F * Nat.card Z := by
    rw [← card_sup_eq_mul_of_normalizes_of_disjoint E Z hZE hEZ,
      ← card_sup_eq_mul_of_normalizes_of_disjoint F Z hZF hFZ]
    have hi : E ⊔ Z ≤ F ⊔ Z := sup_le (hEZF.trans_eq (sup_comm Z F)) le_sup_right
    exact Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
  have he : Nat.card E ≤ Nat.card F := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  rw [source_central_factors_card h D structural A C hnone]
  exact he.trans (chosen_sylow_fixed_card D A)

/-- Assembly of the all-dimensional record after the still-owned Sylow
intersection step. The common-centralizers owner must discharge `hdisjoint`;
this conditional application is not a completed source theorem. -/
theorem centralizers_of_sylow_disjoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hdisjoint : Disjoint ((T : Subgroup G) ⊓ L)
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    LocalRigidityCentralizers T L V U P where
  kernel_split := source_kernel_split h D structural A C hnone
  kernel_disjoint := kernel_disjoint D A
  centralizer_split := source_centralizer_split h D structural A C hnone
  centralizer_disjoint := core_disjoint_component_centralizer D A C
  common_trivial := common_trivial h D C
  elementary := radical_elementary h D structural A C hnone
  component_centralizer_card := source_component_centralizer_card h D structural A C hnone
  sylow_split := source_sylow_split h D structural A C hnone
  sylow_disjoint := hdisjoint
  component_centralizer_central := source_component_centralizer_central h D structural A C hnone
  pair_centralizer_central := source_pair_centralizer_central h D structural A C hnone
  hyperplane_centralizer := source_hyperplane_centralizer h D structural A C hnone
  residual_normalizes := residual_normalizes h D structural A C hnone

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
