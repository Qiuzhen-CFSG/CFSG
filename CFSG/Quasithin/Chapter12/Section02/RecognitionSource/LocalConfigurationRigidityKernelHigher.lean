module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelHyperplane
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelSylow
public import Theory.Representation.FirstCohomologyAutomorphism.FixedSupplement
public import Theory.Representation.SLHigherNaturalFirstCohomology

/-!
# Higher-dimensional centralizer reductions for 12.2.25

For the original chosen binary natural module in dimension at least four,
vanishing of natural first cohomology splits the literal Sylow kernel over V.
The common centralizer calculations then give both decompositions in (*), the
hyperplane centralizer, the Sylow product, and centrality of the two factors.
All displayed product equivalences are induced by multiplication in G.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
original 12.2.25, printed pp. 804–805. The dimension-three exclusion, the
order bound, the Sylow-factor disjointness and Thompson normalization are
separate remaining obligations of the common-centralizers owner; these
reductions alone do not assert the complete LocalRigidityCentralizers record.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- In dimensions four and five, the original kernel splits over V by
vanishing of natural first cohomology. The quotient kernel is the actual
O₂(L), which is allowed to be larger than V. -/
theorem higher_kernel_split
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) (hd : 4 ≤ d) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let := D.elementary
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  obtain ⟨e,f,hf⟩ := A.natural
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : a.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have he (l : L) (v : Fin d → ZMod 2) :
      (f.symm (Multiplicative.ofAdd (Representation.specialLinearNatural d (a l) v)) : G) =
        l * (f.symm (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ := by
    simpa [a] using hf l (f.symm (Multiplicative.ofAdd v))
  let : Subsingleton (Representation.OneCohomology.H1
      (Representation.specialLinearNatural (k := ZMod 2) d)) :=
    Representation.OneCohomology.SLHigherNatural.H1_subsingleton_of_four_le hd
  have hs := Representation.OneCohomology.eq_sup_inf_centralizer_of_H1_zero L V Q
    D.le_component (le_inf D.le_sylow (le_centralizer V)) a ha f
    (Representation.specialLinearNatural (k := ZMod 2) d) he
    (by rw [hk]; exact component_core_centralizes_kernel D A C)
    (kernel_commutator_eq D A C).le
  have hc : Q ⊓ centralizer (L : Set G) = (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le D.le_component))) inf_le_right)
  exact hs.trans (congrArg (fun Z : Subgroup G => V ⊔ Z) hc)

/-- The multiplication map identifies the actual kernel with V × C_T(L). -/
theorem higher_kernel_directProduct
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) (hd : 4 ≤ d) :
    ∃ e : V × ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (V : Set G)),
      ∀ v z, (e (v,z) : G) = (v : G) * (z : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) (kernel_disjoint D A)
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le D.le_component)))
  exact ⟨e.trans (MulEquiv.subgroupCongr (higher_kernel_split D A C hd).symm),he⟩

/-- The second literal centralizer decomposition in (*) for d=4,5. -/
theorem higher_centralizer_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  centralizer_split_of_kernel_split h D structural A C hnone (higher_kernel_split D A C hd)

/-- Both decompositions in (*) use the original multiplication maps. -/
theorem higher_centralizer_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    ∃ e : U × ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (U : Set G)),
      ∀ u z, (e (u,z) : G) = (u : G) * (z : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) (core_disjoint_component_centralizer D A C)
    (le_centralizer_iff.mp (component_centralizer_le_core_centralizer D A C))
  exact ⟨e.trans (MulEquiv.subgroupCongr (higher_centralizer_split h D structural A C hnone hd).symm),he⟩

/-- The two elementary central factors have the same order, as used in the
source's subsequent rank bound. No order-two bound is assumed. -/
theorem higher_central_factors_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) =
      Nat.card ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  obtain ⟨e,_⟩ := higher_centralizer_directProduct h D structural A C hnone hd
  obtain ⟨f,_⟩ := chosen_centralizer_core_directProduct h D structural A C hnone
  have hc := Nat.card_congr (e.trans f.symm).toEquiv
  rw [Nat.card_prod, Nat.card_prod] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- The hyperplane centralizer in the higher-dimensional branch, with the
literal pair centralizer required by the public record. -/
theorem higher_hyperplane_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      U ⊔ V ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  rw [hyperplane_centralizer_eq_core_sup_kernel h D structural A C, higher_kernel_split D A C hd,
    ← sup_left_comm, ← higher_centralizer_split h D structural A C hnone hd,
    C.sylow_centralizer_core_decomposition (by omega)
      (((structural G T L h).2.2 V D).1) D.le_sylow hnone,
    sup_left_comm, ← sup_assoc]

/-- The source Sylow product over C_T(L), in dimensions four and five. -/
theorem higher_sylow_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 4 ≤ d) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have he := sylow_split_over_kernel h D structural A
  rw [higher_kernel_split D A C hd, ← sup_assoc,
    sup_eq_left.mpr (le_inf D.le_sylow D.le_component)] at he
  exact he

/-- The component's Sylow centralizer is central in T, after the literal
kernel split. Elementarity of R supplies its own internal commutativity. -/
theorem higher_component_centralizer_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ centralizer (T : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary h D structural A C hnone
  have hZR : Z ≤ R := le_inf inf_le_left (component_centralizer_le_core_centralizer D A C)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hZR
  apply le_centralizer_iff.mp
  conv_lhs => rw [higher_sylow_split h D structural A C hd]
  exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le inf_le_right)))
    (le_centralizer Z)

/-- The second central factor is central in T as well: its T-commutator
lies both in U and in the disjoint factor C_T(I). -/
theorem higher_pair_centralizer_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) ≤ centralizer (T : Set G) := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZU := component_centralizer_le_core_centralizer D A C
  have hZT := higher_component_centralizer_central h D structural A C hnone hd
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
      ← higher_centralizer_split h D structural A C hnone hd]
    exact hER hx
  obtain ⟨u,hu,z,hz,rfl⟩ := hprod
  have hc : ⁅z,t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZT hz t ht).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hc, mul_one, mul_inv_cancel, one_mul]
  exact (le_normalizer_iff_commutator_le_left.mp C.sylow_normalizes_core)
    (commutator_mem_commutator hu ht)

/-- The hyperplane-centralizer product is internal: the stated map is
multiplication in G, and its two factors have trivial intersection. -/
theorem higher_hyperplane_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 4 ≤ d) :
    ∃ e : ↥(U ⊔ V) × ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)),
      ∀ x z, (e (x,z) : G) = (x : G) * (z : G) := by
  let := C.elementary
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hEU : E ≤ centralizer (U : Set G) := inf_le_right.trans
    (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left))
  have hEV : E ≤ centralizer (V : Set G) := inf_le_right.trans
    (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right))
  have hsplit : (U ⊔ V) ⊓ centralizer (U : Set G) = U := by
    rw [inf_centralizer_sup_of_centralizing U V U
      (C.core_le_sylow.trans (((structural G T L h).2.2 V D).1)) (le_centralizer U),
      chosen_centralizer_core A C, sup_eq_left.mpr inf_le_left]
  have hdis : Disjoint (U ⊔ V) E := by
    apply disjoint_def.mpr
    intro x hx hxE
    exact disjoint_def.mp C.core_disjoint_sylow_pair_centralizer
      (hsplit.le ⟨hx,hEU hxE⟩) hxE
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (U ⊔ V) E hdis
    (sup_le (le_centralizer_iff.mp hEU) (le_centralizer_iff.mp hEV))
  exact ⟨e.trans (MulEquiv.subgroupCongr (higher_hyperplane_centralizer h D structural A C hnone hd).symm),he⟩

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
