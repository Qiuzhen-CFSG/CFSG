module
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.NonbinaryNormalForms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Stellmacher.ElementaryAbelianMaxPair

/-!
# Maximum elementary subgroups of a symplectic field extension

A diagram-preserving outer involution has fixed group Sp₄ over the half
field, so its automorphism centralizer has two-rank at most 3(n/2)+1.
An elementary abelian subgroup of order at least q³ therefore lies in
the inner group, including when q=4. In the native Sylow, the square
formula shows that every elementary subgroup lies in one of the two
coordinate wings. These are exactly its maximum elementary subgroups.

The prepared source application transports these assertions through the
faithful whole-middle action before invoking Burnside fusion. No ambient
fusion or recognition is assumed in these native calculations.

Source: Aschbacher–Smith F.4.29(6) and the symplectic proof of F.4.35,
printed pp.289–292 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open SymplecticConjugatePair.Ambient.AutomorphismCentralizers
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The centralizer of a diagram-preserving outer involution has strictly
smaller elementary two-rank than a parabolic radical. -/
theorem outer_involution_centralizer_rank {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : MulAut (Sp F)) (hao : orderOf a=2) (ha : PreservesDiagram a)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    Even n ∧ primeRank 2 (centralizer ({a} : Set (MulAut (Sp F)))) ≤ 3*(n/2)+1 := by
  let := ExceptionalGraph.outer_isCyclic_of_card hF hn
    SemilinearClassification.inner_field_of_preservesDiagram
  obtain ⟨heven,hc⟩ := preserving_outer_normal_form hF (by omega)
    (half_frobenius_cocycle_coboundary hF hn) a hao ha hi
  refine ⟨heven,?_⟩
  have hfixed : primeRank 2 a.fixedSubgroup = 3*(n/2) := by
    rw [fixed_rank_eq_of_isConj hc]
    exact field_fixed_rank hF (by omega) heven
  exact hfixed ▸ centralizer_rank_le_fixed_add_one inner_injective a

/-- Elementary subgroups as large as a parabolic radical contain no outer
involution, including over the four-element field. -/
theorem large_elementary_preserving_is_inner {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (V : Subgroup (MulAut (Sp F))) [IsElementaryAbelian 2 V]
    (hV : ∀ a ∈ V, PreservesDiagram a) (hc : Nat.card F^3 ≤ Nat.card V) :
    V ≤ MulAut.innerSubgroup (Sp F) := by
  intro a ha
  by_contra hi
  have hne : a ≠ 1 := fun hh => hi (hh ▸ one_mem _)
  have hao : orderOf a=2 := by
    apply orderOf_eq_prime
    · exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := V)) (⟨a,ha⟩ : V))
    · exact hne
  obtain ⟨_,hr⟩ := outer_involution_centralizer_rank hF hn a hao (hV a ha) hi
  let C := centralizer ({a} : Set (MulAut (Sp F)))
  have hVC : V ≤ C := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hb ha)
  have he : IsElementaryAbelian 2 (V.subgroupOf C) := IsElementaryAbelian.subgroupOf hVC
  have hcard := (primeRank_le_iff_elementary_card_le C).mp hr (V.subgroupOf C) he
  rw [Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv] at hcard
  have hpow : 2^(3*n) ≤ 2^(3*(n/2)+1) := by
    calc
      _ = Nat.card F^3 := by rw [hF,←pow_mul]; congr 1; omega
      _ ≤ _ := hc.trans hcard
  have hle := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  omega
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder

namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
/-- The two radicals are exactly the maximum elementary subgroups of the
native Sylow, with their original coordinate embeddings. -/
theorem native_max_elementary_pair :
    Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (unipotent (F := F))) =
      {wing false,wing true} := by
  let := wing_elementary (F := F) false
  let := wing_elementary (F := F) true
  apply Stellmacher.maxFamily_eq_pair_of_cover _ _ _ le_top le_top
    ((card_wing false).trans (card_wing true).symm)
  intro V hV
  let := hV.2.1
  apply SubgroupClass.subset_union.mp
  intro x hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx
  rw [element_square,←element_zero,theta,element_eq_iff] at hs
  rcases mul_eq_zero.mp hs.2.2.1 with hb | hv
  · exact Or.inr ((element_mem_wing true _ _ _ _).mpr hb)
  · exact Or.inl ((element_mem_wing false _ _ _ _).mpr hv)
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
