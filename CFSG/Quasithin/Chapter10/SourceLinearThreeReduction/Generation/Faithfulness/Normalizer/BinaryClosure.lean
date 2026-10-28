module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryExclusions
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Closing the binary model branches for the actual odd normalizer

For a normal component in a shared Theorem C model, the proved outer
solvability theorem makes the original perfect residual act innerly.
The original covering-uniqueness subgroup then places that residual in
the component. The literal quotient geometry excludes PSL₃, Sp₄, G₂
and triality without additional action or local-rank inputs.

The Hall-kernel application retains exactly module fixation and covering
uniqueness, which are still owed by qt-d-10-nona5-hall-faithfulness.
This closes these model branches, not the full 4.4.3 theorem.
Source: Aschbacher--Smith 4.4.10--12, pp.621--622, and 10.2.3(2), p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hu : UniqueMaximalOvergroup
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hBC hodd hBV hu hK hout

/-- Actual Theorem C models discharge the outer-action premise in component placement. -/
theorem source_nonnormal_oddNormalizer_residual_le_of_theoremC
    (hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC
      (Group.IsPerfect.not_isMulCommutative _) hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) :=
    le_trans le_top le_normalizer_of_normal
  have hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))) :=
    le_trans le_top le_normalizer_of_normal
  exact (source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    D hn B hBC hodd hBV hu K hK hout hYK
      (source_oddNormalizer_component_inner B K hK hFK)).2.2.2

/-- The linear-three model supplies its own outer action and is excluded. -/
theorem source_nonnormal_oddNormalizer_no_psl3_component
    {E : Type} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) E) : False := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨n,_,hcard⟩ := FiniteField.card E 2
  have hE : Nat.card E = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K) :=
    .rank_two n (.linear n.pos ⟨E,inferInstance,inferInstance,hE,⟨a⟩⟩)
  exact source_nonnormal_oddNormalizer_no_placed_psl3_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout hm) a

/-- The large binary symplectic-four model supplies its own outer action and is excluded. -/
theorem source_nonnormal_oddNormalizer_no_sp4_component
    {E : Type} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (a : K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp E) : False := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨n,_,hcard⟩ := FiniteField.card E 2
  have hc : Nat.card E = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra! hn2
    have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
    simp only [hn1,pow_one] at hc
    omega
  have hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K) :=
    .rank_two n (.symplectic hn2 ⟨E,inferInstance,inferInstance,hc,
      ⟨a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩)
  exact source_nonnormal_oddNormalizer_no_placed_sp4_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout hm) a

/-- The large binary G₂ model supplies its own outer action and is excluded. -/
theorem source_nonnormal_oddNormalizer_no_g2_component
    {E : Type} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (a : K ⧸ center K ≃* Atlas.G2.Model E) : False := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨n,_,hcard⟩ := FiniteField.card E 2
  have hc : Nat.card E = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra! hn2
    have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
    simp only [hn1,pow_one] at hc
    omega
  have hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K) :=
    .rank_two n (.g2 hn2 ⟨E,inferInstance,inferInstance,hc,⟨a⟩⟩)
  exact source_nonnormal_oddNormalizer_no_placed_g2_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout hm) hE a

/-- The binary triality model supplies its own outer action and is excluded. -/
theorem source_nonnormal_oddNormalizer_no_triality_component
    (n : ℕ) (hn' : 0 < n)
    (a : K ⧸ center K ≃* Triality.Standard.Carrier
      (Triality.Standard.binaryParameters n hn')) : False := by
  have hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K) :=
    .rank_two n (.triality hn' ((Triality.Standard.isTrialityGroupAt_binary_iff _ n hn').mpr ⟨a⟩))
  exact source_nonnormal_oddNormalizer_no_placed_triality_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout hm) n hn' a

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The selected elementary subgroup of the literal Hall kernel cannot
have a binary linear-three normalizer component. Module fixation and
covering uniqueness are the two retained earlier source premises. -/
theorem source_hall_kernel_no_psl3_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H)
    (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) E) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_psl3_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) hu K hK hout a

end CFSG.Quasithin.Chapter10
