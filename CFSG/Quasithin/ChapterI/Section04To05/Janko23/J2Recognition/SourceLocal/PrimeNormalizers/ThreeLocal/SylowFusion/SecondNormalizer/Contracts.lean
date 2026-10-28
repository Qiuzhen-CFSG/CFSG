module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Contracts

/-!
# The two branches of the second cubic centralizer calculation

For a cubic element of the actual selected component E(C_G(t)), the root
four-group lies in its centralizer. The missing recognition calculation is
that this four-group is normal there, or that the full centralizer is
C₃ × A₅. The definitions below describe that intermediate statement; they
assert neither the alternative nor the second-normalizer theorem.

The normality is relative to C_G(⟨y⟩). The component and four-group retain
their literal embeddings in G. We also construct a cubic representative in
that component and verify its source 3B condition for the eventual fusion
assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed pp.261–262.
The cited FGT Exercise 16.6 (second edition, pp.266–267) requires elementary
abelian centralizers for every involution, as well as a noncyclic, nonnormal
Sylow two-subgroup. A calculation for only one involution does not suffice.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The literal centralizer of the cubic subgroup. -/
abbrev cubicCentralizer (y : G) := centralizer (zpowers y : Set G)

/-- Normality is inside the cubic centralizer, not in the ambient simple group. -/
def RootNormal (S : InvolutionGeometry.SelectedGeometry D) (y : G) : Prop :=
  ((InvolutionGeometry.rootCore S.t).subgroupOf (cubicCentralizer y)).Normal

/-- The missing intermediate recognition alternative, before using 47.2
and the first-class centralizer to eliminate the A₅ branch. -/
def CentralizerAlternatives (S : InvolutionGeometry.SelectedGeometry D) : Prop :=
  ∀ y : G, y ∈ InvolutionGeometry.rootComponent S.t → orderOf y = 3 →
    RootNormal S y ∨ Nonempty (cubicCentralizer y ≃*
      (Multiplicative (ZMod 3) × alternatingGroup (Fin 5)))

/-- The selected component lies in its actual involution centralizer. -/
theorem component_le_involutionCentralizer (S : InvolutionGeometry.SelectedGeometry D) :
    InvolutionGeometry.rootComponent S.t ≤ involutionCentralizer S.t :=
  map_subtype_le _

/-- Thus the source root four-group really is a subgroup of C_G(⟨y⟩). -/
theorem rootCore_le_cubicCentralizer (S : InvolutionGeometry.SelectedGeometry D)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) :
    InvolutionGeometry.rootCore S.t ≤ cubicCentralizer y := by
  apply le_centralizer_iff.mp
  apply zpowers_le.mpr
  exact S.model.centralizer_le_core_centralizer
    (component_le_involutionCentralizer S hy)

/-- Cubic elements of the literal component have the source 3B property. -/
theorem threeB_of_mem_component (S : InvolutionGeometry.SelectedGeometry D)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) (hyo : orderOf y = 3) :
    ThreeB D y :=
  ⟨hyo, S.t, S.other.1, S.other.2, mem_centralizer_singleton_iff.mp
    (component_le_involutionCentralizer S hy)⟩

/-- A concrete representative for the normalizer and fusion assembly exists
in E(C_G(t)); no second-normalizer conclusion is needed to choose it. -/
theorem exists_component_three (S : InvolutionGeometry.SelectedGeometry D) :
    ∃ y : G, y ∈ InvolutionGeometry.rootComponent S.t ∧ orderOf y = 3 ∧ ThreeB D y := by
  let K := InvolutionGeometry.rootComponent S.t
  have hK : Nat.card K = 60 := by
    rw [show K = S.model.fiveFactor from S.component_eq,
      InvolutionGeometry.SecondCentralizer.fiveFactor,
      card_map_of_injective S.model.embedding_injective,
      Nat.card_congr (prodEquiv (⊥ : Subgroup InvolutionGeometry.E4)
        (⊤ : Subgroup InvolutionGeometry.A5)).toEquiv,
      Nat.card_prod, card_bot, card_top, one_mul, InvolutionGeometry.card_A5]
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hK]; norm_num)
  have hyo : orderOf (y : G) = 3 := (orderOf_coe y).trans hy
  exact ⟨y, y.property, hyo, threeB_of_mem_component S y.property hyo⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
