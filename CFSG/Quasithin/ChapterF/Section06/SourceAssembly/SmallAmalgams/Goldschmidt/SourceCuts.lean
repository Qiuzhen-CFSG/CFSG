module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeResidualSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeSingularityBounds
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.LargeNonabelianReduction

/-!
# Independent source arguments in the large marked amalgam classification

The original finite amalgam supplies a locally finite, possibly infinite,
two-perfect tree action and a least odd singularity index at least five.
The remaining source arguments are canonical-label construction, the radius
restriction, recognition at each radius, and normal-base reconstruction.
The two recognition conclusions retain actual isomorphisms of amalgams,
including the common overlap maps. Their conditional assembly below is not
an assertion that these five source arguments have been proved.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(3.2), (3.7)--(3.8), (4.3)--(4.4), and Sections 5--6, pp.386--406.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupTheory
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open GreenBook
universe u

/-- Only source hypotheses and the least singularity witness. In particular,
this contains no labels, order bound, or model recognition. -/
structure LargeTreeSource {G : Type u} [Group G] (F : Bool → Subgroup G)
    (s : ℕ) : Prop where
  action : TwoPerfectTreeAction F
  not_cubic : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3))
  not_alternating : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4))
  five_le : 5 ≤ s
  odd : Odd s
  regular : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
    k < s → p.Nonbacktracking → RightRegular (A := G) p
  singular : ∃ (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) s v),
    p.Nonbacktracking ∧ ¬ RightRegular (A := G) p

/-- Construct the entire source context from the original large amalgam.
The size bound is on the original overlap, not on the residual overlap. -/
theorem exists_largeTreeSource {G : Type u} [Group G] [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hlarge : 64 ≤ Nat.card (A ⊓ B : Subgroup G)) :
    let F := residualFamily (RankTwoAmalgam.Universal.cosetFamily (inclusionAmalgam A B))
    ∃ s, LargeTreeSource F s := by
  obtain ⟨ht, hC, hAlt⟩ := large_universal_residual_setup h hcore hA hB hlarge
  obtain ⟨s, hs, ho, hr, hn⟩ :=
    ht.toCubicTreeAction.exists_large_odd_singularityIndex_of_large_residual hC hAlt
  exact ⟨s, ht, hC, hAlt, hs, ho, hr, hn⟩

/-- The two-perfect G₄ model, with either original vertex orientation. -/
def DerivedMarkedBase {G : Type u} [Group G] (F : Bool → Subgroup G) : Prop :=
  ExceptionalModels.G2.IsDerivedAmalgam (inclusionAmalgam (F false) (F true)) ∨
    ExceptionalModels.G2.IsDerivedAmalgam (inclusionAmalgam (F true) (F false))

/-- The two-perfect G₅ model, with either original vertex orientation. -/
def MathieuMarkedBase {G : Type u} [Group G] (F : Bool → Subgroup G) : Prop :=
  MathieuTwelve.IsM12Amalgam (inclusionAmalgam (F false) (F true)) ∨
    MathieuTwelve.IsM12Amalgam (inclusionAmalgam (F true) (F false))

/-- The independent geometric construction in (5.3), (6.4)--(6.8). -/
def CanonicalLabelsInput : Prop :=
  ∀ (G : Type u) [Group G] (F : Bool → Subgroup G) (s : ℕ),
    LargeTreeSource F s → Nonempty (CanonicalLabelSetup F s)

/-- The odd-radius argument of (6.11), including its source commutator. -/
def CanonicalRadiusInput : Prop :=
  ∀ (G : Type u) [Group G] (F : Bool → Subgroup G) (s : ℕ),
    LargeTreeSource F s → ∀ d : CanonicalLabelSetup F s,
      d.radius = 2 ∨ d.radius = 3

/-- Compatible recognition of the radius-two source groups in (6.9). -/
def RadiusTwoMarkedInput : Prop :=
  ∀ (G : Type u) [Group G] (F : Bool → Subgroup G) (s : ℕ),
    LargeTreeSource F s → ∀ d : CanonicalLabelSetup F s,
      d.radius = 2 → DerivedMarkedBase F

/-- Compatible recognition of the radius-three source groups in (6.12). -/
def RadiusThreeMarkedInput : Prop :=
  ∀ (G : Type u) [Group G] (F : Bool → Subgroup G) (s : ℕ),
    LargeTreeSource F s → ∀ d : CanonicalLabelSetup F s,
      d.radius = 3 → MathieuMarkedBase F

/-- Recover the original marked extension from its actual universal normal
base, as in (3.2), (3.7)--(3.8). The residual model is an explicit input;
no abstract endpoint types can replace its compatible inclusion maps. -/
def NormalBaseReconstructionInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A B : Subgroup G) (S : Sylow 2 G),
    IsGoldschmidtTriple A B → pCore 2 G = ⊥ →
    generalizedFitting A = pCore 2 A → generalizedFitting B = pCore 2 B →
    A ⊓ B = (S : Subgroup G) → 64 ≤ Nat.card S →
    ¬ IsMulCommutative (pCore 2 A) → ¬ IsMulCommutative (pCore 2 B) →
    let F := residualFamily (RankTwoAmalgam.Universal.cosetFamily (inclusionAmalgam A B))
    DerivedMarkedBase F ∨ MathieuMarkedBase F →
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A

/-- Apply the two independent recognition proofs only after the geometric
radius restriction. All four earlier source arguments remain explicit. -/
theorem marked_base_of_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u})
    {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}
    (h : LargeTreeSource F s) : DerivedMarkedBase F ∨ MathieuMarkedBase F := by
  obtain ⟨d⟩ := labels G F s h
  rcases radius G F s h d with hr | hr
  · exact Or.inl (two G F s h d hr)
  · exact Or.inr (three G F s h d hr)

/-- Actual application to the large F.6 amalgam: construct the universal
normal-base geometry, classify that marked base, and reconstruct the original
pair. This is a conditional assembly, not the source classification theorem. -/
theorem largeNonabelian_of_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u})
    (reconstruct : NormalBaseReconstructionInput.{u}) :
    LargeNonabelianMarkedAmalgamInput.{u} := by
  intro G _ _ A B S h hcore hA hB hS hlarge hnA hnB
  have hcard : 64 ≤ Nat.card (A ⊓ B : Subgroup G) := hS.symm ▸ hlarge
  obtain ⟨s, hs⟩ := exists_largeTreeSource h hcore hA hB hcard
  exact reconstruct G A B S h hcore hA hB hS hlarge hnA hnB
    (marked_base_of_source_cuts labels radius two three hs)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
