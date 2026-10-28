module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootImage
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
/-!
# The ordered chi-zero product in the original root-image branch

For the actual opposite pair I and Q₁ = O₂(G₁), the root-image calculation
makes Q₁ a Sylow subgroup of IQ₁ and proves that IQ₁ is SQTK of
characteristic two. Applying the proved known-simple C(G,T) theorem gives
an ordered product of the characteristic-normalizer closure and at most
two actual chi-zero blocks. Each block lies outside that closure and is
moved by the Thompson subgroup of the original Sylow group.

The application preserves the opposite-pair action and the exclusion of
nontrivial characteristic subgroups of Q₁ normalized by I. It does not
assert that a characteristic subgroup exists: eliminating the chi-zero
block alternative remains with qt-d-1222-natural-closure-sp4, as does the
nonbinary rank-two classification in the full-image branch.

Source: Aschbacher--Smith C.1.29, printed p.134, and 11.5.7, printed p.783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
open scoped Pointwise
/-- The C.1.29 ordered-product conclusion, retaining its actual ambient
blocks, their Thompson movement, and all product witnesses. -/
@[expose] def RootChiProduct {H : Type*} [Group H] (S : Sylow 2 H) : Prop :=
  ∃ r : ℕ, r ≤ 2 ∧ ∃ B : Fin r → Subgroup H,
    (∀ i, ChapterC.IsChiZeroBlockIn (B i)) ∧
    (∀ i, ¬B i ≤ (S : Subgroup H).characteristicNormalizerClosure) ∧
    (∀ i, B i = ⁅B i,Stellmacher.elementaryAbelianMaxJ (S : Subgroup H)⁆) ∧
    ∀ z : H, ∃ c : (S : Subgroup H).characteristicNormalizerClosure,
      ∃ b : ∀ i, B i, z = (c : H) * (List.ofFn (fun i => (b i : H))).prod


private theorem rootChiProduct_of_sqtk {H : Type*} [Group H] [Finite H]
    (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hf : generalizedFitting H = pCore 2 H) (S : Sylow 2 H) : RootChiProduct S := by
  unfold RootChiProduct
  exact ChapterC.RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
    hq hf S (S : Subgroup H).characteristicNormalizerClosure le_rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The literal C(G,T) ordered product for IQ₁, with its marked action and original Sylow Q₁. -/
theorem root_case_chi_product_of_preceding (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hne : ¬ IsMulCommutative E.W)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    ∃ (g' : Sp E.input.field.Carrier) (y : L),
      let J : Subgroup G := oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g').toMonoidHom).map (FullAction.modelHom m) ∧
      ∃ S : Sylow 2 J,
        (S : Subgroup J).map J.subtype = E.G₁.pCoreIn 2 ∧
        (∀ C : Subgroup (E.G₁.pCoreIn 2), C.Characteristic → C ≠ ⊥ →
          ¬ oppositeJoin (auxiliaryW E) (y : G) ≤
            normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G)) ∧
        RootChiProduct S := by
  obtain ⟨g',y,hpair,S,hS,hq,hf,hno⟩ := root_case_inputs_of_preceding
    (G := G) (T := T) (L := L) (V := V) (D := D) E m g hpoint hthree
    hX hcartan hn3 hirr hti hgen hVX hfour hfive hout hne hroot
  refine ⟨g',y,hpair,S,hS,hno,?_⟩
  exact rootChiProduct_of_sqtk hq hf S

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
