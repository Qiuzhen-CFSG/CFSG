module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.CentralDiagonal
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionBounds
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Algebra
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Choice
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Recognition

/-!
# Centrality of the selected source diagonal

The selected order-four preimage provides both local nonnesting assertions and
excludes both exceptional centralizer models. The rank input then permits
source (d). In its proper-centralizer branch, the selected diagonal normalizes
an outside conjugate factor. Clause (c) bounds its fixed subgroup by two;
two-group recognition contradicts the already excluded factor models.

The final theorem supplies the geometric choice and both recognition inputs
from their proved constructions. It handles an initial involution in either
factor and retains only the explicit order-two intersection assumption.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the paragraph ending “Thus y ∈ Z(G)”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Source (d) makes the selected diagonal central: clause (c) and two-group
recognition rule out its proper-centralizer alternative. The geometric choice
and the two recognition inputs must still be supplied by their producers. -/
theorem MinimalCounterexample.centralDiagonal_of_choice_of_recognition
    [Finite G] (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (hc : DiagonalChoice A₁ A₂ (g⁻¹ * a * g))
    (hr : DiagonalCentralizerRanks S A₁ A₂) (hf : SmallFixedModel G) :
    CentralDiagonal A₁ A₂ (g⁻¹ * a * g) := by
  let t := g⁻¹ * a * g
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have hs := l.swap_of_outside_transporter m.setup ha ha1 hg ht
  have hmodel := m.not_model_of_intersection_card_two l ha ha1 hg ht hcap
  obtain ⟨u, hu, hu4, hy2, _, k, hk, hnorm⟩ := hc
  let y := u * (t⁻¹ * u * t)
  let K := centralizer ({y} : Set G)
  have hrr := hr m.setup t u hs.1 hs.2 ht2 hcap hmodel hu hu4 hy2
  have hnn := DiagonalConstruction.diagonal_nonnesting m.setup hs.1 hu hu4 hcap
  have hy : y ∈ A₁ ⊔ A₂ := (A₁ ⊔ A₂).mul_mem
    ((le_sup_left : A₁ ≤ A₁ ⊔ A₂) hu)
    ((le_sup_right : A₂ ≤ A₁ ⊔ A₂) (DiagonalConstruction.conjugate_mem hs.1 hu))
  have he : K = ⊤ := by
    rcases l.centralizers y hy hy2 hrr.1 hrr.2 hnn.1 hnn.2
      (fun _ _ => DiagonalConstruction.diagonal_local_not_model m.setup hs.1 hu hu4) with he | he
    · exact he
    · exfalso
      have rule (A : Subgroup G) (hA : A ≤ A₁ ∨ A ≤ A₂) (hAS : A ≤ S)
          (hAr : TwoRankAtLeastTwo A) (hAm : ¬ DihedralOrSemidihedral A)
          (hyN : y ∈ normalizer (conjugate A k : Set G)) : False := by
        let e : A ≃* conjugate A k :=
          A.equivMapOfInjective (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective
        have hp : IsPGroup 2 (conjugate A k) := (S.isPGroup'.to_le hAS).of_equiv e
        have hrk := DiagonalConstruction.rank_of_equiv e hAr
        have hb := DiagonalConstruction.outside_fixed_card l hA hk he
        exact hAm (DiagonalConstruction.model_of_equiv e (hf _ hp hrk y hy2 hyN hb))
      rcases hnorm with hn | hn
      · exact rule A₁ (Or.inl le_rfl) m.setup.left_le m.setup.left_rank hmodel hn.2
      · have hmodel₂ : ¬ DihedralOrSemidihedral A₂ := by
          intro hh
          let e : A₁ ≃* conjugate A₁ t :=
            A₁.equivMapOfInjective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective
          apply hmodel
          apply DiagonalConstruction.model_of_equiv e
          rwa [hs.1]
        exact rule A₂ (Or.inr le_rfl) m.setup.right_le m.setup.right_rank hmodel₂ hn.2
  refine ⟨hs.1, hcap, u, hu, hu4, hy2, ?_⟩
  apply mem_center_iff.mpr
  intro x
  apply mem_centralizer_singleton_iff.mp
  change x ∈ K
  rw [he]
  exact mem_top x

/-- The source central diagonal for an order-two intersection. The rootless
involution and diagonal four supply the order-four preimage; the proved rank
and model-recognition results discharge every premise of the centrality
argument. The initial involution may lie in either factor. -/
theorem MinimalCounterexample.centralDiagonal_of_intersection_card_two
    [Finite G] (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    CentralDiagonal A₁ A₂ (g⁻¹ * a * g) := by
  exact m.centralDiagonal_of_choice_of_recognition l ha ha2 hg ht hcap
    (m.diagonalChoice_of_intersection_card_two l ha ha2 hg ht hcap)
    diagonalCentralizerRanks smallFixedModel

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
