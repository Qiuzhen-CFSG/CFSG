module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.LocalMembers
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThreeCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.Action
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank

/-!
# Large outer PSL₃ families lie over both parabolics

Conjugate an entire family member into a suitable involution centralizer.
An intermediate subgroup K containing C_T(z) satisfies E0 and has the
correct intrinsic Sylow subgroup. If K satisfies the actual E1 or E2
conditions, the central actor z removes one from the quotient rank bound.
The normalizer of weak closure already contains T, so generation by K and T
puts both transported parabolics in the required E-generation subgroup.

The sharp rank bound forces a large outer actor to have rank f+1. The
centralizer geometry then supplies the actual E1/E2 witness, including
generation of the socle together with T. The final theorem discharges both
model inputs, including the binary case. It supplies exactly the outer-family
premise of `LinearThree.isEGenerated_of_inner_and_outer_family_parabolics`;
the inner-family and small-actor branches remain with that assembly. The
SQTK hypothesis is unnecessary for this branch.

Source: Aschbacher--Smith E.1.1--6, printed pp.209--211, and E.1.14(1),
p.214. The latter cites Aschbacher (1982), Lemma 4.7. Neither a point/line
overgroup equal to G nor diagram-preserving extension facts settle the
graph case.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite F] in
private theorem parabolics_le_of_centralizer_calculations
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hcore : pCore 2 G = ⊥)
    (hbound : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      ¬ A ≤ L → Group.rank A ≤ f + 1)
    (hlocal : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → ¬ A ≤ L → Group.rank A = f + 1 →
      HasCentralizerLocalWitness L T A)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥)
    (houter : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → ¬ A ≤ L)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding L e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding L e) ≤ M := by
  obtain ⟨A, hA, hAT, hne⟩ := hex
  have hAO := houter A hA hAT hne
  have hrankA := hbound A (hΩ.1 A hA) hAO
  have heq : Group.rank A = f + 1 := by
    have := hlarge A hA hAT hne
    omega
  obtain ⟨g, z, hBT, hzB, hzL, S, hS, K, hSK, hKC, hcase, hgen⟩ :=
    hlocal A (hΩ.1 A hA) hAT hAO heq
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : B ∈ Ω := hΩ.2 g A hA
  have hrank : Group.rank B ≤ f + 1 :=
    (Group.rank_congr ((MulAut.conj g).subgroupMap A)).symm.le.trans
      hrankA
  have hmem := isEMemberAt_of_centralizer_intermediate hf hcore T B (hΩ.1 B hB)
    hBT hrank z hzB (fun h => hzL (h ▸ L.one_mem)) S hS K hSK hKC hcase
  let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hKM : K ≤ M :=
    (show K ≤ eSubgroup f (T : Subgroup G) B from le_sSup hmem).trans
      ((le_iSup (fun C : {C : Subgroup G // C ∈ Ω ∧ C ≤ (T : Subgroup G)} =>
        eSubgroup f (T : Subgroup G) C.1) ⟨B, hB, hBT⟩).trans le_sup_left)
  have hTM : (T : Subgroup G) ≤ M :=
    (Subgroup.le_normalizer.trans
      (RankOneUpper.normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans
        le_sup_right
  have hLM : L ≤ M := hgen.trans (sup_le hKM hTM)
  have hP (P : Subgroup PSL(3,F)) : P.map (linearThreeEmbedding L e) ≤ M :=
    ((P.map_le_range _).trans_eq (linearThreeEmbedding_range L e)).trans hLM
  exact ⟨hP _, hP _⟩

variable [IsSimpleGroup (generalizedFitting G)]

/-- Consumer of the two independent model calculations. The source's
simple generalized Fitting subgroup supplies the ambient two-core identity
and faithful rank transport; the family argument discharges the desired
parabolic containments once the remaining model premises are proved. -/
theorem parabolics_le_of_model_calculations
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hbound : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      ¬ E ≤ MulAut.innerSubgroup PSL(3,F) → Group.rank E ≤ f + 1)
    (hlocal : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → ¬ A ≤ generalizedFitting G → Group.rank A = f + 1 →
      HasCentralizerLocalWitness (generalizedFitting G) T A)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥)
    (houter : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      ¬ A ≤ generalizedFitting G)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M :=
  parabolics_le_of_centralizer_calculations _ e T hf (twoCore_eq_bot e T hLT)
    (outer_rank_le_of_model_bound e hbound) hlocal Ω hΩ hex houter hlarge

/-- In the binary branch the rank premise is fully discharged, including
outer four-groups. Only the actual centralizer local calculation remains. -/
theorem parabolics_le_of_card_two_and_centralizer_calculations
    (e : generalizedFitting G ≃* PSL(3,F)) (hF : Nat.card F = 2)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hlocal : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → ¬ A ≤ generalizedFitting G → Group.rank A = 2 →
      HasCentralizerLocalWitness (generalizedFitting G) T A)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥)
    (houter : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      ¬ A ≤ generalizedFitting G)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A) :
    let M := eFamilySubgroup 1 (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M :=
  parabolics_le_of_centralizer_calculations _ e T (by decide) (twoCore_eq_bot e T hLT)
    (fun A hA _ => rank_le_two_of_card_two e hF A hA) hlocal Ω hΩ hex houter hlarge

/-- The large outer-family branch of E.1.14(1) for PSL₃(2ᶠ). The sharp
outer rank bound and the actual centralizer E1/E2 witnesses discharge all
model premises, including f = 1. This has the literal parabolic embeddings
and weak-closure normalizer required by the upper E-generation assembly. -/
theorem parabolics_le_of_large_outer_family
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ (T : Subgroup G))
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥)
    (houter : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      ¬ A ≤ generalizedFitting G)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M :=
  parabolics_le_of_model_calculations e T hf hLT
    (Matrix.PSL3Even.OuterElementaryRank.rank_le_of_not_le_inner hf hF)
    (hasCentralizerLocalWitness_of_exact_rank e T hf hF hLT hUT)
    Ω hΩ hex houter hlarge

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
