module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedMathieu
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddG2
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Removing M₂₄ from the original binary-three placed branch

The same odd-actor residual and the whole marked natural--dual orbit map into
the original component. Its full centralizer is the odd core, so its entire
center has odd order. Projection through that center is therefore injective
on the whole elementary orbit. The native Mathieu normalizer exclusion now
applies to the literal residual action, with no new local or module premise.

The remaining placed models are PSL₅(2), PSp₆(2), J₄, He and Ru. The original
component, movement, outside condition, zero two-core, full centralizer and
residual section are all retained. The H-star application also retains the
separate maximal pushing-up alternative. Odd-normalizer control, global-w
control and the doubled-branch contradiction still require those remaining
arguments.
Source: Aschbacher--Smith 4.4.12 and the following local inspection, printed
pp.622--623, as used by 7.3.4 and 7.6.1, pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original placed component has no Mathieu central quotient. The full
center is retained; its odd order makes the whole orbit inject into the quotient. -/
theorem sourceOrbit_binary_oddNormalizer_not_mathieu
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G))) :
    ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) := by
  rintro ⟨m⟩
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  let W := D.sourceOrbit
  let a : K.map N.subtype ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let i : R →* K := a.toMonoidHom.comp (inclusion hr)
  have hi : Function.Injective i := a.injective.comp (inclusion_injective hr)
  obtain ⟨_,_,hWR,t,ht,hnt,q,hq,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  have hWR' : W ≤ R := hWR.trans (pCoreIn_le 2 R)
  let iW : W →* K := i.comp (inclusion hWR')
  have hiW : Function.Injective iW := hi.comp (inclusion_injective hWR')
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  let π := QuotientGroup.mk' (center K)
  have hπ : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hoZ.coprime_two_left
  have hp : IsPGroup 2 iW.range := (IsElementaryAbelian.isPGroup 2 W).of_surjective
    iW.rangeRestrict iW.rangeRestrict_surjective
  have hiπ : Function.Injective (π.comp iW) := by
    have hh := injective_comp_subtype_of_coprime_ker π hπ iW.range hp
    intro x y he
    apply hiW
    exact congrArg Subtype.val (hh (show (π.comp iW.range.subtype) (iW.rangeRestrict x) =
      (π.comp iW.range.subtype) (iW.rangeRestrict y) from he))
  let v : Multiplicative NaturalDual.Space ≃* W :=
    E.symm.toAddEquiv.toMultiplicative.trans (MulEquiv.toMultiplicative_toAdditive)
  let f := m.toMonoidHom.comp (π.comp i)
  let j := m.toMonoidHom.comp ((π.comp iW).comp v.toMonoidHom)
  have hj : Function.Injective j := m.injective.comp (hiπ.comp v.injective)
  let qR := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hqR : Function.Surjective qR := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : _root_.Group.IsPerfect R := oddActorResidual_isPerfect L A
  apply DoubledBinaryPlacedMathieu.no_mathieu_natural_dual f qR hqR j hj
  intro r x
  have hact : doubledSeedAction R W
      (((oddActorResidual_le L A).trans inf_le_left).trans
        D.sourceOrbit_component_normalizes) r (E.symm x) =
      E.symm (NaturalDual.action (qR r) x) := by
    apply E.injective
    rw [hE,E.apply_symm_apply,E.apply_symm_apply]
    rfl
  have hh : r * inclusion hWR' (v (Multiplicative.ofAdd x)) * r⁻¹ =
      inclusion hWR' (v (Multiplicative.ofAdd (NaturalDual.action (qR r) x))) :=
    Subtype.ext (congrArg (fun w : Additive W => (w.toMul : G)) hact)
  have hf := congrArg f hh
  simp only [map_mul,map_inv] at hf
  exact hf

/-- The same original placed component, with the Mathieu row removed. -/
@[expose] def BinaryPlacedNonMathieuCase (A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p)) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (p^2)) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2))) ∧
    (K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧
      ¬ ChapterA.Section02.IsTheoremBOddModel (K ⧸ center K) ∧
      DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) ∧
      (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
        ClassicalGroup.IsPSp (K ⧸ center K) 3 2 ∨
        ∃ name : ClassificationModels.SporadicName,
          (name = .j4 ∨ name = .he ∨ name = .ru) ∧
          Nonempty ((K ⧸ center K) ≃* name.Carrier)) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f)

private theorem binary_placed_nonMathieu_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hc : D.BinaryPlacedOnlyCase A) :
    D.BinaryPlacedNonMathieuCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hR,hC,hrank,hodd,hl,hrem,hfour,j,hj,f,hf⟩ := hc
  refine ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hR,hC,hrank,hodd,hl,?_,hfour,j,hj,f,hf⟩
  cases hrem with
  | linear_five he => exact Or.inl he
  | symplectic_six he => exact Or.inr (Or.inl he)
  | sporadic name hrow he =>
    rcases hrow with hrow | hrow
    · subst name
      exact (D.sourceOrbit_binary_oddNormalizer_not_mathieu h hd F hF hmodel
        A hAC ho K hR hC he).elim
    · exact Or.inr (Or.inr ⟨name,hrow,he⟩)

/-- The original odd-normalizer component has one of five remaining models.
The full residual and center quotient are retained without a new premise. -/
theorem sourceOrbit_binary_oddNormalizer_placed_nonMathieu
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryPlacedNonMathieuCase A := by
  exact D.binary_placed_nonMathieu_reduction h hd F hF hmodel A hAC ho
    (D.sourceOrbit_binary_oddNormalizer_placed_only h hd F hF hmodel A hne hAC ho hu hout)

/-- The Mathieu exclusion on the same original H-star actor and component.
The independent maximal pushing-up alternative is retained literally. -/
theorem sourceOrbit_binary_globalW_or_placed_nonMathieu_oddLocal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ChapterE.globalW D.sourceOrbit T ≤ 1 ∨
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        D.BinaryPlacedNonMathieuCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_placed_only_oddLocal h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcase⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcase.imp_right (D.binary_placed_nonMathieu_reduction h hd F hF hmodel A hAC (hcard.symm ▸ hpo))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
