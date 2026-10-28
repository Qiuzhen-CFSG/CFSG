module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeld
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedSymplectic

/-!
# Removing Held from the original binary-three placed branch

Oddness of the full component center embeds the entire marked natural--dual
orbit in the central quotient. The actual residual action retains its original
SL₃(2) quotient. Every elementary subgroup of order 64 in Held has a normalizer
of order 138240, prime to seven, excluding this placement without an additional
Sylow-containment or relative-normality premise.

The original H-star application retains J₄ and Ru in the placed branch and the
separate maximal pushing-up alternative. The same component, whole orbit and
literal central quotient and residual maps are preserved. Source: the concluding
inspection in Aschbacher--Smith 4.4.3, printed pp.622--623, as used in 7.3.4 and
7.6.1, printed pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open BinaryLinearThree
private theorem map_conjugate {X Y : Type*} [_root_.Group X] [_root_.Group Y]
    (f : X →* Y) (x y : X) : f (x * y * x⁻¹) = f x * f y * (f x)⁻¹ := by
  simp only [map_mul,map_inv]

universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original component has no Held central quotient. Oddness of its
full center preserves the whole marked natural--dual orbit. -/
theorem sourceOrbit_binary_oddNormalizer_not_held
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
    ¬ Nonempty ((K ⧸ center K) ≃* Held.He) := by
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
  apply DoubledBinaryPlacedHeld.no_held_natural_dual f qR hqR j hj
  · intro r x
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
    rw [map_conjugate] at hf
    exact hf

/-- The remaining placed component with residual uniqueness retained. -/
@[expose] def BinaryPlacedJankoRudvalisCase (A : Subgroup G) : Prop :=
  UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
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
      (∃ name : ClassificationModels.SporadicName,
          (name = .j4 ∨ name = .ru) ∧
          Nonempty ((K ⧸ center K) ≃* name.Carrier)) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f)

private theorem binary_placed_jankoRudvalis_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hc : D.BinaryPlacedSporadicCase A) : D.BinaryPlacedJankoRudvalisCase A := by
  obtain ⟨_,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hR,hC,hrank,hodd,hl,hrem,hfour,j,hj,f,hf⟩ := hc
  refine ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hR,hC,hrank,hodd,hl,?_,hfour,j,hj,f,hf⟩
  obtain ⟨name,hn,he⟩ := hrem
  rcases hn with hn | hn | hn
  · exact ⟨name,Or.inl hn,he⟩
  · subst name
    exact (D.sourceOrbit_binary_oddNormalizer_not_held h hd F hF hmodel A hAC ho K hR hC he).elim
  · exact ⟨name,Or.inr hn,he⟩

/-- J₄ and Ru remain in the original placed branch, without a new model premise. -/
theorem sourceOrbit_binary_oddNormalizer_placed_jankoRudvalis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryPlacedJankoRudvalisCase A := by
  exact D.binary_placed_jankoRudvalis_reduction h hd F hF hmodel A hAC ho hu
    (D.sourceOrbit_binary_oddNormalizer_placed_sporadic h hd F hF hmodel A hne hAC ho hu hout)

/-- The Held exclusion on the same original H-star actor and component.
The independent maximal pushing-up alternative is retained literally. -/
theorem sourceOrbit_binary_globalW_or_placed_jankoRudvalis_oddLocal
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
        D.BinaryPlacedJankoRudvalisCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_odd_escape h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,_,p,hp,hpo,A,hAH,hAC,hcard,hout⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  have ho : Odd (Nat.card A) := hcard.symm ▸ hpo
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · apply Or.inr
    let : Fact p.Prime := ⟨hp⟩
    let : IsCyclic A := isCyclic_of_prime_card hcard
    have hne : A ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      have := hp.one_lt
      omega
    exact D.sourceOrbit_binary_oddNormalizer_placed_jankoRudvalis h hd F hF hmodel A hne hAC ho hu
      (fun he => hout (inf_le_right.trans he))
  · apply Or.inl
    have hA : A ≤ normalizer (L : Set G) ⊓
        centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      rw [←D.sourceOrbit_eq]
      exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
    simpa only [←D.sourceOrbit_eq] using D.doubledOrbit_oddNormalizer_pushingUp h A hA ho hu

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
