module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddAction
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentPlacement

/-!
# The whole binary orbit in the selected odd-local component

The original residual R = C_L(A)^∞ retains its literal SL₃(2) quotient.
Either its action is inner or its outer image has that actual simple
section. In the inner case, original residual uniqueness places R and
the whole orbit W in one normal component K of N_G(A). Its centralizer
is exactly O(N_G(A)); hence the odd center loses none of W's rank six.
The central quotient retains an actual SL₃(2) section via the residual,
with a two-group kernel. Neither W = V nor center-freeness is assumed.

The shared C, alternating and odd PSL₂ outer calculations discharge
those outer cases. Both branches exclude all odd PSL₂ and prime-field
PSL₃/PSU₃ component models. The final application retains the original
H-star prime-order witness when w > 1. Its pushing-up branch, remaining
outer models, and the placed rank-six component still require exclusion;
this is not the full 4.4.3 or the binary Baer–Suzuki conclusion.

Source: Aschbacher–Smith 4.4.10–12, printed pp.621–622, used by 7.3.4
and 7.6.1, printed pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original fixed residual either acts inner or supplies an actual
binary-three section in the outer group of this same component. -/
theorem sourceOrbit_binary_odd_residual_inner_or_outer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) ∨
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f := by
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  have hRN : R ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let a : R.subgroupOf N ≃* R := subgroupOfEquivOfLe hRN
  obtain ⟨_,_,_,t,ht,hnt,q,hq,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 R)).comp a.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp a.surjective)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ←MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective a.toMonoidHom a.injective
  let : _root_.Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : _root_.Group.IsPerfect (R.subgroupOf N) := _root_.Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  have hAN := hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf hAN hAC
  obtain ⟨_,hRK,_⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A hAN ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    (hAC.trans (centralizer_le (by rw [D.sourceOrbit_eq]; exact le_componentOrbit V T))) K hK
  exact DoubledBinaryOddPlacement.inner_or_outer_section K (R.subgroupOf N) f hf hk hRK

/-- In the inner branch the normal component contains the whole order-64
orbit and the original residual. Its full central quotient has two-rank
at least six, and the component centralizer is exactly the odd core. -/
theorem sourceOrbit_binary_oddNormalizer_inner_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hi : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G)))) :
    K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) := by
  have hs : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L := by
    let := h.quasisimple
    apply relative_module_centralizer_le_sectionCentralizer L V D.normalizes _ D.ne_bot D.eq_commutator
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨hn,hv,hr,hcent⟩ := normal_component_of_inner_action h.toHypothesis1221 D hs
    A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) hu hout K hK houtK hi
  have hw : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype :=
    ((D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho).2.2.1.trans
      (pCoreIn_le 2 _)).trans hr
  let N := normalizer (A : Set G)
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  have hrK : primeRank 2 D.sourceOrbit ≤ primeRank 2 K := by
    have hh := primeRank_mono 2 hw
    rwa [←primeRank_equiv 2 (K.equivMapOfInjective N.subtype N.subtype_injective)] at hh
  have hrQ := hrK.trans (primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center K)) (by
    rw [QuotientGroup.ker_mk']; exact hoZ.coprime_two_left))
  have hc : Nat.card D.sourceOrbit = 2^6 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_binary_dimension h hd F hF hmodel] at hh
    exact hh
  have he := IsElementaryAbelian.log_card_eq_primeRank (p := 2) D.sourceOrbit
  rw [hc,Nat.log_pow (by decide : 1 < (2 : ℕ))] at he
  exact ⟨hn,hw,hr,hcent,he ▸ hrQ⟩

/-- The original fixed residual gives a literal binary-three section in
the containing component's central quotient, with its two-kernel retained. -/
theorem sourceOrbit_binary_oddNormalizer_component_section
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    ∃ j : oddActorResidual L A →* K ⧸ center K,
      IsPGroup 2 j.ker ∧
      ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f := by
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  let a : K.map N.subtype ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let i : R →* K := a.toMonoidHom.comp (inclusion hr)
  have hi : Function.Injective i := a.injective.comp (inclusion_injective hr)
  obtain ⟨_,_,_,t,ht,hnt,q,hq,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  let j := (QuotientGroup.mk' (center K)).comp i
  have hk := DoubledBinaryOddPlacement.central_kernel_le_twoCore e i hi
  let b := QuotientGroup.quotientKerEquivRange j
  let f : j.range →* BinaryLinearThree.Group := e.toMonoidHom.comp
    ((QuotientGroup.map j.ker (pCore 2 R) (MonoidHom.id R) hk).comp b.symm.toMonoidHom)
  refine ⟨j,pCore_isPGroup.to_le hk,f,?_⟩
  intro g
  obtain ⟨r,hrg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) g
  refine ⟨j.rangeRestrict r,?_⟩
  have hb : b.symm (j.rangeRestrict r) = QuotientGroup.mk' j.ker r :=
    b.injective (by rw [b.apply_symm_apply]; rfl)
  change e (QuotientGroup.map j.ker (pCore 2 R) (MonoidHom.id R) hk
    (b.symm (j.rangeRestrict r))) = g
  rw [hb]
  exact hrg

/-- Output on the actual odd normalizer: the full orbit is placed in a
normal component, or the literal outer section escapes all completed shared
C, alternating and odd linear-two rows. -/
@[expose] def BinaryOddComponentCase (A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p)) ∧
    ((K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f) ∨
     ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) ∧
       ¬ ChapterA.Section02.IsTheoremCModel (K ⧸ center K) ∧
       (∀ n : ℕ, ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) ∧
       ∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q))

/-- Original chosen-module application of the component placement, rank
and outer-section exclusions; no model or inner-action callback is added. -/
theorem sourceOrbit_binary_oddNormalizer_component_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryOddComponentCase A := by
  obtain ⟨K,hK,hm,houtK,hcore,hqt,hknown,hRK,hWK⟩ :=
    D.sourceOrbit_binary_oddNormalizer_component h hd F hF hmodel A hne hAC ho hu hout
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
    ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  have hb := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
  refine ⟨K,hK,hm,houtK,hcore,hb,?_⟩
  rcases D.sourceOrbit_binary_odd_residual_inner_or_outer h hd F hF hmodel A hAC ho K hK with hi | he
  · obtain ⟨hn,hw,hr,hcent,hrank⟩ := D.sourceOrbit_binary_oddNormalizer_inner_placement
      h hd F hF hmodel A hAC ho hu hout K hK houtK hi
    obtain ⟨h2,h3⟩ := DoubledBinaryOddPlacement.small_model_exclusions (Or.inl hrank)
    exact ⟨h2,h3,Or.inl ⟨hn,hw,hr,hcent,hrank,
      D.sourceOrbit_binary_oddNormalizer_component_section h hd F hF hmodel A hAC ho K hr⟩⟩
  · obtain ⟨h2,h3⟩ := DoubledBinaryOddPlacement.small_model_exclusions (Or.inr he)
    exact ⟨h2,h3,Or.inr ⟨he,DoubledBinaryOddPlacement.outer_section_exclusions he⟩⟩

/-- The original H-star witness now reaches the placed component or
an actual outstanding outer section. The pushing-up alternative and every
original prime-order, centralizer and escaping-normalizer condition remain. -/
theorem sourceOrbit_binary_globalW_or_placed_oddLocal
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
        D.BinaryOddComponentCase A) := by
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
    exact D.sourceOrbit_binary_oddNormalizer_component_placement h hd F hF hmodel A hne hAC ho hu
      (fun he => hout (inf_le_right.trans he))
  · apply Or.inl
    have hA : A ≤ normalizer (L : Set G) ⊓
        centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      rw [←D.sourceOrbit_eq]
      exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
    simpa only [←D.sourceOrbit_eq] using D.doubledOrbit_oddNormalizer_pushingUp h A hA ho hu


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
