module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.FullAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Kernel
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Exclusion

/-!
# The surviving cubic action of the full partner

The actual action on E has elementary three-core of order dividing nine.
Triviality would make the reduced action a two-group, contrary to the
original Sylow exchange. Order nine contradicts the actual section kernel
and the ambient three-rank bound. Thus the full partner's three-core has
order three. The remaining source contradiction must exclude this case.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- In the full-partner branch only a cubic three-core can survive. -/
theorem PreparedChosenModule.decomposable_five_full_partner_three_core_card_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      localModule T Mc = thompsonFixed T V →
      let E := thompsonFixed T V
      ∃ hn : Mc ≤ normalizer (E : Set G),
        pCore 2 (internalActionImage Mc E hn) = ⊥ ∧
        IsElementaryAbelian 3 (pCore 3 (internalActionImage Mc E hn)) ∧
        Nat.card (pCore 3 (internalActionImage Mc E hn)) = 3 ∧
        IsPGroup 2 ((internalActionImage Mc E hn) ⧸
          pCore 3 (internalActionImage Mc E hn)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq E
  obtain ⟨hn,he,hdiv,hquot⟩ := h.decomposable_five_full_partner_three_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hUcEq
  let D := internalActionImage Mc E hn
  let R := pCore 3 D
  let : IsElementaryAbelian 3 R := he
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  have hcore : pCore 2 D = ⊥ := by
    have hEMc : E ≤ Mc := by
      rw [show E = localModule T Mc from hUcEq.symm]
      exact localModule_le T hTMc
    have hred : IsPReduced 2 (E.subgroupOf Mc) := by
      rw [show E = localModule T Mc from hUcEq.symm]
      exact localModule_reduced_from_source hG T
        ⟨Chapter1.mem_H_of_isTwoLocal hMcC.1.1,hTMc⟩
    let := hred.normal
    let f₀ := actionHom Mc E hn
    have hk₀ : f₀.ker = centralizer (E.subgroupOf Mc : Set Mc) := by
      rw [show f₀.ker = (centralizer (E : Set G)).subgroupOf Mc from actionHom_ker Mc E hn]
      ext m
      constructor
      · intro hm x hx
        exact Subtype.ext (hm x hx)
      · intro hm x hx
        exact congrArg Mc.subtype (hm ⟨x,hEMc hx⟩ hx)
    let e₀ := (QuotientGroup.quotientMulEquivOfEq hk₀.symm).trans
      (QuotientGroup.quotientKerEquivRange f₀)
    change pCore 2 f₀.range = ⊥
    rw [←pCore_map_iso 2 e₀,hred.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hnot1 : Nat.card R ≠ 1 := by
    intro hc
    have hRbot : R = ⊥ := R.eq_bot_of_card_eq hc
    have htwo : IsPGroup 2 D := by
      have hh : IsPGroup 2 (D ⧸ R) := hquot
      exact hh.of_equiv ((QuotientGroup.quotientMulEquivOfEq hRbot).trans
        QuotientGroup.quotientBot)
    have htop : (⊤ : Subgroup D) ≤ pCore 2 D :=
      le_sSup ⟨inferInstance,htwo.to_subgroup ⊤⟩
    have hcentral : Mc ≤ centralizer (E : Set G) := by
      intro x hx
      have hi : (actionHom Mc E hn).rangeRestrict ⟨x,hx⟩ = 1 :=
        htop.trans hcore.le (mem_top _)
      have hh : (⟨x,hx⟩ : Mc) ∈ (actionHom Mc E hn).ker := congrArg Subtype.val hi
      rwa [actionHom_ker] at hh
    let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
    let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
    let S₀ := (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d s.first).space : Set G)
    have hSne : S₀ ≠ (T : Subgroup G) := by
      intro hh
      have hi := s.stabilizer_index
      change S₀.relIndex (T : Subgroup G) = 2 at hi
      rw [hh,relIndex_self] at hi
      omega
    obtain ⟨t,ht,htout⟩ := SetLike.exists_of_lt
      (lt_of_le_of_ne (show S₀ ≤ (T : Subgroup G) from inf_le_left) hSne)
    have hex : Z₁.map (MulAut.conj t).toMonoidHom = Z₂ :=
      (s.thompson_exchanges t ht (fun hh => htout ⟨ht,hh⟩)).1
    have hle : Z₁ ≤ Z₂ := by
      intro z hz
      have hc : t*z*t⁻¹ = z := by
        rw [←hcentral (hTMc ht) z (show z ∈ E from hz.2),mul_inv_cancel_right]
      rw [←hc]
      exact hex ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hz
    have hbot : Z₁ = ⊥ := bot_unique (by
      intro z hz
      exact s.thompson_disjoint ▸ (show z ∈ Z₁ ⊓ Z₂ from ⟨hz,hle hz⟩))
    have hcZ : Nat.card Z₁ = 4 := s.thompson_card s.first
    rw [hbot,card_bot] at hcZ
    omega
  have hnot9 : Nat.card R ≠ 9 := by
    intro hc
    let H := conjugateSpanBy V (centralizer (E : Set G))
    let K := (commutatorPreimage Mc H E).subgroupOf Mc
    obtain ⟨hKC,hK,hnot⟩ := h.decomposable_five_section_kernel_obstruction
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
    let : K.Normal := hK
    let f₀ := (actionHom Mc E hn).rangeRestrict
    have hf₀ : f₀.ker = (centralizer (E : Set G)).subgroupOf Mc := by
      rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
    have hKf : K ≤ f₀.ker := by
      rw [hf₀]
      exact fun _ hx => (hKC hx).2
    let f := QuotientGroup.lift K f₀ hKf
    have hf : f.ker =
        ((centralizer (E : Set G)).subgroupOf Mc).map (QuotientGroup.mk' K) := by
      rw [QuotientGroup.ker_lift,hf₀]
    have hfnot : ¬HasNormalPComplement 3 f.ker := by
      rw [hf]
      exact hnot
    have hrank : primeRank 3 Mc ≤ 2 :=
      (hG.twoLocal_sqtk hMcC.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
    exact @false_of_cubic_preimage Mc (Mc ⧸ K) D _ _ _ _ _ (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
      hrank f (QuotientGroup.lift_surjective_of_surjective K f₀
        (actionHom Mc E hn).rangeRestrict_surjective hKf) hfnot R he hc
  have hcard : Nat.card R = 3 := by
    change Nat.card R ∣ 9 at hdiv
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 9 = {1,3,9} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  exact ⟨hn,hcore,he,hcard,hquot⟩

end CFSG.Quasithin.Chapter15.Section01
