module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartner
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFixedAction

/-!
# No order-eight module for the actual quintic partner

The literal partner's order-eight module would make every fourth power in
its original intersection with M centralize that module. Source ordering
and reducedness then make the entire partner action trivial. The original
Sylow exchange cannot fix the nontrivial intersection with a marked plane,
so the partner module has order two, order four, or is all of E.

The internal import deliberately reuses the frozen order-eight calculation
and reduced-action helpers from the same proof package. It avoids copying
those proofs or changing the frozen public boundary. No private declaration
occurs in the new public theorem's statement.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original quintic partner has a line, a four-group, or the whole
sixteen-element Thompson fixed subgroup as its own local module. -/
theorem PreparedChosenModule.decomposable_five_partner_card_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 ∨ Nat.card (localModule T Mc) = 4 ∨
        localModule T Mc = thompsonFixed T V := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  let W := localModule T Mc
  let H := M⊓Mc
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hnE,hWE⟩ := h.decomposable_five_partner_control hG T hempty hM hmany hJ hu
    hfull c d hd s π hp hs hdec hq hfive
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc∈maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  have hex : ∃t∈(T : Subgroup G), Z₁.map (MulAut.conj t).toMonoidHom=Z₂ := by
    let S₀ := (T : Subgroup G)⊓normalizer (plane V (c.ambientFactor d s.first).space : Set G)
    have hne : S₀≠(T : Subgroup G) := by
      intro he
      have hi := s.stabilizer_index
      change S₀.relIndex (T : Subgroup G)=2 at hi
      rw [he,relIndex_self] at hi
      omega
    obtain ⟨t,ht,htn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne
      (show S₀≤(T : Subgroup G) from inf_le_left) hne)
    exact ⟨t,ht,(s.thompson_exchanges t ht (fun hh => htn ⟨ht,hh⟩)).1⟩
  obtain ⟨t,ht,hext⟩ := hex
  have hfirst : ∀g∈H, Z₁.map (MulAut.conj g).toMonoidHom=Z₁ ∨
      Z₁.map (MulAut.conj g).toMonoidHom=Z₂ := by
    intro g hg
    let x : M := ⟨g,hg.1⟩
    have he : E.map (MulAut.conj g).toMonoidHom=E :=
      mem_normalizer_iff_map_conj_eq.mp (hnE hg)
    have hh : Z₁.map (MulAut.conj g).toMonoidHom=
        thompsonPlane T V
          (c.ambientFactor d (π ((actionHom M V h.normalized).rangeRestrict x) s.first)).space := by
      change ((plane _ _)⊓E).map _=(plane _ _)⊓E
      rw [map_inf _ _ _ (MulAut.conj g).injective,he,plane_conjugate h.normalized _ x]
      exact congrArg (fun P => plane V P⊓E)
        (hs ((actionHom M V h.normalized).rangeRestrict x) s.first)
    rcases s.covers (π ((actionHom M V h.normalized).rangeRestrict x) s.first) with hi | hi
    · exact Or.inl (hh.trans (congrArg (fun k => thompsonPlane T V
        (c.ambientFactor d k).space) hi))
    · exact Or.inr (hh.trans (congrArg (fun k => thompsonPlane T V
        (c.ambientFactor d k).space) hi))
  have hperm := pair_permutation_of_conjugate_orbit H Z₁ Z₂ hfirst t ⟨hM.1.2 ht,hTMc ht⟩ hext
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWE
  have hnW : Mc ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnot8 : Nat.card W ≠ 8 := by
    intro hcW
    have hfour := eight_action_fourth H E Z₁ Z₂ W s.thompson_split
      (disjoint_iff.mpr s.thompson_disjoint) (s.thompson_card s.first)
      (s.thompson_card s.second) s.fixed_card hWE hcW
      (inf_le_right.trans hnW) hperm t ⟨hM.1.2 ht,hTMc ht⟩ hext
    have htwo := local_action_two_of_fourth_intersection hG T hempty hM hJ hMc hfour
    have hcore := maximal_local_action_twoCore hG T hMc
    have htop : (⊤ : Subgroup (internalActionImage Mc W hnW)) ≤ pCore 2 _ :=
      le_sSup ⟨inferInstance,htwo.of_injective (⊤ : Subgroup _).subtype
        (Subgroup.subtype_injective _)⟩
    have hcentral : Mc ≤ centralizer (W : Set G) := by
      intro x hx
      have hi : (actionHom Mc W hnW).rangeRestrict ⟨x,hx⟩ = 1 :=
        htop.trans hcore.le (mem_top _)
      have hh : (⟨x,hx⟩ : Mc) ∈ (actionHom Mc W hnW).ker := congrArg Subtype.val hi
      rwa [actionHom_ker] at hh
    have hbot : W ⊓ Z₁ = ⊥ := by
      apply bot_unique
      intro z hz
      have htz : t*z*t⁻¹ = z := by
        rw [←hcentral (hTMc ht) z hz.1,mul_inv_cancel_right]
      have hz₂ : z ∈ Z₂ := by
        rw [←htz]
        exact hext ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hz.2
      exact (disjoint_iff.mp (disjoint_iff.mpr s.thompson_disjoint)).le ⟨hz.2,hz₂⟩
    have hc := (eight_intersections E Z₁ Z₂ W s.thompson_split
      (disjoint_iff.mpr s.thompson_disjoint) (s.thompson_card s.first)
      (s.thompson_card s.second) s.fixed_card hWE hcW t (hnW (hTMc ht)) hext).1
    rw [hbot,card_bot] at hc
    omega
  have hdiv : Nat.card W ∣ 16 := s.fixed_card ▸ card_dvd_of_le hWE
  have hWne : W ≠ ⊥ := by
    intro hb
    exact centralInvolutions_ne_bot_of_maximal_local T hMc
      (bot_unique ((le_conjugateSpanBy (centralInvolutions T) Mc).trans_eq hb))
  have hcases : Nat.card W = 2 ∨ Nat.card W = 4 ∨ Nat.card W = 16 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 16 = {1,2,4,8,16} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    have hlo := W.one_lt_card_iff_ne_bot.mpr hWne
    omega
  rcases hcases with hc | hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (eq_of_le_of_card_ge hWE (by rw [hc,s.fixed_card])))

end CFSG.Quasithin.Chapter15.Section01
