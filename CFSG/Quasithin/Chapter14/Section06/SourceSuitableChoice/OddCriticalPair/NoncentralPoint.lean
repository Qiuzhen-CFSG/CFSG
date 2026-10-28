module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice
public import Theory.GroupTheory.FixedModuloSylowConjugacy

/-!
# The central-point obstruction in the odd critical-pair branch

A suitable vector cannot be conjugate to an element of the original
central line: such a conjugate centralizes an ambient Sylow subgroup,
contrary to original 14.6.3(4). On a separated summand, every nonzero
S-fixed vector is suitable. Relative Sylow conjugacy therefore excludes
a conjugate central point from that summand whenever its fixing group
is Sylow in the factor-preserving subgroup.

This proves the obstruction used to eliminate 14.6.13(2). The original
critical-pair alternatives and their Sylow placement are separate inputs;
this module does not assert their construction.

Source: Aschbacher--Smith 14.6.13 and 14.6.17(1--3), printed pp.1031--1036.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hG hempty hM hunique hmany hcard e hab H hH

/-- The non-two-central conclusion of 14.6.3(4) excludes fusion to the source point. -/
theorem source_suitable_not_isConj_point
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (z : G) (hz : z ∈ centralInvolutions T) : ¬ IsConj u z := by
  have hn := (source_suitable_normalizer_of_local_normalizer
    hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3).2.2
  exact fun hc => hn (exists_sylow_le_centralizer_of_isConj T u z
    (centralInvolutions_le_centralizer_sylow T hz) hc)

variable (K W S : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
      K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    (hfixedFree : ∀ u ∈ W, (∀ k ∈ K, ⁅u,k⁆ ∈ centralInvolutions T) →
      u ∈ centralInvolutions T)

include hK hWU hZW hKW hST hindex hU3 hseparate hfixedFree

/-- Every nonzero S-fixed vector in the original first summand avoids point fusion. -/
theorem source_separated_support_not_isConj_point
    (u : G) (hu : u ∈ W) (huz : u ∉ centralInvolutions T)
    (hfixed : ∀ s ∈ S, ⁅u,s⁆ ∈ centralInvolutions T)
    (z : G) (hz : z ∈ centralInvolutions T) : ¬ IsConj u z := by
  have hmoved : ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T := by
    by_contra! hc
    exact huz (hfixedFree u hu hc)
  obtain ⟨heq,hm,hp,_⟩ := source_suitable_of_separated_support
    hG T hempty hM hunique hmany hcard e hab H hH
      K W S hK hWU hZW hKW hST hindex hU3 hseparate u hu hfixed hmoved
  apply source_suitable_not_isConj_point hG T hempty hM hunique hmany hcard e hab H hH
    u (hWU hu) (by rwa [heq]) hm hp (by rwa [heq]) z hz

/-- The rank-eight contradiction after the literal starred-actor Sylow placement.
The conjugate vector and its S-fixedness are constructed, not assumed. -/
theorem source_critical_point_not_le_support_of_sylow
    (H0 Q : Subgroup G) (hH0H : H0 ≤ H)
    (hH0W : H0 ≤ normalizer (W : Set G))
    (hS : Chapter1.IsSylowIn 2 S H0) (hQ : Chapter1.IsSylowIn 2 Q H0)
    (g : G) (houtside : g ∉ Mc)
    (hpointFixed : ∀ w ∈ (centralInvolutions T).map (MulAut.conj g).toMonoidHom,
      ∀ q ∈ Q, ⁅w,q⁆ ∈ centralInvolutions T) :
    ¬ (centralInvolutions T).map (MulAut.conj g).toMonoidHom ≤ W := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hZcard := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,_⟩ :=
    plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZcard
  have hne : (centralInvolutions T).map (MulAut.conj g).toMonoidHom ≠
      centralInvolutions T := by
    intro he
    apply houtside
    rw [hMc]
    exact normalizer_le_centralizer_of_card_two _ hZcard
      (mem_normalizer_iff_map_conj_eq.mpr he)
  have hnot : ¬ (centralInvolutions T).map (MulAut.conj g).toMonoidHom ≤
      centralInvolutions T := by
    intro hl
    apply hne
    apply eq_of_le_of_card_ge hl
    rw [card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨w,hw,hwz⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q',hQ'⟩ := hQ
  have hH0Z : H0 ≤ normalizer (centralInvolutions T : Set G) :=
    hH0H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨k,hk,hfixed⟩ := exists_relative_sylow_fixed_conjugate
    H0 P Q' (centralInvolutions T) hH0Z w (by
      rw [hQ']; exact hpointFixed w hw)
  rw [hP] at hfixed
  intro hle
  have hkW : (MulAut.conj k) w ∈ W := (hH0W hk w).mp (hle hw)
  have hkz : (MulAut.conj k) w ∉ centralInvolutions T :=
    fun hc => hwz ((hH0Z hk w).mpr hc)
  obtain ⟨z,hz,he⟩ := mem_map.mp hw
  have hconj : IsConj ((MulAut.conj k) w) z := by
    have hkconj : IsConj ((MulAut.conj k) w) w :=
      isConj_iff.mpr ⟨k⁻¹,by simp [MulAut.conj_apply, mul_assoc]⟩
    apply IsConj.trans hkconj
    exact (isConj_iff.mpr ⟨g,by simpa only [MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using he⟩).symm
  exact source_separated_support_not_isConj_point
    hG T hempty hM hunique hmany hcard e hab H hH
      K W S hK hWU hZW hKW hST hindex hU3 hseparate hfixedFree
      _ hkW hkz hfixed z hz hconj

end CFSG.Quasithin.Chapter14.Section06
