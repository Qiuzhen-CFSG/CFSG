module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSetup
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.Fusion

/-!
# Fusion in the original contained triple-six branch

Choose z in the original U intersect Z(T). Its K-orbit has odd order,
so its marked codeword has weight four. The supplied even-orbit t has
weight six. The actual weight fibers give the two K-orbits without
replacing t. In the contained branch these remain distinct ambient
classes. E.6.1 provides the actual local normalization needed by the
fusion and conjugate-incidence lemmas.

Source: Aschbacher--Smith 12.7.9(1--3), printed p.842, and 12.7.22(5).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem coordinate_nonzero (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (v : U) (hv : v ≠ 1) : (tripleSixPointCoordinates D a v).toAdd ≠ 0 := by
  intro hz
  exact hv ((tripleSixPointCoordinates D a).injective
    (show tripleSixPointCoordinates D a v = tripleSixPointCoordinates D a 1 from
      hz.trans (tripleSixPointCoordinates D a).map_one.symm))

/-- The original Sylow-fixed z and the unchanged supplied t represent the
two original K-orbits; z has odd relative centralizer index. -/
theorem original_tripleSix_two_orbits_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    ∃ z : G, z ∈ U ∧ z ≠ 1 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      ¬ 2 ∣ (centralizer ({z} : Set G)).relIndex K ∧
      ∀ v ∈ U, v ≠ 1 → ∃ k ∈ K,
        MulAut.conj k v = z ∨ MulAut.conj k v = (t : G) := by
  have hTU := ((structural K h).2.2 U D).1
  obtain ⟨⟨z,hz⟩,hz1'⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' D.ne_bot D.le_sylow hTU)
  have hz1 : z ≠ 1 := fun he => hz1' (Subtype.ext he)
  have hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hz.2.2) s hs)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K D.sylow_normalizes_component
  have hodd : ¬ 2 ∣ (centralizer ({z} : Set G)).relIndex K := by
    intro hi
    apply P.not_dvd_index
    apply hi.trans
    apply index_dvd_of_le
    rw [hP]
    exact fun k hk => hzT hk
  let zU : U := ⟨z,hz.1⟩
  let e := tripleSixPointCoordinates D a
  have hz0 : (e zU).toAdd ≠ 0 := coordinate_nonzero D a zU (fun he => hz1 (congrArg Subtype.val he))
  have ht0 : (e t).toAdd ≠ 0 := coordinate_nonzero D a t ht
  have hzweight : hammingNorm (e zU).toAdd.val = 4 := by
    have hc := Hexacode.evenAction_orbit_card (e zU).toAdd hz0
    rw [tripleSixPoint_orbit_card D a zU] at hc
    by_contra hn
    rw [if_neg hn] at hc
    exact hodd (hc ▸ (by norm_num : 2 ∣ 18))
  have htweight : hammingNorm (e t).toAdd.val = 6 :=
    Hexacode.evenAction_full_weight_of_even_orbit (e t).toAdd ht0
      (by rwa [tripleSixPoint_orbit_card D a t])
  refine ⟨z,hz.1,hz1,hzT,hodd,?_⟩
  intro v hv hv1
  let vU : U := ⟨v,hv⟩
  have hv0 : (e vU).toAdd ≠ 0 := coordinate_nonzero D a vU
    (fun he => hv1 (congrArg Subtype.val he))
  have hweights : hammingNorm (e vU).toAdd.val = 4 ∨
      hammingNorm (e vU).toAdd.val = 6 := by
    rcases hex_weights (e vU).toAdd with h0 | h4 | h6
    · exact (hv0 (Subtype.ext (hammingNorm_eq_zero.mp h0))).elim
    · exact Or.inl h4
    · exact Or.inr h6
  have transport (w : U) (hw : hammingNorm (e w).toAdd.val = hammingNorm (e vU).toAdd.val) :
      ∃ k ∈ K, MulAut.conj k v = (w : G) := by
    have hm : (e w).toAdd ∈ Set.range (fun g : HexEvenAutomorphisms =>
        Hexacode.evenAction g (e vU).toAdd) := by
      rw [Hexacode.evenAction_orbit_eq_weight _ hv0]
      exact hw
    obtain ⟨g,hg⟩ := hm
    change Hexacode.evenAction g (tripleSixPointCoordinates D a vU).toAdd =
      (tripleSixPointCoordinates D a w).toAdd at hg
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g)
    have he := tripleSixPointCoordinates_conjugate D a k vU
    rw [hk,a.groupEquiv.apply_symm_apply,hg] at he
    change (e.symm (e w) : G) = _ at he
    rw [e.symm_apply_apply] at he
    exact ⟨k,k.property,he.symm⟩
  rcases hweights with h4 | h6
  · obtain ⟨k,hk,he⟩ := transport zU (hzweight.trans h4.symm)
    exact ⟨k,hk,Or.inl he⟩
  · obtain ⟨k,hk,he⟩ := transport t (htweight.trans h6.symm)
    exact ⟨k,hk,Or.inr he⟩

/-- Original contained-branch fusion: C_G(v) is transitive on conjugates
of U through every v in U; U is the unique conjugate through the same t;
and the whole original U lies in O2(C_G(t)). -/
theorem original_tripleSix_contained_fusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    (∀ v : G, v ∈ U → ∀ g : G, v ∈ U.conjBy g →
      ∃ c ∈ centralizer ({v} : Set G), U.conjBy c = U.conjBy g) ∧
    (∀ g : G, (t : G) ∈ U.conjBy g → U.conjBy g = U) ∧
    U ≤ (centralizer ({(t : G)} : Set G)).pCoreIn 2 := by
  obtain ⟨z,hzU,hz1,hzT,_,horbits⟩ := original_tripleSix_two_orbits_at h structural D a t ht heven
  have hzt : ¬ IsConj z (t : G) :=
    Preliminaries.not_isConj_of_even_local_orbit T K z t hzT contained heven
  have ht1 : (t : G) ≠ 1 := fun he => ht (Subtype.ext he)
  have hMt : normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G) ≤
      normalizer (U : Set G) := by
    have hc := (original_chosen_hypothesisE61_at h structural D).localCentralizer_le_normalizer
      (zpowers_ne_bot.mpr ht1) (zpowers_le.mpr t.property)
    simpa only [zpowers_eq_closure,centralizer_closure] using hc
  let := D.elementary
  refine ⟨?_,?_,Preliminaries.le_t_centralizer_core U (normalizer (K : Set G))
    t t.property hMt contained⟩
  · intro v hv g hg
    exact Preliminaries.centralizer_transitive_on_conjugates U K z t D.normalizes
      horbits hzt hv g hg
  · intro g hg
    exact Preliminaries.unique_conjugate_through_t U K (normalizer (K : Set G)) z t
      D.normalizes t.property horbits hzt contained hMt g hg

end CFSG.Quasithin.Chapter12.Section07
