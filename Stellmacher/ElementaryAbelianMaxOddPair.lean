module
public import Stellmacher.ElementaryAbelianMaxNormalizerAction
public import Theory.GroupTheory.PairNormalizerIndex
/-!
# Odd normalizers fix a two-member maximum elementary family

The normalizer of J(S) permutes the maximum elementary subgroups of S.
If that family has at most two specified members, moving one gives an
index-two normalizer in the actor. An odd-order actor cannot do this.
No assumption that the two displayed members are distinct is needed.

Source application: Aschbacher–Smith 2.4.8(5), printed p.530.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G]

theorem odd_normalizes_maximum_pair (S D A B : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups S = {A,B})
    (hD : D ≤ normalizer (elementaryAbelianMaxJ S : Set G))
    (hodd : Odd (Nat.card D)) :
    D ≤ normalizer (A : Set G) ∧ D ≤ normalizer (B : Set G) := by
  have hfix (P Q : Subgroup G) (hf' : elementaryAbelianMaxSubgroups S = {P,Q}) :
      D ≤ normalizer (P : Set G) := by
    have hpair (g : G) (hg : g ∈ D) :
        P.map (MulAut.conj g).toMonoidHom = P ∨ P.map (MulAut.conj g).toMonoidHom = Q := by
      have hm := maxFamily_map_of_normalizes_maxJ S P (hf' ▸ Set.mem_insert _ _) g (hD hg)
      simpa only [hf',Set.mem_insert_iff,Set.mem_singleton_iff] using hm
    intro g hg
    by_contra hn
    have hm : P.map (MulAut.conj g).toMonoidHom ≠ P := fun he =>
      hn (mem_normalizer_iff_map_conj_eq.mpr he)
    have hi := normalizer_relIndex_eq_two_of_pair D P Q hpair g hg hm
    have hd : 2 ∣ Nat.card D := hi ▸ (normalizer (P : Set G)).relIndex_dvd_card D
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  exact ⟨hfix A B hf,hfix B A (hf.trans (Set.pair_comm _ _))⟩

end Stellmacher

