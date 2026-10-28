module
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.GroupTheory.CComponent.RadicalPairSpectrum
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.Order.Atoms.Finite

/-!
# Component uniqueness from Sylow-containing two-locals

Distinct C-components force two prime divisors outside two and three, counted
with multiplicity. Thus an order dividing 2^n 3^m p, with p a different prime,
permits only one component in any subgroup.

A nontrivial two-core in a containing subgroup M places every Sylow overgroup
P ≤ M inside its ambient normalizer. An actual cover of such two-locals by
groups with component uniqueness therefore settles P. In a perfect simple
group, any remaining failure gives a maximal odd-index subgroup with trivial
two-core. The cover and the nontrivial-core hypothesis remain explicit here;
the Held and Rudvalis consumers prove their local covers separately.

Source: Aschbacher--Smith A.3.12, printed pp.47--48, and the embedding
restriction 1.2.8(1), printed p.506.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- A single prime outside two and three, occurring to exponent at most one,
precludes distinct components in every subgroup. -/
theorem SylowOvergroupComponentUnique.of_card_dvd_two_three_prime {H : Type*} [Group H] [Finite H]
    (n m p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hc : Nat.card H ∣ 2^n * 3^m * p) : SylowOvergroupComponentUnique H := by
  intro S P _ B C hB hC
  by_contra hn
  obtain ⟨r,s,hr,hs,hr2,hr3,hs2,hs3,hd,_⟩ := hB.exists_prime_pair_of_ne hC hn
  have hd := hd.trans (P.card_subgroup_dvd_card.trans hc)
  have key (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
      (hd : r ∣ 2^n * 3^m * p) : r = p := by
    rcases hr.dvd_mul.mp hd with hd | hd
    · rcases hr.dvd_mul.mp hd with hd | hd
      · exact (hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          (hr.dvd_of_dvd_pow hd))).elim
      · exact (hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
          (hr.dvd_of_dvd_pow hd))).elim
    · exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hd
  have hrp := key r hr hr2 hr3 ((dvd_mul_right r s).trans hd)
  have hsp := key s hs hs2 hs3 ((dvd_mul_left s r).trans hd)
  rw [hrp,hsp] at hd
  have hdpp : p * p ∣ p * (2^n * 3^m) := by
    simpa only [Nat.mul_comm] using hd
  have hd : p ∣ 2^n * 3^m := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdpp
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd))


namespace SylowOvergroupComponentUnique
variable {G : Type*} [Group G] [Finite G]

/-- Restrict uniqueness after a specified ambient change of coordinates. -/
theorem eq_of_le_mapped_overgroup (S : Sylow 2 G) {P J : Subgroup G}
    (e : G ≃* G) (hSP : (S : Subgroup G) ≤ P)
    (hPJ : P.map e.toMonoidHom ≤ J) (hJ : SylowOvergroupComponentUnique J)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  let f := e.subgroupMap P
  apply map_injective (f := f.toMonoidHom) f.injective
  exact eq_of_le_overgroup (S.mapSurjective e.surjective) (map_mono hSP) hPJ hJ
    (hB.map_equiv f) (hC.map_equiv f)

/-- The normalizer of the containing subgroup's nontrivial two-core is a
Sylow-containing two-local. A proved local cover then gives uniqueness in P. -/
theorem eq_of_le_overgroup_twoCore_ne_bot
    (hlocal : ∀ (S : Sylow 2 G) (N : Subgroup G),
      (S : Subgroup G) ≤ N → IsTwoLocal N →
      ∃ (e : G ≃* G) (J : Subgroup G), N.map e.toMonoidHom ≤ J ∧
        SylowOvergroupComponentUnique J)
    (S : Sylow 2 G) (P M : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (hPM : P ≤ M) (hcore : pCore 2 M ≠ ⊥)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  let U := (pCore 2 M).map M.subtype
  have hU : U ≠ ⊥ := fun he => hcore
    ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp he)
  have hMN : M ≤ normalizer (U : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  obtain ⟨e,J,hNJ,hJ⟩ := hlocal S _ (hSP.trans (hPM.trans hMN))
    ⟨U,hU,pCore_isPGroup.map M.subtype,rfl⟩
  exact eq_of_le_mapped_overgroup S e hSP ((map_mono (hPM.trans hMN)).trans hNJ) hJ hB hC


/-- Transport the nontrivial-two-core restriction through an actual model equivalence. -/
theorem eq_of_le_overgroup_twoCore_ne_bot_of_equiv
    {H : Type*} [Group H] (e : G ≃* H)
    (h : ∀ (S : Sylow 2 H) (P M : Subgroup H), (S : Subgroup H) ≤ P → P ≤ M →
      pCore 2 M ≠ ⊥ → ∀ B C : Subgroup P, B.IsCComponent → C.IsCComponent → B = C)
    (S : Sylow 2 G) (P M : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (hPM : P ≤ M) (hcore : pCore 2 M ≠ ⊥)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  let f := e.subgroupMap P
  have hc : pCore 2 (M.map e.toMonoidHom) ≠ ⊥ := by
    intro he
    apply hcore
    apply (map_eq_bot_iff_of_injective (f := (e.subgroupMap M).toMonoidHom)
      _ (e.subgroupMap M).injective).mp
    rw [pCore_map_iso]
    exact he
  apply map_injective (f := f.toMonoidHom) f.injective
  exact h (S.mapSurjective e.surjective) _ _ (map_mono hSP) (map_mono hPM) hc _ _
    (hB.map_equiv f) (hC.map_equiv f)

/-- Any remaining failure lies inside a maximal odd-index subgroup with trivial
two-core. This is an obstruction reduction, not a proof that such subgroups do not exist. -/
theorem exists_coreFree_maximal_of_not_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (h : ∀ (S : Sylow 2 G) (P M : Subgroup G), (S : Subgroup G) ≤ P → P ≤ M →
      pCore 2 M ≠ ⊥ → ∀ B C : Subgroup P, B.IsCComponent → C.IsCComponent → B = C)
    (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ (S : Sylow 2 G) (M : Subgroup G), IsCoatom M ∧ (S : Subgroup G) ≤ M ∧
      ¬ 2 ∣ M.index ∧ pCore 2 M = ⊥ := by
  classical
  by_contra hn
  apply hu
  apply of_proper_overgroups
  intro S P hSP hP B C hB hC
  obtain ⟨M,hM,hPM⟩ := (eq_top_or_exists_le_coatom P).resolve_left hP
  have hSM := hSP.trans hPM
  have hi : ¬ 2 ∣ M.index := fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSM))
  have hc : pCore 2 M ≠ ⊥ := fun he => hn ⟨S,M,hM,hSM,hi,he⟩
  exact h S P M hSP hPM hc B C hB hC

end SylowOvergroupComponentUnique
end Theory.GroupTheory
