module
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.QuotientHyperplane

/-!
# A hyperplane TI pair with a prescribed prime-subgroup conjugator

The quotient coprime action supplies a cyclic line inverted by an elementary
actor. If the quotient odd subgroup is the image of a specified p-subgroup P,
lift the line generator inside P itself. The quotient-hyperplane theorem then
constructs the actual pair with normalizer index two. Only the image of P
needs to be normalized; the elementary actor need not normalize P upstairs.

This retains the chosen odd Sylow supplement in the construction preceding
Aschbacher–Smith 12.2.20, printed p.802.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G K : Type*} [Group G] [Finite G] [Group K]

theorem exists_pair_index_two_in_prime_subgroup
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hTI : IsTISubgroup V)
    (q : G →* K) (hq : Function.Surjective q)
    (hk : q.ker ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (P : Subgroup G)
    (hP : IsPGroup p P) (hn : V.map q ≤ normalizer (P.map q : Set K))
    (hm : ⁅P.map q, V.map q⁆ ≠ ⊥) :
    ∃ g ∈ P, Odd (orderOf g) ∧ q g ≠ 1 ∧
      (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  let : Finite K := Finite.of_surjective q hq
  let : IsElementaryAbelian 2 (V.map q) := IsElementaryAbelian.map _
  obtain ⟨b, u, a, hbP, hu, ha, ho, hinv, hsign⟩ :=
    Theory.GroupAction.exists_inverted_prime_power_line hp (P.map q) (V.map q)
      (hP.map q) hn hm
  obtain ⟨g, hgP, hgb⟩ := hbP
  have hb : Odd (orderOf b) := ho.symm ▸ ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hb1 : b ≠ 1 := by
    intro he
    have hpow : 1 < p ^ a := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
    rw [← ho, he, orderOf_one] at hpow
    omega
  have hg : Odd (orderOf g) := by
    have hc := hP.orderOf_coprime
      (Nat.coprime_two_right.mpr ((Fact.out : p.Prime).odd_of_ne_two hp)) (⟨g, hgP⟩ : P)
    rw [← Subgroup.orderOf_coe] at hc
    exact Nat.coprime_two_right.mp hc
  obtain ⟨v, hv, hvu⟩ := hu
  refine ⟨g, hgP, hg, hgb ▸ hb1, pair_normalizer_index_two_of_quotient_inverted_line
    V hTI q hk g v hv (hgb ▸ hb) (hgb ▸ hb1) ?_ ?_⟩
  · simpa only [hgb, hvu] using hinv
  · intro w hw
    simpa only [hgb] using hsign (q w) (mem_map_of_mem q hw)

end CFSG.Quasithin.ChapterI.Section06To08
