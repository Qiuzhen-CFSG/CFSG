module

public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# TI counting and Sylow indices in the rank-two reductions

For K tightly embedded, a two-group V ∩ K has disjoint distinct conjugates
under N_G(V). The proof compares the two-power order of an intersection
with the odd order imposed by tight embedding. Counting their nonidentity
elements bounds the orbit size. A Sylow two-subgroup in the stabilizer
forces that size to be odd, contradicting the Sp₄ count `(q-1)^2+1`.

A separate divisibility argument treats the long-root case when only
`N_T(X)` lies in the acting group: a power-of-two orbit index divides
`|T : N_T(X)|`. No Sylow claim about that intersection is needed.
The model-dependent construction of the containing set and Cartan orbit
is left explicit in the counting theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1201–1202 (Lemma 16.5.13).
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo
open Subgroup
open scoped Pointwise BigOperators
variable {G : Type*} [Group G] [Finite G]

private theorem disjoint_intersection_conj_of_tight
    {K V : Subgroup G} (hK : Theory.GroupTheory.IsTightlyEmbedded K)
    (hU : IsPGroup 2 ↥(V ⊓ K)) {g : G}
    (hgV : g ∈ normalizer (V : Set G))
    (hne : V ⊓ K ≠ (V ⊓ K).conjBy g) :
    Disjoint (V ⊓ K) ((V ⊓ K).conjBy g) := by
  have hgK : g ∉ normalizer (K : Set G) := by
    intro hgK
    apply hne
    symm
    change (V ⊓ K).map (MulAut.conj g).toMonoidHom = V ⊓ K
    rw [map_inf _ _ _ (MulAut.conj g).injective, MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp hgV, mem_normalizer_iff_map_conj_eq.mp hgK]
  let Q := (V ⊓ K) ⊓ (V ⊓ K).conjBy g
  have hQ : IsPGroup 2 Q := hU.to_le inf_le_left
  have hle : Q ≤ K ⊓ K.conjBy g :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans (map_mono inf_le_right))
  have hodd := hK.2 g hgK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hcop : (Nat.card Q).Coprime (Nat.card ↥(K ⊓ K.conjBy g)) := by
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hb := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [inf_eq_left.mpr hle] at hb
  exact disjoint_iff.mpr hb

/-- Intersect a tightly embedded K with an M-invariant subgroup V.
If the intersection is a two-group, its distinct M-conjugates are disjoint.
This proves the TI assertion used in both rank-two orbit arguments. -/
theorem ti_conjugates_of_tightlyEmbedded_intersection
    {K V M : Subgroup G} (hK : Theory.GroupTheory.IsTightlyEmbedded K)
    (hU : IsPGroup 2 ↥(V ⊓ K)) (hM : M ≤ normalizer (V : Set G))
    {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (hne : (V ⊓ K).conjBy a ≠ (V ⊓ K).conjBy b) :
    Disjoint ((V ⊓ K).conjBy a) ((V ⊓ K).conjBy b) := by
  have hgV := hM (M.mul_mem (M.inv_mem ha) hb)
  have hne' : V ⊓ K ≠ (V ⊓ K).conjBy (a⁻¹ * b) := by
    intro he
    apply hne
    have hh := congrArg (fun U : Subgroup G => U.conjBy a) he
    simpa only [conjBy_conjBy, mul_inv_cancel_left] using hh
  have hd := disjoint_intersection_conj_of_tight hK hU hgV hne'
  have hm := Subgroup.disjoint_map (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective hd
  change Disjoint ((V ⊓ K).conjBy a)
    (((V ⊓ K).conjBy (a⁻¹ * b)).conjBy a) at hm
  simpa only [conjBy_conjBy, mul_inv_cancel_left] using hm

/-- The nonidentity elements in a TI family are disjoint, so a containing
set bounds the number of members times their common punctured order. -/
theorem ti_family_card_bound
    (F : Finset (Subgroup G)) (β : Finset G) (r : ℕ)
    (hcard : ∀ U ∈ F, Nat.card U = r)
    (hTI : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → Disjoint U V)
    (hβ : ∀ U ∈ F, ∀ x ∈ U, x ≠ 1 → x ∈ β) :
    F.card * (r - 1) ≤ β.card := by
  classical
  let := Fintype.ofFinite G
  let parts (U : Subgroup G) : Finset G := (U : Set G).toFinset.erase 1
  have hparts (U : Subgroup G) (hU : U ∈ F) : (parts U).card = r - 1 := by
    change ((U : Set G).toFinset.erase 1).card = r - 1
    rw [Finset.card_erase_of_mem (by simp), Set.toFinset_card]
    rw [← Nat.card_eq_fintype_card]
    change Nat.card U - 1 = r - 1
    exact congrArg (fun n : ℕ => n - 1) (hcard U hU)
  have hd : (F : Set (Subgroup G)).PairwiseDisjoint parts := by
    intro U hU V hV hne
    apply Finset.disjoint_left.mpr
    intro x hxU hxV
    obtain ⟨hx1, hxU⟩ := Finset.mem_erase.mp hxU
    obtain ⟨_, hxV⟩ := Finset.mem_erase.mp hxV
    exact hx1 (Subgroup.disjoint_def.mp (hTI U hU V hV hne)
      (Set.mem_toFinset.mp hxU) (Set.mem_toFinset.mp hxV))
  calc
    F.card * (r - 1) = ∑ U ∈ F, (parts U).card := by
      simp only [Finset.sum_congr rfl hparts, Finset.sum_const, smul_eq_mul]
    _ = (F.biUnion parts).card := (Finset.card_biUnion hd).symm
    _ ≤ β.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨U, hU, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hx1, hx⟩ := Finset.mem_erase.mp hx
      exact hβ U hU x (Set.mem_toFinset.mp hx) hx1

/-- If a Sylow two-subgroup fixes U, its orbit under any overgroup has odd
size. Here the family is the actual family of subgroup conjugates. -/
theorem odd_conjugate_family_card
    (T : Sylow 2 G) (M U : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (F : Finset (Subgroup G))
    (hF : ∀ V, V ∈ F ↔ ∃ a : M, U.conjBy a = V) : Odd F.card := by
  let : MulAction M (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp M.subtype)
  have hsmul (a : M) (V : Subgroup G) : a • V = V.conjBy a := rfl
  have hstab : (T.subtype hTM : Subgroup M) ≤ MulAction.stabilizer M U := by
    intro a ha
    change a • U = U
    rw [hsmul]
    exact mem_normalizer_iff_map_conj_eq.mp (hTU ha)
  have hn : ¬ 2 ∣ (MulAction.stabilizer M U).index := fun h =>
    (T.subtype hTM).not_dvd_index (h.trans (index_dvd_of_le hstab))
  have horbit : MulAction.orbit M U = (F : Set (Subgroup G)) := by
    ext V
    rw [MulAction.mem_orbit_iff]
    exact (hF V).symm
  rw [MulAction.index_stabilizer, horbit, Set.ncard_coe_finset] at hn
  exact Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))

/-- A power-of-two orbit index divides `|T : P|` whenever P lies both
in the Sylow two-subgroup T and in the point stabilizer. In the long-root argument this bounds the
power-of-two alternative by `|T : N_T(X)| ≤ 2`, without asserting that
`N_T(X)` itself is Sylow in the whole acting group. -/
theorem two_power_relIndex_dvd_sylow_relIndex
    (T : Sylow 2 G) {P M N : Subgroup G} (n : ℕ)
    (hPT : P ≤ (T : Subgroup G)) (hPM : P ≤ M) (hPN : P ≤ N)
    (hindex : N.relIndex M = 2 ^ n) : 2 ^ n ∣ P.relIndex (T : Subgroup G) := by
  have hd : 2 ^ n ∣ P.index := by
    rw [← hindex]
    exact (relIndex_dvd_of_le_left M hPN).trans (relIndex_dvd_index_of_le hPM)
  rw [← relIndex_mul_index hPT] at hd
  have hc : Nat.Coprime (2 ^ n) (T : Subgroup G).index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr T.not_dvd_index).pow_left n
  exact hc.dvd_of_dvd_mul_right hd

/-- The Sp₄ count on printed p.1202: a TI orbit filling a set of at most
`((q-1)^2+1)(r-1)` points has even size, contradicting its Sylow stabilizer.
The separate model argument must construct β, prove containment, and
produce the Cartan orbit giving the lower bound. -/
theorem symplectic_ti_count_contradiction
    (T : Sylow 2 G) (M U : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (F : Finset (Subgroup G)) (β : Finset G) (q r : ℕ)
    (hq : Even q) (hq2 : 2 ≤ q) (hr : 1 < r)
    (hF : ∀ V, V ∈ F ↔ ∃ a : M, U.conjBy a = V)
    (hU : Nat.card U = r)
    (hTI : ∀ V ∈ F, ∀ W ∈ F, V ≠ W → Disjoint V W)
    (hβ : ∀ V ∈ F, ∀ x ∈ V, x ≠ 1 → x ∈ β)
    (hβcard : β.card ≤ ((q - 1) ^ 2 + 1) * (r - 1))
    (hlower : (q - 1) ^ 2 + 1 ≤ F.card) : False := by
  have hcard : ∀ V ∈ F, Nat.card V = r := by
    intro V hV
    obtain ⟨a, rfl⟩ := (hF V).mp hV
    exact (card_map_of_injective (MulAut.conj (a : G)).injective).trans hU
  have hbound := (ti_family_card_bound F β r hcard hTI hβ).trans hβcard
  have hupper : F.card ≤ (q - 1) ^ 2 + 1 :=
    Nat.le_of_mul_le_mul_right hbound (by omega)
  have heq := le_antisymm hupper hlower
  have hodd := odd_conjugate_family_card T M U hTM hTU F hF
  have heven : Even ((q - 1) ^ 2 + 1) := by
    have hqodd : Odd (q - 1) := Nat.Even.sub_odd (by omega) hq odd_one
    exact hqodd.pow.add_odd odd_one
  exact (Nat.not_even_iff_odd.mpr hodd) (heq ▸ heven)

end CFSG.Quasithin.Chapter16.Intersections.RankTwo
