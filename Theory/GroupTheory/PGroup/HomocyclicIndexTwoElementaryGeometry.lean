module

public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.IndexTwoIntersection
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Group.TypeTags.Finite
/-!
# Elementary eights over a homocyclic index-two subgroup

Let `C` be an abelian subgroup of index two, isomorphic to two cyclic groups
of order `2 ^ n`, with `n ≥ 2`. Assume its elements of square one are central,
and the elements of `C` commuting with an outside involution have square one.
Then outside involutions have elementary centralizers of order eight. Every
other elementary eight is one of these centralizers, is self-centralizing,
and has normalizer of order thirty-two.

Write `O` for the two-torsion of `C`. The fixed-point hypothesis gives
`C_P(t) = O ⊔ ⟨t⟩`. The commutator homomorphism `δ(c) = c*t*c⁻¹*t⁻¹`
has kernel `O`, so `δ(c)² = 1` if and only if `c⁴ = 1`. This identifies the
intersection of the normalizer with `C` as its four-torsion, of order sixteen.
The index-two formula gives the normalizer order. No separate surjectivity
argument for the restriction of `δ` to four-torsion is needed.

The fixed-point hypothesis is explicit throughout. The ambient two-group
hypothesis is unnecessary for these local calculations.

Source context: the homocyclic abelian index-two case of the MacWilliams
argument; see `refs/original/n-group-global/odd-core-rank-two-source/`.
The torsion counts use Mathlib's cyclic power-kernel cardinality formula.
-/

open Subgroup
open scoped IsMulCommutative

namespace HomocyclicIndexTwo
variable {P : Type*} [Group P]
private def torsion (C : Subgroup P) [IsMulCommutative C] (k : ℕ) : Subgroup P :=
  ((powMonoidHom k : C →* C).ker).map C.subtype
private theorem mem_torsion (C : Subgroup P) [IsMulCommutative C] (k : ℕ) (x : P) :
    x ∈ torsion C k ↔ x ∈ C ∧ x ^ k = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, congrArg Subtype.val hy⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hp, rfl⟩

private theorem card_torsion [Finite P] (C : Subgroup P) [IsMulCommutative C]
    (n k : ℕ) (hk : k ∣ 2 ^ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    Nat.card (torsion C k) = k ^ 2 := by
  let Z := Multiplicative (ZMod (2 ^ n))
  let K := (powMonoidHom k : Z →* Z).ker
  let f : (powMonoidHom k : C →* C).ker → K × K := fun x =>
    (⟨(e x).1, by
      have h := congrArg (fun c : C => (e c).1) x.property
      change (e x).1 ^ k = 1
      simpa using h⟩,
     ⟨(e x).2, by
      have h := congrArg (fun c : C => (e c).2) x.property
      change (e x).2 ^ k = 1
      simpa using h⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      exact Prod.ext (congrArg (fun z : K × K => (z.1 : Z)) h)
        (congrArg (fun z : K × K => (z.2 : Z)) h)
    · intro y
      refine ⟨⟨e.symm (y.1, y.2), ?_⟩, ?_⟩
      · change (e.symm (y.1, y.2)) ^ k = 1
        apply e.injective
        have h1 : (y.1 : Z) ^ k = 1 := y.1.property
        have h2 : (y.2 : Z) ^ k = 1 := y.2.property
        simpa using (show ((y.1 : Z), (y.2 : Z)) ^ k = 1 from Prod.ext h1 h2)
      · apply Prod.ext <;> apply Subtype.ext <;> simp [f]
  rw [torsion, card_map_of_injective C.subtype_injective,
    Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  have hK : Nat.card K = k := by
    rw [IsCyclic.card_powMonoidHom_ker]
    have hZ : Nat.card Z = 2 ^ n := by simp [Z, Nat.card_eq_fintype_card]
    rw [hZ, Nat.gcd_eq_right hk]
  rw [hK, pow_two]

private def conjugation (C : Subgroup P) [C.Normal] (t : P) : C →* C where
  toFun c := ⟨t * c * t⁻¹, (inferInstance : C.Normal).conj_mem c c.property t⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private def delta (C : Subgroup P) [IsMulCommutative C] [C.Normal] (t : P) : C →* C where
  toFun c := c * (conjugation C t c)⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private theorem delta_val (C : Subgroup P) [IsMulCommutative C] [C.Normal]
    (t : P) (c : C) : (delta C t c : P) = c * t * (c : P)⁻¹ * t⁻¹ := by
  change (c : P) * (t * c * t⁻¹)⁻¹ = _
  group

private theorem delta_eq_one (C : Subgroup P) [IsMulCommutative C] [C.Normal]
    (t : P) (c : C) : delta C t c = 1 ↔ Commute (c : P) t := by
  rw [← Subtype.coe_inj, delta_val]
  change (c : P) * t * (c : P)⁻¹ * t⁻¹ = 1 ↔ (c : P) * t = t * c
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

variable (C : Subgroup P) [IsMulCommutative C]
    (hi : C.index = 2)
    (hcentral : ∀ c ∈ C, c ^ 2 = 1 → c ∈ center P)
    (hfixed : ∀ t : P, orderOf t = 2 → t ∉ C →
      ∀ c ∈ C, Commute c t → c ^ 2 = 1)

include hcentral in
private theorem torsion_le_center : torsion C 2 ≤ center P := by
  intro c hc
  obtain ⟨hc, hp⟩ := (mem_torsion C 2 c).mp hc
  exact hcentral c hc hp

include hi hcentral hfixed

private theorem centralizer_eq_join (t : P) (ht : orderOf t = 2) (hout : t ∉ C) :
    centralizer ({t} : Set P) = torsion C 2 ⊔ zpowers t := by
  have htZ : t ∈ centralizer ({t} : Set P) := mem_centralizer_singleton_iff.mpr rfl
  apply le_antisymm
  · intro x hx
    by_cases hxC : x ∈ C
    · exact (show torsion C 2 ≤ torsion C 2 ⊔ zpowers t from le_sup_left) ((mem_torsion C 2 x).mpr
        ⟨hxC, hfixed t ht hout x hxC (mem_centralizer_singleton_iff.mp hx)⟩)
    · have hxc : x * t⁻¹ ∈ C := (C.mul_mem_iff_of_index_two hi).mpr
        (by simp only [C.inv_mem_iff]; exact iff_of_false hxC hout)
      have hxm : x * t⁻¹ ∈ torsion C 2 := (mem_torsion C 2 _).mpr
        ⟨hxc, hfixed t ht hout _ hxc (mem_centralizer_singleton_iff.mp
          ((centralizer ({t} : Set P)).mul_mem hx
            ((centralizer ({t} : Set P)).inv_mem htZ)))⟩
      have hm := (torsion C 2 ⊔ zpowers t).mul_mem ((show torsion C 2 ≤ torsion C 2 ⊔ zpowers t from le_sup_left) hxm)
        ((show zpowers t ≤ torsion C 2 ⊔ zpowers t from le_sup_right) (mem_zpowers t))
      simpa using hm
  · exact sup_le ((torsion_le_center C hcentral).trans (center_le_centralizer _))
      (zpowers_le.mpr htZ)

private theorem elementary_centralizer (t : P) (ht : orderOf t = 2) (hout : t ∉ C) :
    IsElementaryAbelian 2 (centralizer ({t} : Set P)) := by
  rw [centralizer_eq_join C hi hcentral hfixed t ht hout]
  let : IsElementaryAbelian 2 (torsion C 2) :=
    { toIsMulCommutative := le_centralizer_iff_isMulCommutative.mp
        ((torsion_le_center C hcentral).trans (center_le_centralizer _))
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext ((mem_torsion C 2 x).mp x.property).2) }
  let : IsElementaryAbelian 2 (zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  apply IsElementaryAbelian.sup_of_le_centralizer
  exact le_centralizer_iff.mp
    ((torsion_le_center C hcentral).trans (center_le_centralizer _))

private theorem card_centralizer [Finite P]
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (t : P) (ht : orderOf t = 2) (hout : t ∉ C) :
    Nat.card (centralizer ({t} : Set P)) = 8 := by
  rw [centralizer_eq_join C hi hcentral hfixed t ht hout,
    card_sup_zpowers_of_normalizing_involution]
  · rw [card_torsion C n 2 (dvd_pow_self 2 (by omega)) e]
    norm_num
  · exact ht ▸ pow_orderOf_eq_one t
  · exact fun h => hout ((mem_torsion C 2 t).mp h).1
  · exact centralizer_le_normalizer _
      (le_centralizer_iff.mp
        ((torsion_le_center C hcentral).trans (center_le_centralizer _))
        (show t ∈ (⊤ : Subgroup P) from mem_top t))

/-- The centralizer of an outside involution is elementary of order eight. -/
public theorem centralizer_geometry [Finite P]
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (t : P) (ht : orderOf t = 2) (hout : t ∉ C) :
    IsElementaryAbelian 2 (centralizer ({t} : Set P)) ∧
      Nat.card (centralizer ({t} : Set P)) = 8 :=
  ⟨elementary_centralizer C hi hcentral hfixed t ht hout,
    card_centralizer C hi hcentral hfixed n hn e t ht hout⟩

/-- Every elementary eight is the centralizer of one of its outside involutions. -/
public theorem elementary_eight_eq_centralizer [Finite P]
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    ∃ t ∈ E, orderOf t = 2 ∧ t ∉ C ∧ E = centralizer ({t} : Set P) := by
  have hnle : ¬ E ≤ C := by
    intro hle
    have hEO : E ≤ torsion C 2 := fun x hx => (mem_torsion C 2 x).mpr
      ⟨hle hx, elemPow_eq_one_of_isElementaryAbelian x hx⟩
    have hc := card_le_of_le hEO
    rw [hE, card_torsion C n 2 (dvd_pow_self 2 (by omega)) e] at hc
    norm_num at hc
  obtain ⟨t, htE, htC⟩ := SetLike.not_le_iff_exists.mp hnle
  have ht : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htE)
    (fun h => htC (h ▸ C.one_mem))
  refine ⟨t, htE, ht, htC, eq_of_le_of_card_ge ?_ ?_⟩
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr ((E.le_centralizer htE) x hx)
  · rw [hE, card_centralizer C hi hcentral hfixed n hn e t ht htC]

/-- Every elementary eight in this index-two geometry is self-centralizing. -/
public theorem elementary_eight_self_centralizing [Finite P]
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    centralizer (E : Set P) = E := by
  obtain ⟨t, htE, _, _, hEq⟩ :=
    elementary_eight_eq_centralizer C hi hcentral hfixed n hn e E hE
  apply le_antisymm _ E.le_centralizer
  exact (centralizer_le (Set.singleton_subset_iff.mpr htE)).trans hEq.ge

variable [C.Normal]

omit hi in
private theorem delta_sq_iff (t : P) (ht : orderOf t = 2) (hout : t ∉ C) (c : C) :
    delta C t c ^ 2 = 1 ↔ (c : P) ^ 4 = 1 := by
  rw [← map_pow, delta_eq_one]
  constructor
  · intro hc
    have h := hfixed t ht hout ((c : P) ^ 2) (C.pow_mem c.property 2) hc
    simpa [← pow_mul] using h
  · intro hc
    have hz := hcentral ((c : P) ^ 2) (C.pow_mem c.property 2)
      (by simpa [← pow_mul] using hc)
    exact mem_centralizer_singleton_iff.mp (center_le_centralizer ({t} : Set P) hz)

private theorem normalizer_mem_iff_fourth [Finite P]
    (t : P) (ht : orderOf t = 2) (hout : t ∉ C) (c : C) :
    (c : P) ∈ normalizer (centralizer ({t} : Set P) : Set P) ↔ (c : P) ^ 4 = 1 := by
  let E := centralizer ({t} : Set P)
  have htE : t ∈ E := mem_centralizer_singleton_iff.mpr rfl
  rw [← delta_sq_iff C hcentral hfixed t ht hout c]
  constructor
  · intro hcN
    have hdE : (delta C t c : P) ∈ E := by
      rw [delta_val]
      exact E.mul_mem ((hcN t).mp htE) (E.inv_mem htE)
    exact Subtype.ext (hfixed t ht hout _ (delta C t c).property
      (mem_centralizer_singleton_iff.mp hdE))
  · intro hd
    have hdO : (delta C t c : P) ∈ torsion C 2 := (mem_torsion C 2 _).mpr
      ⟨(delta C t c).property, congrArg Subtype.val hd⟩
    have hEq : E = torsion C 2 ⊔ zpowers t := centralizer_eq_join C hi hcentral hfixed t ht hout
    have hOt : torsion C 2 ≤ E := hEq ▸ le_sup_left
    have hct : (c : P) * t * (c : P)⁻¹ ∈ E := by
      have h := E.mul_mem (hOt hdO) htE
      simpa only [delta_val, mul_assoc, inv_mul_cancel, mul_one] using h
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · change E.map (MulAut.conj (c : P)).toMonoidHom ≤ E
      rw [hEq, Subgroup.map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · rintro x ⟨o, ho, rfl⟩
        have hz := torsion_le_center C hcentral ho
        have he : (c : P) * o * (c : P)⁻¹ = o := by
          rw [(Subgroup.mem_center_iff.mp hz) (c : P), mul_assoc, mul_inv_cancel, mul_one]
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, he] using
          ((show torsion C 2 ≤ torsion C 2 ⊔ zpowers t from le_sup_left) ho)
      · apply zpowers_le.mpr
        exact hEq ▸ hct
    · rw [card_map_of_injective (MulAut.conj (c : P)).injective]

private theorem card_normalizer_centralizer [Finite P]
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (t : P) (ht : orderOf t = 2) (hout : t ∉ C) :
    Nat.card (normalizer (centralizer ({t} : Set P) : Set P)) = 32 := by
  let N := normalizer (centralizer ({t} : Set P) : Set P)
  have htN : t ∈ N := (centralizer ({t} : Set P)).le_normalizer
    (mem_centralizer_singleton_iff.mpr rfl)
  have hinter : C ⊓ N = torsion C 4 := by
    ext x
    rw [mem_inf, mem_torsion]
    constructor
    · rintro ⟨hxC, hxN⟩
      exact ⟨hxC, (normalizer_mem_iff_fourth C hi hcentral hfixed t ht hout ⟨x, hxC⟩).mp hxN⟩
    · rintro ⟨hxC, hx4⟩
      exact ⟨hxC, (normalizer_mem_iff_fourth C hi hcentral hfixed t ht hout ⟨x, hxC⟩).mpr hx4⟩
  have hc : Nat.card (C.subgroupOf N) = 16 := by
    rw [← card_map_of_injective (K := C.subgroupOf N) N.subtype_injective,
      subgroupOf_map_subtype, hinter,
      card_torsion C n 4 (show 2 ^ 2 ∣ 2 ^ n from pow_dvd_pow 2 hn) e]
    norm_num
  have hiN : (C.subgroupOf N).index = 2 :=
    subgroupOf_index_eq_two C N hi (fun h => hout (h htN))
  have hh := (C.subgroupOf N).card_mul_index
  rw [hc, hiN] at hh
  exact hh.symm

/-- Every elementary eight has normalizer of order thirty-two. -/
public theorem elementary_eight_normalizer_card [Finite P]
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    Nat.card (normalizer (E : Set P)) = 32 := by
  obtain ⟨t, _, ht, hout, rfl⟩ :=
    elementary_eight_eq_centralizer C hi hcentral hfixed n hn e E hE
  exact card_normalizer_centralizer C hi hcentral hfixed n hn e t ht hout

end HomocyclicIndexTwo
