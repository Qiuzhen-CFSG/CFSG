module

public import Theory.GroupTheory.SylowCentralizerInversion
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.SylowCentralizerInvolutionCosets
import Mathlib.Tactic

/-!
# The Suzuki–Feit bound for a self-centralizing Sylow two-subgroup

For a nonnormal Sylow two-subgroup `P` containing two distinct involutions,
centralizer containment implies `Nat.card (Sylow 2 G) ≤ Nat.card P + 1`.
The initial involution count supplies the coset saturation and nontrivial
normalizer quotient used in the disjoint-product argument below.

Write `L = N_G(P)`. If every `P`-coset outside `L` contains an involution,
then a nonidentity element of `L \ P` has its centralizer in `L`: conjugation
preserves an external coset, hence fixes its unique involution. A member of
`L` commuting with an involution must lie in `P`, giving a contradiction.

Saturation gives exactly `[L:P]` involutions in each external `L`-coset.
Choose one as a base and multiply it by the others. These products lie in `L \ P`. Equal products
from two cosets force the product of their bases into the centralizer, so the
cosets coincide. The resulting injection gives
`([G:L]-1)([L:P]-1) ≤ |P|([L:P]-1)`, which yields the bound when `[L:P] > 1`.

Source: Suzuki, *Finite groups with nilpotent centralizers* (1961), Part I,
Theorem 2, Lemma 7 and the counting argument, printed pp. 430–431.
-/

open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
variable (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
  centralizer ({x} : Set G) ≤ (P : Subgroup G))

include hcent in
private lemma centralizer_involution_isPGroup {t : G} (ht : orderOf t = 2) :
    IsPGroup 2 (centralizer ({t} : Set G)) := by
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ht)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hyne : (y : G) ≠ 1 := by
    intro he
    have heq : (MulAut.conj g) t = 1 := hg.trans he
    have htone : t = 1 := (MulAut.conj g).injective (heq.trans (map_one _).symm)
    simp [htone] at ht
  let f : centralizer ({t} : Set G) →* P :=
    ((MulAut.conj g).toMonoidHom.comp (centralizer ({t} : Set G)).subtype).codRestrict
      (P : Subgroup G) (fun z => hcent y y.property hyne (by
        apply mem_centralizer_singleton_iff.mpr
        rw [← hg]
        simpa [MulAut.conj_apply, mul_assoc] using congrArg (MulAut.conj g)
          (mem_centralizer_singleton_iff.mp z.property)))
  exact P.isPGroup'.of_injective f (fun a b h => Subtype.ext
    ((MulAut.conj g).injective (congrArg Subtype.val h)))

include hcent in
private lemma mem_of_normalizes_of_commutes_involution {t v : G} (ht : orderOf t = 2)
    (hv : v ∈ normalizer (P : Set G)) (hvt : v * t = t * v) : v ∈ (P : Subgroup G) := by
  have hi := (P.centralizer_involution_isPGroup hcent ht).inf_normalizer_sylow P
  have hv' : v ∈ centralizer ({t} : Set G) ⊓ normalizer (P : Set G) :=
    ⟨mem_centralizer_singleton_iff.mpr hvt, hv⟩
  rw [hi] at hv'
  exact hv'.2

include hcent in
/-- Coset saturation contains centralizers of normalizer elements outside the Sylow subgroup. -/
public theorem centralizer_le_normalizer_of_cover
    (hcover : ∀ g : G, g ∉ normalizer (P : Set G) →
      ∃ t : G, orderOf t = 2 ∧ g⁻¹ * t ∈ (P : Subgroup G))
    {v : G} (hv : v ∈ normalizer (P : Set G)) (hvn : v ∉ (P : Subgroup G)) :
    centralizer ({v} : Set G) ≤ normalizer (P : Set G) := by
  intro g hg
  by_contra hgn
  obtain ⟨t, ht, hgt⟩ := hcover g hgn
  have htn : t ∉ (P : Subgroup G) := by
    intro htP
    have : g⁻¹ ∈ (P : Subgroup G) := by
      simpa using (P : Subgroup G).mul_mem hgt ((P : Subgroup G).inv_mem htP)
    exact hgn (le_normalizer (by simpa using (P : Subgroup G).inv_mem this))
  have hcomm := mem_centralizer_singleton_iff.mp hg
  have hcv : g⁻¹ * (v * t * v⁻¹) ∈ (P : Subgroup G) := by
    have hh := (mem_normalizer_iff.mp hv (g⁻¹ * t)).mp hgt
    have he : g⁻¹ * (v * t * v⁻¹) = v * (g⁻¹ * t) * v⁻¹ := by
      have hc : g⁻¹ * v = v * g⁻¹ := by
        apply (Commute.inv_left (show Commute g v from hcomm)).eq
      simp only [mul_assoc] at hc ⊢
      rw [← mul_assoc g⁻¹ v, hc, mul_assoc]
    rwa [he]
  have hprod : t * (v * t * v⁻¹)⁻¹ ∈ (P : Subgroup G) := by
    have hh := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hgt) hcv
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by
      simpa [pow_two, ht] using pow_orderOf_eq_one t)
    have hci : (v * t * v⁻¹)⁻¹ = v * t * v⁻¹ := by simp [mul_inv_rev, hti, mul_assoc]
    simpa [mul_inv_rev, mul_assoc, hti, hci] using hh
  have hpow : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have heq := P.eq_of_involutions_mul_inv_mem_of_centralizer_le hcent htn hpow
    (show (v * t * v⁻¹) ^ 2 = 1 by
      simpa using congrArg (MulAut.conj v) hpow) hprod
  exact hvn (P.mem_of_normalizes_of_commutes_involution hcent ht hv
    (mul_inv_eq_iff_eq_mul.mp heq.symm))
end Sylow

namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private lemma nat_card_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {b : α // b ≠ a} = Nat.card α - 1 := by
  classical
  let := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [Finite G] in
private lemma inv_eq_self_of_order_two {t : G} (ht : orderOf t = 2) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_left (by simpa [pow_two, ht] using pow_orderOf_eq_one t)

/-- The disjoint-product count after saturation of the external Sylow cosets. -/
private theorem card_sylow_le_of_involution_cosets (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hcover : ∀ g : G, g ∉ normalizer (P : Set G) →
      ∃ t : G, orderOf t = 2 ∧ g⁻¹ * t ∈ (P : Subgroup G))
    (hcount : ∀ q : G ⧸ normalizer (P : Set G), q ≠ ((1 : G) : G ⧸ normalizer (P : Set G)) →
      Nat.card {t : G // orderOf t = 2 ∧ (t : G ⧸ normalizer (P : Set G)) = q} =
        (P : Subgroup G).relIndex (normalizer (P : Set G)))
    (hindex : 1 < (P : Subgroup G).relIndex (normalizer (P : Set G))) :
    Nat.card (Sylow 2 G) ≤ Nat.card P + 1 := by
  classical
  let L := normalizer (P : Set G)
  change 1 < (P : Subgroup G).relIndex L at hindex
  let X := {q : G ⧸ L // q ≠ ((1 : G) : G ⧸ L)}
  let I (q : X) := {t : G // orderOf t = 2 ∧ (t : G ⧸ L) = q.val}
  have hI (q : X) : Nat.card (I q) = (P : Subgroup G).relIndex L := hcount q q.property
  have hex (q : X) : Nonempty (I q) := (Nat.card_pos_iff.mp (by rw [hI]; omega)).1
  let a (q : X) : I q := Classical.choice (hex q)
  have hn (q : X) (t : I q) : (t : G) ∉ L := by
    intro ht
    apply q.property
    rw [← t.property.2]
    apply QuotientGroup.eq.mpr
    simpa using L.inv_mem ht
  have hnP (q : X) (t : I q) : (t : G) ∉ (P : Subgroup G) :=
    fun ht => hn q t (le_normalizer ht)
  have hinv (q : X) (t : I q) : (t : G)⁻¹ = t :=
    inv_eq_self_of_order_two t.property.1
  let D := Σ q : X, {t : I q // t ≠ a q}
  let f (z : D) : G := (a z.1 : G) * (z.2.val : G)
  have hfL (z : D) : f z ∈ L := by
    have he : ((a z.1 : G) : G ⧸ L) = ((z.2.val : G) : G ⧸ L) :=
      (a z.1).property.2.trans z.2.val.property.2.symm
    simpa only [hinv] using QuotientGroup.eq.mp he
  have hfP (z : D) : f z ∉ (P : Subgroup G) := by
    intro hz
    have he := P.eq_of_involutions_mul_inv_mem_of_centralizer_le hcent (hnP _ (a z.1))
      (show (a z.1 : G) ^ 2 = 1 by simpa only [(a z.1).property.1] using pow_orderOf_eq_one (a z.1 : G))
      (show (z.2.val : G) ^ 2 = 1 by simpa only [z.2.val.property.1] using pow_orderOf_eq_one (z.2.val : G))
      (show (a z.1 : G) * (z.2.val : G)⁻¹ ∈ (P : Subgroup G) by rwa [hinv])
    exact z.2.property (Subtype.ext he.symm)
  have hfinj : Function.Injective f := by
    rintro ⟨q, b, hb⟩ ⟨r, d, hd⟩ he
    change (a q : G) * (b : G) = (a r : G) * (d : G) at he
    have hac : (a q : G) * (a r : G) ∈ L := by
      apply P.centralizer_le_normalizer_of_cover hcent hcover
        (hfL ⟨q, b, hb⟩) (hfP ⟨q, b, hb⟩)
      apply mem_centralizer_singleton_iff.mpr
      change ((a q : G) * (a r : G)) * ((a q : G) * (b : G)) =
        ((a q : G) * (b : G)) * ((a q : G) * (a r : G))
      have hcc : (a r : G) * (a r : G) = 1 := by
        simpa [hinv] using inv_mul_cancel (a r : G)
      have hdv : (d : G) * (a r : G) = (b : G) * (a q : G) := by
        simpa only [mul_inv_rev, hinv] using congrArg Inv.inv he.symm
      calc
        _ = (a q : G) * (d : G) := by rw [mul_assoc, he, ← mul_assoc (a r : G), hcc, one_mul]
        _ = (a q : G) * ((d : G) * (a r : G)) * (a r : G) := by
          simp only [mul_assoc, hcc, mul_one]
        _ = _ := by rw [hdv]; simp only [mul_assoc]
    have hqr : q = r := by
      apply Subtype.ext
      rw [← (a q).property.2, ← (a r).property.2]
      apply QuotientGroup.eq.mpr
      simpa only [hinv] using hac
    subst r
    have hbd : b = d := Subtype.ext (mul_left_cancel he)
    subst d
    rfl
  let F (z : D) : {v : L // (v : G) ∉ (P : Subgroup G)} := ⟨⟨f z, hfL z⟩, hfP z⟩
  have hbound := Nat.card_le_card_of_injective F (fun z w h =>
    hfinj (congrArg (fun v => ((v.val : L) : G)) h))
  have hD : Nat.card D = (L.index - 1) * ((P : Subgroup G).relIndex L - 1) := by
    let := Fintype.ofFinite X
    rw [show Nat.card D = ∑ q : X, Nat.card {t : I q // t ≠ a q} from Nat.card_sigma]
    simp_rw [nat_card_ne, hI]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    congr 1
    exact nat_card_ne ((1 : G) : G ⧸ L)
  have hcod : Nat.card {v : L // (v : G) ∉ (P : Subgroup G)} = Nat.card L - Nat.card P := by
    let := Fintype.ofFinite L
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show (P : Subgroup G) ≤ L from le_normalizer)).toEquiv
  rw [hD, hcod] at hbound
  have hmul : (P : Subgroup G).relIndex L * Nat.card P = Nat.card L := by
    have hh := ((P : Subgroup G).subgroupOf L).index_mul_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (P : Subgroup G) ≤ L from le_normalizer)).toEquiv] at hh
  have hmul' : Nat.card L - Nat.card P = Nat.card P * ((P : Subgroup G).relIndex L - 1) := by
    rw [← hmul, Nat.mul_comm, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hmul'] at hbound
  have hle := Nat.le_of_mul_le_mul_right hbound (by omega)
  rw [P.card_eq_index_normalizer]
  change L.index ≤ Nat.card P + 1
  omega

/-- Saturated Sylow cosets give exactly the relative index many involutions in each
external normalizer coset. -/
public theorem card_involutions_normalizer_coset_of_cover (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hcover : ∀ g : G, g ∉ normalizer (P : Set G) →
      ∃ t : G, orderOf t = 2 ∧ g⁻¹ * t ∈ (P : Subgroup G))
    (q : G ⧸ normalizer (P : Set G)) (hq : q ≠ ((1 : G) : G ⧸ normalizer (P : Set G))) :
    Nat.card {t : G // orderOf t = 2 ∧ (t : G ⧸ normalizer (P : Set G)) = q} =
      (P : Subgroup G).relIndex (normalizer (P : Set G)) := by
  classical
  let L := normalizer (P : Set G)
  let g := q.out
  have hgq : (g : G ⧸ L) = q := Quotient.out_eq' q
  have hgn : g ∉ L := by
    intro hg
    apply hq
    rw [← hgq]
    exact QuotientGroup.eq.mpr (by simpa using L.inv_mem hg)
  let I := {t : G // orderOf t = 2 ∧ (t : G ⧸ L) = q}
  have hmem (t : I) : g⁻¹ * (t : G) ∈ L :=
    QuotientGroup.eq.mp (hgq.trans t.property.2.symm)
  let f (t : I) : L ⧸ (P : Subgroup G).subgroupOf L :=
    (⟨g⁻¹ * (t : G), hmem t⟩ : L)
  have hinj : Function.Injective f := by
    intro a b hab
    have hm := QuotientGroup.eq.mp hab
    change (g⁻¹ * (a : G))⁻¹ * (g⁻¹ * (b : G)) ∈ (P : Subgroup G) at hm
    have hai : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_left (by
      simpa [pow_two, a.property.1] using pow_orderOf_eq_one (a : G))
    have hbi : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_left (by
      simpa [pow_two, b.property.1] using pow_orderOf_eq_one (b : G))
    have haP : (a : G) ∉ (P : Subgroup G) := by
      intro ha
      have he : ((a : G) : G ⧸ L) = ((1 : G) : G ⧸ L) :=
        QuotientGroup.eq.mpr (by simpa using L.inv_mem (le_normalizer ha))
      exact hq (a.property.2.symm.trans he)
    apply Subtype.ext
    exact P.eq_of_involutions_mul_inv_mem_of_centralizer_le hcent haP
      (by simpa only [a.property.1] using pow_orderOf_eq_one (a : G))
      (by simpa only [b.property.1] using pow_orderOf_eq_one (b : G))
      (by simpa [mul_inv_rev, mul_assoc, hai, hbi] using hm)
  have hsurj : Function.Surjective f := by
    intro r
    induction r using Quotient.inductionOn with
    | h l =>
      have hgln : g * (l : G) ∉ L := by
        intro hh
        exact hgn (by simpa using L.mul_mem hh (L.inv_mem l.property))
      obtain ⟨t, ht, hgt⟩ := hcover (g * (l : G)) hgln
      have hlt : g⁻¹ * t ∈ L := by
        have hh := L.mul_mem l.property (le_normalizer hgt)
        simpa [mul_inv_rev, mul_assoc] using hh
      have htq : (t : G ⧸ L) = q :=
        (QuotientGroup.eq.mpr hlt).symm.trans hgq
      refine ⟨⟨t, ht, htq⟩, ?_⟩
      apply Eq.symm
      apply QuotientGroup.eq.mpr
      change (l : G)⁻¹ * (g⁻¹ * t) ∈ (P : Subgroup G)
      simpa [mul_inv_rev, mul_assoc] using hgt
  exact Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩

/-- The Suzuki–Feit bound from external Sylow-coset saturation and a nontrivial
normalizer quotient. The disjoint-product argument supplies the inequality. -/
public theorem card_sylow_le_of_cover (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hcover : ∀ g : G, g ∉ normalizer (P : Set G) →
      ∃ t : G, orderOf t = 2 ∧ g⁻¹ * t ∈ (P : Subgroup G))
    (hindex : 1 < (P : Subgroup G).relIndex (normalizer (P : Set G))) :
    Nat.card (Sylow 2 G) ≤ Nat.card P + 1 :=
  P.card_sylow_le_of_involution_cosets hcent hcover
    (P.card_involutions_normalizer_coset_of_cover hcent hcover) hindex

/-- The Suzuki–Feit counting bound for a nonnormal self-centralizing Sylow
two-subgroup with at least two involutions. -/
public theorem card_sylow_le_of_centralizer_le (P : Sylow 2 G)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (htwo : ∃ t u : P, orderOf t = 2 ∧ orderOf u = 2 ∧ t ≠ u) :
    Nat.card (Sylow 2 G) ≤ Nat.card P + 1 := by
  obtain ⟨hcover, hindex⟩ := P.involution_coset_saturation_of_centralizer_le hn hcent htwo
  exact P.card_sylow_le_of_cover hcent hcover hindex

end Sylow
