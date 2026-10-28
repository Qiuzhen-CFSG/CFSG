module

public import Theory.PGroupCore
public import Theory.GroupTheory.SymmetricThreeQuotientInverter
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-!
# An outside-involution cover by a three-normalizer

Let a finite group have a Sylow two-subgroup T of index three and two-core H.
If N/H is symmetric of degree three, every involution of T outside H is
conjugate within T into the normalizer of any supplied subgroup of order three.
If H has index two in T, an outside element t inverting a generator q gives
N_T(⟨q⟩) = C_H(q) ⊔ ⟨t⟩, with the centralizer restricted to T; t normalizes
that centralizer.

An outside involution inverts some subgroup of order three by the quotient
lifting theorem. Both three-subgroups are Sylow subgroups. The complement
factorization N = T⟨q⟩ removes the three-factor from a Sylow conjugator,
so the resulting element conjugacy takes place in T. A core element
normalizing ⟨q⟩ centralizes it: its commutator lies in the disjoint subgroups
H and ⟨q⟩. The two cosets of H in T then give the normalizer formula.

Source: Janko–Thompson (1970), printed p.392 (PDF p.8), the claim that every
involution outside H is T-conjugate into N_T(Q). The local source is
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
The proof uses only general group theory and has no recognition dependencies.
-/

open scoped Pointwise
namespace Subgroup
variable {N : Type*} [Group N]

private theorem three_sylow [Finite N] (T : Sylow 2 N) (hi : (T : Subgroup N).index = 3)
    (Q : Subgroup N) (hQ : Nat.card Q = 3) :
    ∃ P : Sylow 3 N, (P : Subgroup N) = Q := by
  have hcard : Nat.card N = 3 * Nat.card T := by
    simpa only [hi] using (T : Subgroup N).index_mul_card.symm
  have hind : Q.index = Nat.card T := by
    have h := Q.card_mul_index
    rw [hQ, hcard] at h
    omega
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact ⟨(IsPGroup.of_card (p := 3) (n := 1) (by simpa using hQ)).toSylow
    (by rw [hind]; exact Nat.prime_three.coprime_iff_not_dvd.mp hcop), rfl⟩

private theorem sylow_conjugator_in_two [Finite N] (T : Sylow 2 N)
    (hi : (T : Subgroup N).index = 3) (P R : Sylow 3 N)
    (hP : Nat.card P = 3) : ∃ s : T, (s : N) • P = R := by
  have hc : (T : Subgroup N).IsComplement' (P : Subgroup N) := by
    apply isComplement'_of_coprime
    · rw [hP, ← hi]
      exact (T : Subgroup N).card_mul_index
    · obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
      rw [hP, hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P R
  obtain ⟨⟨s, r⟩, hsr, _⟩ := hc.existsUnique g
  have hr : (r : N) • P = P :=
    Sylow.smul_eq_iff_mem_normalizer.mpr ((P : Subgroup N).le_normalizer r.property)
  refine ⟨s, ?_⟩
  rw [← hsr, mul_smul, hr] at hg
  exact hg

/-- Every outside involution is conjugate inside the supplied Sylow subgroup
into the normalizer of the supplied three-subgroup. -/
public theorem outside_involution_conj_normalizer [Finite N] (T : Sylow 2 N)
    (hi : (T : Subgroup N).index = 3)
    (he : Nonempty ((N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3)))
    (q : N) (hq : orderOf q = 3)
    (u : T) (hu : orderOf u = 2) (huH : (u : N) ∉ pCore 2 N) :
    ∃ w : (normalizer (zpowers q : Set N)).comap (T : Subgroup N).subtype,
      IsConj u (w : T) := by
  obtain ⟨Q, hQ, hinv⟩ := exists_inverted_three_of_symmetric_three_quotient
    (pCore 2 N) pCore_isPGroup he (u : N) ((orderOf_coe u).trans hu) huH
  obtain ⟨P, hP⟩ := three_sylow T hi (zpowers q) ((Nat.card_zpowers q).trans hq)
  obtain ⟨R, hR⟩ := three_sylow T hi Q hQ
  have huR : (u : N) ∈ normalizer (R : Set N) := by
    change (u : N) ∈ normalizer ((R : Subgroup N) : Set N)
    rw [hR]
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [hinv x hx]
      exact Q.inv_mem hx
    · intro hx
      have hx' := Q.inv_mem (show (u : N) * ((u : N) * x * (u : N)⁻¹) *
          (u : N)⁻¹ ∈ Q by rw [hinv _ hx]; exact Q.inv_mem hx)
      have hu2 : (u : N) * (u : N) = 1 := by
        simpa only [pow_two, orderOf_coe, hu] using pow_orderOf_eq_one (u : N)
      have heq : (u : N) * ((u : N) * x * (u : N)⁻¹) * (u : N)⁻¹ = x := by
        calc
          _ = ((u : N) * (u : N)) * x * ((u : N) * (u : N))⁻¹ := by group
          _ = x := by rw [hu2]; simp
      exact Q.inv_mem_iff.mp (heq ▸ hx')
  obtain ⟨s, hs⟩ := sylow_conjugator_in_two T hi P R (by
    rw [hP, Nat.card_zpowers, hq])
  have hw : ((s : N)⁻¹ * (u : N) * (s : N)) • P = P := by
    rw [mul_smul, mul_smul, hs, Sylow.smul_eq_iff_mem_normalizer.mpr huR, ← hs,
      inv_smul_smul]
  have hwmem : s⁻¹ * u * s ∈ (normalizer (zpowers q : Set N)).comap
      (T : Subgroup N).subtype := by
    change (s : N)⁻¹ * (u : N) * (s : N) ∈ normalizer (zpowers q : Set N)
    rw [← hP]
    exact Sylow.smul_eq_iff_mem_normalizer.mp hw
  exact ⟨⟨s⁻¹ * u * s, hwmem⟩, isConj_iff.mpr ⟨s⁻¹, by simp⟩⟩

private theorem core_normalizer_centralizes (q : N) (hq : orderOf q = 3)
    (x : N) (hxH : x ∈ pCore 2 N) (hxN : x ∈ normalizer (zpowers q : Set N)) :
    x ∈ centralizer ({q} : Set N) := by
  have hdis : Disjoint (pCore 2 N) (zpowers q) :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup
      (IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hq))
  have hcH : x * q * x⁻¹ * q⁻¹ ∈ pCore 2 N := by
    have h := (pCore 2 N).mul_mem hxH
      ((inferInstance : (pCore 2 N).Normal).conj_mem x⁻¹ ((pCore 2 N).inv_mem hxH) q)
    simpa only [mul_assoc] using h
  have hcQ : x * q * x⁻¹ * q⁻¹ ∈ zpowers q :=
    (zpowers q).mul_mem ((hxN q).mp (mem_zpowers q)) ((zpowers q).inv_mem (mem_zpowers q))
  have heq := disjoint_def.mp hdis hcH hcQ
  exact mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp heq))

private theorem centralizer_le_three_normalizer (q : N) :
    centralizer ({q} : Set N) ≤ normalizer (zpowers q : Set N) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (x * q * x⁻¹) = zpowers q
  rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]

/-- The three-normalizer in the Sylow subgroup is generated by its two-core
centralizer and any supplied outside inverter. -/
public theorem index_three_normalizer_eq (T : Sylow 2 N)
    (hindex : (pCore 2 N).relIndex (T : Subgroup N) = 2)
    (q : N) (hq : orderOf q = 3) (t : T) (htH : (t : N) ∉ pCore 2 N)
    (hinv : (t : N) * q * (t : N)⁻¹ = q⁻¹) :
    (normalizer (zpowers q : Set N)).comap (T : Subgroup N).subtype =
      ((pCore 2 N ⊓ centralizer ({q} : Set N)).comap (T : Subgroup N).subtype) ⊔
        zpowers t := by
  let D := (pCore 2 N ⊓ centralizer ({q} : Set N)).comap (T : Subgroup N).subtype
  let S := (normalizer (zpowers q : Set N)).comap (T : Subgroup N).subtype
  have hDS : D ≤ S := fun x hx => centralizer_le_three_normalizer q hx.2
  have htS : t ∈ S := by
    change (t : N) ∈ normalizer (zpowers q : Set N)
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers ((t : N) * q * (t : N)⁻¹) = zpowers q
    rw [hinv, zpowers_inv]
  apply le_antisymm
  · intro x hx
    change x ∈ D ⊔ zpowers t
    by_cases hxH : (x : N) ∈ pCore 2 N
    · exact mem_sup_left ⟨hxH, core_normalizer_centralizes q hq x hxH hx⟩
    · have hxt : (x : N) * (t : N) ∈ pCore 2 N :=
        (mul_mem_iff_of_index_two (H := (pCore 2 N).subgroupOf (T : Subgroup N))
          hindex).mpr (iff_of_false hxH htH)
      have hxtD : x * t ∈ D :=
        ⟨hxt, core_normalizer_centralizes q hq _ hxt (S.mul_mem hx htS)⟩
      have hm := (D ⊔ zpowers t).mul_mem (mem_sup_left hxtD)
        (mem_sup_right ((zpowers t).inv_mem (mem_zpowers t)))
      simpa using hm
  · exact sup_le hDS (zpowers_le.mpr htS)

/-- The supplied outside inverter normalizes the two-core centralizer. -/
public theorem inverter_mem_normalizer_core_centralizer (T : Sylow 2 N)
    (q : N) (hq : orderOf q = 3) (t : T)
    (hinv : (t : N) * q * (t : N)⁻¹ = q⁻¹) :
    t ∈ normalizer
      (((pCore 2 N ⊓ centralizer ({q} : Set N)).comap
        (T : Subgroup N).subtype : Subgroup T) : Set T) := by
  let H := (pCore 2 N).comap (T : Subgroup N).subtype
  let S := (normalizer (zpowers q : Set N)).comap (T : Subgroup N).subtype
  have hD : (pCore 2 N ⊓ centralizer ({q} : Set N)).comap
      (T : Subgroup N).subtype = H ⊓ S := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, centralizer_le_three_normalizer q hx.2⟩
    · intro hx
      exact ⟨hx.1, core_normalizer_centralizes q hq x hx.1 hx.2⟩
  have htS : t ∈ S := by
    change (t : N) ∈ normalizer (zpowers q : Set N)
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers ((t : N) * q * (t : N)⁻¹) = zpowers q
    rw [hinv, zpowers_inv]
  rw [hD]
  exact inf_normalizer_le_normalizer_inf
    ⟨by rw [H.normalizer_eq_top]; trivial, S.le_normalizer htS⟩

/-- The outside-involution normalizer cover, including the normalizer formula
and invariance of the core centralizer. No order hypothesis on the supplied
inverter t is necessary. -/
public theorem sylow_index_three_normalizer_cover [Finite N] (T : Sylow 2 N)
    (hi : (T : Subgroup N).index = 3)
    (hindex : (pCore 2 N).relIndex (T : Subgroup N) = 2)
    (he : Nonempty ((N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3)))
    (q : N) (hq : orderOf q = 3) (t : T) (htH : (t : N) ∉ pCore 2 N)
    (hinv : (t : N) * q * (t : N)⁻¹ = q⁻¹) :
    let D := (pCore 2 N ⊓ centralizer ({q} : Set N)).comap (T : Subgroup N).subtype
    let L := D ⊔ zpowers t
    t ∈ normalizer (D : Set T) ∧
      (normalizer (zpowers q : Set N)).comap (T : Subgroup N).subtype = L ∧
      ∀ u : T, orderOf u = 2 → (u : N) ∉ pCore 2 N →
        ∃ w : L, IsConj u (w : T) := by
  dsimp only
  refine ⟨inverter_mem_normalizer_core_centralizer T q hq t hinv,
    index_three_normalizer_eq T hindex q hq t htH hinv, ?_⟩
  intro u hu huH
  obtain ⟨w, hw⟩ := outside_involution_conj_normalizer T hi he q hq u hu huH
  exact ⟨⟨w, (index_three_normalizer_eq T hindex q hq t htH hinv) ▸ w.property⟩, hw⟩

end Subgroup
