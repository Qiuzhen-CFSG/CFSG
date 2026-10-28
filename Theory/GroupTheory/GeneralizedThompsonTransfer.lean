module

public import Theory.GroupTheory.FusionInvariantTransfer
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.IntervalCases

/-!
# Generalized Thompson transfer

For a character of H constant on the conjugate powers of g, the orbit-product
transfer formula gives transfer(g) = character(g)^[G:H]. If the order of g
is coprime to the index and its character value is nontrivial, this detects
g outside the derived subgroup. Applying this to H → H/K proves generalized
Thompson transfer with relative normality K ◁ H and the literal quotient map.
For involutions, only fusion of g itself needs to be checked.

An ambient involution having no conjugate in an index-two subgroup Q of a
Sylow two-subgroup P can first be conjugated into P. The quotient character
P → P/Q then has nontrivial transfer on the involution. Its kernel has a
two-group quotient, so it contains the two-residual and detects the involution
outside that residual. No restriction on normal index-two subgroups is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.1.36–37, printed pp.30–31. The evaluation is
supplied by `Theory.GroupTheory.FusionInvariantTransfer`, using Mathlib's
ordinary transfer and its orbit-product formula.
-/

public section

namespace MonoidHom

/-- Transfer detects a nontrivial character value when the element order is coprime to the index. -/
theorem transfer_ne_one_of_conjugate_powers
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (character : H →* A) (element : H)
    (hcop : Nat.Coprime (orderOf element) H.index)
    (hne : character element ≠ 1)
    (hrespect : ∀ (power : ℕ) (other : H),
      IsConj (((element ^ power) : H) : G) (other : G) →
        character other = character (element ^ power)) :
    character.transfer (element : G) ≠ 1 := by
  rw [character.transfer_apply_eq_pow_of_conjugate_powers element hrespect]
  intro h
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := element) hcop.symm
  apply hne
  rw [← hm, map_pow, map_pow, h, one_pow]

/-- A character respecting conjugate powers detects an element outside the ambient derived subgroup. -/
theorem not_mem_commutator_of_conjugate_powers
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (character : H →* A) (element : H)
    (hcop : Nat.Coprime (orderOf element) H.index)
    (hne : character element ≠ 1)
    (hrespect : ∀ (power : ℕ) (other : H),
      IsConj (((element ^ power) : H) : G) (other : G) →
        character other = character (element ^ power)) :
    (element : G) ∉ _root_.commutator G := by
  intro h
  exact character.transfer_ne_one_of_conjugate_powers element hcop hne hrespect
    (Abelianization.commutator_subset_ker character.transfer h)

private theorem respect_powers_of_order_two
    {G A : Type*} [Group G] [CommGroup A]
    {H : Subgroup G} (character : H →* A) (element : H)
    (horder : orderOf element = 2)
    (hrespect : ∀ other : H, IsConj (element : G) (other : G) →
      character other = character element)
    (power : ℕ) (other : H)
    (hconj : IsConj (((element ^ power) : H) : G) (other : G)) :
    character other = character (element ^ power) := by
  have hreduce : element ^ power = element ^ (power % 2) := by
    simpa only [horder] using (pow_mod_orderOf element power).symm
  rw [hreduce] at hconj ⊢
  have hbound : power % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize hremainder : power % 2 = remainder at hconj ⊢ hbound
  interval_cases remainder
  · have hother : other = 1 := Subtype.coe_injective
      (isConj_one_right.mp (by simpa using hconj))
    simp [hother]
  · simp only [pow_one] at hconj ⊢
    exact hrespect other hconj

/-- For an involution, invariance on its own ambient fusion class suffices to detect transfer. -/
theorem transfer_ne_one_of_order_two
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (character : H →* A) (element : H)
    (hcop : Nat.Coprime 2 H.index) (horder : orderOf element = 2)
    (hne : character element ≠ 1)
    (hrespect : ∀ other : H, IsConj (element : G) (other : G) →
      character other = character element) :
    character.transfer (element : G) ≠ 1 :=
  character.transfer_ne_one_of_conjugate_powers element (horder ▸ hcop) hne
    (respect_powers_of_order_two character element horder hrespect)

/-- An odd-index character detects an involution outside the ambient derived subgroup. -/
theorem not_mem_commutator_of_order_two
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (character : H →* A) (element : H)
    (hcop : Nat.Coprime 2 H.index) (horder : orderOf element = 2)
    (hne : character element ≠ 1)
    (hrespect : ∀ other : H, IsConj (element : G) (other : G) →
      character other = character element) :
    (element : G) ∉ _root_.commutator G := by
  intro h
  exact character.transfer_ne_one_of_order_two element hcop horder hne hrespect
    (Abelianization.commutator_subset_ker character.transfer h)

end MonoidHom

namespace Subgroup

/-- Generalized Thompson transfer for a p-element and a relatively normal subgroup with abelian quotient. -/
theorem not_mem_commutator_of_conjugate_zpowers
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} {H : Subgroup G} (K : Subgroup H) [K.Normal]
    [IsMulCommutative (H ⧸ K)] (element : H)
    (hcop : Nat.Coprime p H.index)
    (hp : ∃ n : ℕ, orderOf element = p ^ n) (hne : element ∉ K)
    (hrespect : ∀ (power : ℤ) (other : H),
      IsConj (((element ^ power) : H) : G) (other : G) →
        (element ^ power)⁻¹ * other ∈ K) :
    (element : G) ∉ _root_.commutator G := by
  let : CommGroup (H ⧸ K) := { (inferInstance : Group (H ⧸ K)) with
    mul_comm := mul_comm' }
  apply (QuotientGroup.mk' K).not_mem_commutator_of_conjugate_powers element
  · obtain ⟨n, hn⟩ := hp
    rw [hn]
    exact hcop.pow_left n
  · exact fun h => hne ((QuotientGroup.eq_one_iff element).mp h)
  · intro power other hconj
    apply ((QuotientGroup.mk'_eq_mk' K).mpr ?_).symm
    refine ⟨(element ^ power)⁻¹ * other, ?_, by simp⟩
    simpa only [zpow_natCast] using hrespect (power : ℤ) other (by simpa only [zpow_natCast] using hconj)

/-- The involution specialization of generalized Thompson transfer. -/
theorem not_mem_commutator_of_involution_fusion
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (K : Subgroup H) [K.Normal]
    [IsMulCommutative (H ⧸ K)] (element : H)
    (hcop : Nat.Coprime 2 H.index) (horder : orderOf element = 2)
    (hne : element ∉ K)
    (hrespect : ∀ other : H, IsConj (element : G) (other : G) →
      element⁻¹ * other ∈ K) :
    (element : G) ∉ _root_.commutator G := by
  let : CommGroup (H ⧸ K) := { (inferInstance : Group (H ⧸ K)) with
    mul_comm := mul_comm' }
  apply (QuotientGroup.mk' K).not_mem_commutator_of_order_two element hcop horder
  · exact fun h => hne ((QuotientGroup.eq_one_iff element).mp h)
  · intro other hconj
    exact ((QuotientGroup.mk'_eq_mk' K).mpr
      ⟨element⁻¹ * other, hrespect other hconj, by simp⟩).symm

end Subgroup
namespace Sylow

open Subgroup

/-- Thompson transfer: an ambient involution with no conjugate in Q lies outside the two-residual. -/
theorem involution_not_mem_twoResidual_of_no_conjugate
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (Q : Subgroup P) (hQ : Q.index = 2)
    (u : G) (hu : orderOf u = 2)
    (hno : ∀ v : P, IsConj u (v : G) → v ∉ Q) :
    u ∉ pResidual 2 G := by
  let : Q.Normal := Q.normal_of_index_eq_two hQ
  have hcard : Nat.card (P ⧸ Q) = 2 := hQ
  let : IsCyclic (P ⧸ Q) := isCyclic_of_prime_card hcard
  let : CommGroup (P ⧸ Q) := IsCyclic.commGroup
  let character := QuotientGroup.mk' Q
  have hcyc : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨R, hR⟩ := hcyc.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G R P
  have hv : MulAut.conj a u ∈ (P : Subgroup G) := by
    rw [← ha]
    exact mem_map_of_mem _ (hR (mem_zpowers u))
  let v : P := ⟨MulAut.conj a u, hv⟩
  have hconj : IsConj u (v : G) := isConj_iff.mpr ⟨a, rfl⟩
  have hvorder : orderOf v = 2 := by
    rw [← Subgroup.orderOf_coe v]
    exact (orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective u).trans hu
  have hnontrivial (x : P) (hx : IsConj u (x : G)) : character x ≠ 1 := by
    exact fun h => hno x hx ((QuotientGroup.eq_one_iff x).mp h)
  have hrespect (x : P) (hx : IsConj (v : G) (x : G)) : character x = character v := by
    obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : P ⧸ Q)).mp hcard
    exact (hunique _ (hnontrivial x (hconj.trans hx))).trans
      (hunique _ (hnontrivial v hconj)).symm
  have hcop : Nat.Coprime 2 (P : Subgroup G).index :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr P.not_dvd_index
  have htransfer := character.transfer_ne_one_of_order_two v hcop hvorder
    (hnontrivial v hconj) hrespect
  have hA : IsPGroup 2 (P ⧸ Q) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hres : pResidual 2 G ≤ character.transfer.ker :=
    sInf_le ⟨inferInstance, (hA.to_subgroup character.transfer.range).of_equiv
      (QuotientGroup.quotientKerEquivRange character.transfer).symm⟩
  intro huR
  apply htransfer
  exact (isConj_iff_eq.mp (character.transfer.map_isConj hconj)).symm.trans (hres huR)

end Sylow
