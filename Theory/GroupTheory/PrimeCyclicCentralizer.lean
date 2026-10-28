module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Prime subgroups with cyclic centralizers

If a prime-order subgroup R has cyclic centralizer, every Sylow subgroup
containing R is cyclic. Indeed a prime-order subgroup of the Sylow center
lies in C(R), so cyclic-subgroup uniqueness identifies it with R. The whole
Sylow subgroup therefore centralizes R. Conjugacy gives all Sylow subgroups
and the prime-rank bound.

In a finite solvable group, if R also centralizes every other prime core,
it centralizes the Fitting subgroup and thus lies in the p-core. This core
is cyclic, and its subgroups are normal in the ambient group.

These are the group-theoretic deductions in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.12, printed p.22. The proof
uses neither primitive-element recognition nor a cyclic-Sylow assumption.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem mem_of_pow_card_eq_one_cyclic [IsCyclic G] (H : Subgroup G)
    {x : G} (hx : x ^ Nat.card H = 1) : x ∈ H := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hsub : (H : Set G).toFinset ⊆ Finset.univ.filter (fun a : G => a ^ Nat.card H = 1) := by
    intro a ha
    simp only [Set.mem_toFinset] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : H)))
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    simpa [Set.toFinset_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      using IsCyclic.card_pow_eq_one_le (α := G) (Nat.card_pos (α := H)))
  apply Set.mem_toFinset.mp
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

private theorem eq_of_card_eq_of_le_cyclic (A B C : Subgroup G) [IsCyclic C]
    (hAC : A ≤ C) (hBC : B ≤ C) (hcard : Nat.card A = Nat.card B) : A = B := by
  apply eq_of_le_of_card_ge ?_ hcard.ge
  intro a ha
  have hBcard : Nat.card (B.subgroupOf C) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv
  have hpow : (⟨a, hAC ha⟩ : C) ^ Nat.card (B.subgroupOf C) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hBcard, ← hcard]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : A)))
  exact mem_of_pow_card_eq_one_cyclic (B.subgroupOf C) hpow

private theorem normal_of_le_cyclic_normal (A C : Subgroup G) [IsCyclic C] [C.Normal]
    (hAC : A ≤ C) : A.Normal := by
  constructor
  intro a ha g
  let c : C := ⟨g * a * g⁻¹, (inferInstance : C.Normal).conj_mem a (hAC ha) g⟩
  have hcard : Nat.card (A.subgroupOf C) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv
  apply mem_of_pow_card_eq_one_cyclic (A.subgroupOf C) (x := c)
  apply Subtype.ext
  change (g * a * g⁻¹) ^ Nat.card (A.subgroupOf C) = 1
  rw [hcard, ← MulAut.conj_apply, ← map_pow]
  have haone : a ^ Nat.card A = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : A)))
  rw [haone, map_one]

/-- A Sylow subgroup containing a prime subgroup with cyclic centralizer is cyclic. -/
private theorem cyclic_sylow_of_prime_centralizer {p : ℕ} [Fact p.Prime]
    (R : Subgroup G) (hR : Nat.card R = p)
    [IsCyclic (centralizer (R : Set G))]
    (S : Sylow p G) (hRS : R ≤ S) : IsCyclic S := by
  classical
  let C := centralizer (R : Set G)
  let : IsCyclic R := isCyclic_of_prime_card hR
  have hSCard : p ≤ Nat.card S := calc
    p = Nat.card R := hR.symm
    _ ≤ Nat.card S := card_le_of_le hRS
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp
    ((Fact.out : p.Prime).one_lt.trans_le hSCard)
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  have hZp : IsPGroup p (center S) := S.isPGroup'.to_subgroup (center S)
  obtain ⟨z₀, hz₀⟩ := exists_ne (1 : center S)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p
    ((hZp.dvd_orderOf hz₀).trans (_root_.orderOf_dvd_natCard z₀))
  let f : center S →* G := (S : Subgroup G).subtype.comp (center S).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  let B := (zpowers z).map f
  have hBcard : Nat.card B = p := by rw [card_map_of_injective hf, Nat.card_zpowers, hz]
  have hBC : B ≤ C := by
    rintro _ ⟨b, hb, rfl⟩
    intro a ha
    exact congrArg (fun s : S => (s : G))
      ((mem_center_iff.mp b.property) ⟨a, hRS ha⟩)
  have hRB : R = B := eq_of_card_eq_of_le_cyclic R B C
    (le_centralizer R) hBC (hR.trans hBcard.symm)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs a ha
    rw [hRB] at ha
    obtain ⟨b, _, rfl⟩ := ha
    exact (congrArg (fun t : S => (t : G))
      ((mem_center_iff.mp b.property) ⟨s, hs⟩)).symm
  exact isCyclic_of_le hSC

/-- A prime subgroup with cyclic centralizer forces all Sylow subgroups at that prime to be cyclic. -/
public theorem all_cyclic_sylow_of_prime_centralizer {p : ℕ} [Fact p.Prime]
    (R : Subgroup G) (hR : Nat.card R = p)
    [IsCyclic (centralizer (R : Set G))] (P : Sylow p G) : IsCyclic P := by
  have hpR : IsPGroup p R := IsPGroup.of_card (n := 1) (by simpa using hR)
  obtain ⟨S, hRS⟩ := hpR.exists_le_sylow
  let : IsCyclic S := cyclic_sylow_of_prime_centralizer R hR S hRS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let e : (S : Subgroup G) ≃* ((g • S : Sylow p G) : Subgroup G) :=
    equivMapOfInjective (S : Subgroup G) (MulAut.conj g).toMonoidHom
      (EquivLike.injective (MulAut.conj g))
  have he := e.isCyclic.mp (inferInstance : IsCyclic S)
  rwa [hg] at he

/-- A prime subgroup with cyclic centralizer bounds the ambient prime rank by one. -/
public theorem primeRank_le_one_of_prime_centralizer {p : ℕ} [Fact p.Prime]
    (R : Subgroup G) (hR : Nat.card R = p)
    [IsCyclic (centralizer (R : Set G))] : primeRank p G ≤ 1 := by
  let S : Sylow p G := Classical.choice inferInstance
  exact S.primeRank_le_one_of_isCyclic (all_cyclic_sylow_of_prime_centralizer R hR S)

/-- A p-subgroup of the Fitting subgroup belongs to the p-core. -/
public theorem le_pCore_of_le_fitting {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hp : IsPGroup p P) (hP : P ≤ fittingSubgroup G) :
    P ≤ pCore p G := by
  let F := fittingSubgroup G
  let Q := P.subgroupOf F
  have hQ : IsPGroup p Q := hp.of_equiv (subgroupOfEquivOfLe hP).symm
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have hmap : Q.map F.subtype = P := map_subgroupOf_eq_of_le hP
  rw [← hmap]
  exact (map_mono hS).trans (S.map_le_pCore inferInstance inferInstance p)

/-- The Fitting argument for a prime subgroup with cyclic centralizer. -/
public theorem prime_normal_of_cyclic_centralizer_of_other_cores
    (hsolv : Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    (R : Subgroup G) (hR : Nat.card R = p)
    [IsCyclic (centralizer (R : Set G))]
    (hother : ∀ q : ℕ, q.Prime → q ≠ p → R ≤ centralizer (pCore q G : Set G)) :
    R.Normal := by
  have hpR : IsPGroup p R := IsPGroup.of_card (n := 1) (by simpa using hR)
  have hSyl := all_cyclic_sylow_of_prime_centralizer R hR
  have hfit : R ≤ centralizer (fittingSubgroup G : Set G) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    by_cases he : q.val.val = p
    · rw [he]
      exact pSubgroup_le_centralizer_pCore_of_cyclic_sylow_fitting hpR hSyl
    · exact hother q.val.val (Nat.prime_of_mem_primeFactors q.val.property) he
  have hcore : R ≤ pCore p G := le_pCore_of_le_fitting R hpR
    (hfit.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv))
  let S : Sylow p G := Classical.choice inferInstance
  let : IsCyclic S := hSyl S
  let : IsCyclic (pCore p G) := isCyclic_of_le (fitting_pCore_le_sylow S)
  exact normal_of_le_cyclic_normal R (pCore p G) hcore

end Subgroup
