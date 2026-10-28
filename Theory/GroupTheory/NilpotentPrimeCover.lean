module
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.Fitting.Core
public import Theory.PPrimeCore
/-!
# Extracting a central prime cover from a nilpotent kernel

For a perfect group mapping onto a finite group with nilpotent kernel, kill
the kernel's characteristic p′-core. The surviving kernel is the image of
its p-core. If the ambient p-core is central, this gives a perfect central
p-cover. A prime divisor p of the original kernel remains a divisor of the
new kernel because the removed subgroup has order prime to p.

This extraction retains the actual quotient of the original group and needs
no quasithinness of that quotient. It supplies the defining-prime reduction
in the nonsemisimple branch of Aschbacher–Smith A.2.12, pp.35–36.
-/

public section
open Subgroup
namespace Theory.GroupTheory

private theorem nilpotent_prime_core_sup {F : Type*} [Group F] [Finite F]
    [Group.IsNilpotent F] (p : ℕ) [Fact p.Prime] :
    pCore p F ⊔ pPrimeCore p F = ⊤ := by
  apply top_unique
  rw [← fitting_eq_top_of_nilpotent F, fitting_eq_sup_pCore]
  apply iSup_le
  intro q
  have hq : q.val.val.Prime := Nat.prime_of_mem_primeFactors q.val.property
  let : Fact q.val.val.Prime := ⟨hq⟩
  by_cases he : q.val.val = p
  · simpa only [he] using (le_sup_left : pCore p F ≤ pCore p F ⊔ pPrimeCore p F)
  · apply le_trans _ le_sup_right
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := F)).exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun hd => he ((Nat.dvd_prime hq).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one).symm)).pow_right n

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] [Group.IsPerfect G]

omit [Finite Q] in
theorem exists_central_prime_cover_of_nilpotent_kernel
    (p : ℕ) [Fact p.Prime] (f : G →* Q) (hf : Function.Surjective f)
    (hnil : Group.IsNilpotent f.ker) (hpcentral : pCore p G ≤ center G) :
    ∃ (N : Subgroup G) (_ : N.Normal), Nat.Coprime p (Nat.card N) ∧
      ∃ c : PerfectCentralCovering.Cover (G ⧸ N) Q,
        IsPGroup p c.toMonoidHom.ker ∧
        (p ∣ Nat.card f.ker → p ∣ Nat.card c.toMonoidHom.ker) := by
  classical
  let F := f.ker
  let : Group.IsNilpotent F := hnil
  let N := (pPrimeCore p F).map F.subtype
  let : N.Normal := inferInstance
  have hNF : N ≤ F := map_subtype_le _
  have hNcop : Nat.Coprime p (Nat.card N) := by
    rw [card_map_of_injective F.subtype_injective]
    exact pPrimeCore_coprime_card
  let q := QuotientGroup.mk' N
  let g : (G ⧸ N) →* Q := QuotientGroup.lift N f hNF
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨q x, rfl⟩
  have hkg : g.ker = F.map q := by
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N x
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, he⟩
      change g (q y) = 1
      rw [← he]
      exact hz
  let P := (pCore p F).map F.subtype
  have hPcore : P ≤ pCore p G := le_sSup ⟨inferInstance, pCore_isPGroup.map F.subtype⟩
  have hPN : P ⊔ N = F := by
    change (pCore p F).map F.subtype ⊔ (pPrimeCore p F).map F.subtype = F
    rw [← Subgroup.map_sup, nilpotent_prime_core_sup p, ← MonoidHom.range_eq_map, range_subtype]
  have hNq : N.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hFP : F.map q = P.map q := by rw [← hPN, Subgroup.map_sup, hNq, sup_bot_eq]
  have hcentral : g.ker ≤ center (G ⧸ N) := by
    rw [hkg, hFP]
    rintro x ⟨y, hy, rfl⟩
    apply mem_center_iff.mpr
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact congrArg q (mem_center_iff.mp (hpcentral (hPcore hy)) a)
  let c : PerfectCentralCovering.Cover (G ⧸ N) Q :=
    { toMonoidHom := g, surjective := hg, isPerfect := inferInstance,
      ker_le_center := hcentral }
  refine ⟨N, inferInstance, hNcop, c, ?_, ?_⟩
  · change IsPGroup p g.ker
    rw [hkg, hFP]
    exact (pCore_isPGroup.map F.subtype).map q
  · intro hpdiv
    change p ∣ Nat.card g.ker
    rw [hkg]
    let r := q.subgroupMap F
    have hr : Function.Surjective r := q.subgroupMap_surjective F
    have hkr : r.ker = N.subgroupOf F := by
      ext x
      change (⟨q x, mem_map_of_mem q x.property⟩ : F.map q) = 1 ↔ (x : G) ∈ N
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    have hkc : Nat.Coprime p (Nat.card r.ker) := by
      rw [hkr, Nat.card_congr (subgroupOfEquivOfLe hNF).toEquiv]
      exact hNcop
    have hidx : r.ker.index = Nat.card (F.map q) := by
      rw [index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hr).toEquiv
    have hmul := r.ker.card_mul_index
    rw [hidx] at hmul
    rw [← hmul] at hpdiv
    exact (Fact.out : p.Prime).dvd_mul.mp hpdiv |>.resolve_left
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hkc)

end Theory.GroupTheory
