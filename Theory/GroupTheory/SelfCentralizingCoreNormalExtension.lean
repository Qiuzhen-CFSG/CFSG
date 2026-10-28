module
public import Theory.GroupTheory.CoprimeSelfCentralizingAction
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Quasithin.EvenCharacteristic

/-!
# Characteristic-p normal extensions detected by a faithful seed

A finite group with a normal characteristic-p subgroup N is of
characteristic p if C_G(N) is a p-group. For an element of prime order
q different from p centralizing O_p(N), the coprime self-centralizing
normal-subgroup lemma makes it centralize N. The centralizer assumption
then excludes it. Cauchy's theorem gives the required p-group centralizer.

For the normalized product KD, suppose N_K(S)=S and D normalizes both
K and S. An element centralizing S has a product expression in SD.
If S centralizes Z≤S and D acts faithfully on Z, its D component is
trivial. This supplies the normal-extension criterion for KD.

Source application: the right parabolic K₁SD_L in Aschbacher--Smith
6.1.5, printed p.667 (`refs/quasithin.pdf`).
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem prime_order_core_centralizer_of_normal
    (N : Subgroup G) [N.Normal]
    (hN : centralizer (pCore p N : Set N) ≤ pCore p N)
    (hC : IsPGroup p (centralizer (N : Set G)))
    (x : centralizer (N.pCoreIn p : Set G))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (ho : orderOf x = q) : False := by
  let A := zpowers (x : G)
  have hAc : Nat.card A = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ho]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pCore p N)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := p) (G := N)).exists_card_eq
    rw [hAc,hk]
    exact ((hq.coprime_iff_not_dvd).mpr
      (fun hd => hqp ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left hq.ne_one))).pow_right k
  have hfix : A ≤ centralizer (N.pCoreIn p : Set G) := zpowers_le.mpr x.property
  have hAN : A ≤ centralizer (N : Set G) :=
    centralizes_of_coprime_of_selfCentralizing_normal A N (pCore p N) hcop
      le_normalizer_of_normal hN hfix
  obtain ⟨k,hk⟩ := hC.exists_orderOf_dvd_pow ⟨(x : G),hAN (mem_zpowers _)⟩
  have hd : q ∣ p ^ k := by
    simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ho] using hk
  exact hqp ((Nat.dvd_prime Fact.out).mp (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)

/-- Normal characteristic-p groups extend when their centralizer is a p-group. -/
theorem core_selfCentralizing_of_normal_of_centralizer_isPGroup
    (N : Subgroup G) [N.Normal]
    (hN : centralizer (pCore p N : Set N) ≤ pCore p N)
    (hC : IsPGroup p (centralizer (N : Set G))) :
    centralizer (pCore p G : Set G) ≤ pCore p G := by
  have hCp : IsPGroup p (centralizer (N.pCoreIn p : Set G)) := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro q hq
    obtain ⟨hqprime,hqdvd,_⟩ := Nat.mem_primeFactors.mp hq
    by_cases he : q = p
    · subst q
      exact Nat.mem_primeFactors.mpr ⟨Fact.out,dvd_rfl,(Fact.out : p.Prime).ne_zero⟩
    · obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card'
        (G := centralizer (N.pCoreIn p : Set G)) q (hp := ⟨hqprime⟩) hqdvd
      exact (prime_order_core_centralizer_of_normal N hN hC x hqprime he hx).elim
  have hQ : N.pCoreIn p ≤ pCore p G :=
    le_sSup ⟨inferInstanceAs (((pCore p N).map N.subtype).Normal),pCore_isPGroup.map _⟩
  have hp : IsPGroup p (centralizer (pCore p G : Set G)) :=
    hCp.to_le (centralizer_le hQ)
  exact le_sSup ⟨inferInstance,hp⟩

omit [Finite G] in
/-- A faithful seed detects the centralizer in a normalized product with a
self-normalizing common subgroup. -/
theorem inf_centralizer_sup_le_of_faithful_seed_of_self_normalizer
    (K S D Z : Subgroup G)
    (hDK : D ≤ normalizer (K : Set G))
    (hDS : D ≤ normalizer (S : Set G))
    (hB : K ⊓ normalizer (S : Set G) = S)
    (hZS : Z ≤ S) (hSZ : S ≤ centralizer (Z : Set G))
    (hfaith : D ⊓ centralizer (Z : Set G) = ⊥) :
    (K ⊔ D) ⊓ centralizer (S : Set G) ≤ S := by
  intro x hx
  have hxprod : x ∈ (K : Set G) * (D : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K D hDK]
    exact hx.1
  obtain ⟨k,hk,d,hd,hkd⟩ := hxprod
  have hkN : k ∈ normalizer (S : Set G) := by
    have he : k = x * d⁻¹ := eq_mul_inv_iff_mul_eq.mpr hkd
    rw [he]
    exact (normalizer (S : Set G)).mul_mem
      ((centralizer_le_normalizer _) hx.2) ((normalizer (S : Set G)).inv_mem (hDS hd))
  have hkS : k ∈ S := hB ▸ (show k ∈ K ⊓ normalizer (S : Set G) from ⟨hk,hkN⟩)
  have hdZ : d ∈ centralizer (Z : Set G) := by
    have he : d = k⁻¹ * x := by rw [←hkd]; group
    rw [he]
    exact (centralizer (Z : Set G)).mul_mem
      ((centralizer (Z : Set G)).inv_mem (hSZ hkS)) ((centralizer_le hZS) hx.2)
  have hd1 : d = 1 := mem_bot.mp (hfaith ▸ (show d ∈ D ⊓ centralizer (Z : Set G) from ⟨hd,hdZ⟩))
  have hxeq : x = k := by simpa only [hd1,mul_one] using hkd.symm
  exact hxeq.symm ▸ hkS

/-- Characteristic p passes to the normalizing seed-faithful extension. -/
theorem core_selfCentralizing_sup_of_faithful_seed
    (K S D Z : Subgroup G)
    (hK : centralizer (pCore p K : Set K) ≤ pCore p K)
    (hS : IsPGroup p S) (hSK : S ≤ K)
    (hDK : D ≤ normalizer (K : Set G))
    (hDS : D ≤ normalizer (S : Set G))
    (hB : K ⊓ normalizer (S : Set G) = S)
    (hZS : Z ≤ S) (hSZ : S ≤ centralizer (Z : Set G))
    (hfaith : D ⊓ centralizer (Z : Set G) = ⊥) :
    centralizer (pCore p (K ⊔ D : Subgroup G) : Set (K ⊔ D : Subgroup G)) ≤
      pCore p (K ⊔ D : Subgroup G) := by
  let P := K ⊔ D
  let N := K.subgroupOf P
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hDK)
  have hN : centralizer (pCore p N : Set N) ≤ pCore p N :=
    (Theory.Quasithin.centralizer_pCore_le_iff p
      (subgroupOfEquivOfLe (show K ≤ P from le_sup_left))).mpr hK
  apply core_selfCentralizing_of_normal_of_centralizer_isPGroup N hN
  apply (show IsPGroup p (S.subgroupOf P) from hS.comap_subtype).to_le
  intro x hx
  have hxS : (x : G) ∈ centralizer (S : Set G) := by
    intro s hs
    exact congrArg P.subtype (hx ⟨s,(show K ≤ P from le_sup_left) (hSK hs)⟩ (hSK hs))
  exact inf_centralizer_sup_le_of_faithful_seed_of_self_normalizer K S D Z
    hDK hDS hB hZS hSZ hfaith ⟨x.property,hxS⟩
end Subgroup
