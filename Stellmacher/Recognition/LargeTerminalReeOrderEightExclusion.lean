module

public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalFiveNormalizerData
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The involution supplied by an order-eight squaring lift

Write Q for the second local core and F for its cyclic five-fixed subgroup.
A local normalizer of the five-subgroup preserves F, so its square centralizes
F. If a squaring lift b has fourth power z, and t generates F with t² = z,
then b²t⁻¹ is an involution outside Q which inverts the five-subgroup and
centralizes F.

This records a necessary consequence of the remaining order-eight case.
It does not exclude that case: the five-fixed conjugate-geometry theorem
concerns involutions inside Q centralizing the five-subgroup, whereas the
involution constructed here lies outside Q and inverts it.

Source: Thompson VI, pp.629–630, and Shinoda (1975), pp.81–83, for the
terminal local recognition problem. The calculation below is intrinsic
group arithmetic and does not assume a split extension or a Ree model.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

private theorem square_squaring_inverts
    {G : Type*} [Group G] (A : Subgroup G) (hA : Nat.card A = 5)
    (b : G) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) :
    ∀ c ∈ A, b ^ 2 * c * (b ^ 2)⁻¹ = c⁻¹ := by
  intro c hc
  have hc5 : c ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ : A))
    rw [hA] at h
    exact congrArg Subtype.val h
  have hpow : MulAut.conj (b ^ 2) c = c ^ 4 := by
    rw [map_pow, pow_two, MulAut.mul_apply]
    change MulAut.conj b (b * c * b⁻¹) = _
    rw [hb c hc, map_pow]
    change (b * c * b⁻¹) ^ 2 = _
    rw [hb c hc, ← pow_mul]
  change MulAut.conj (b ^ 2) c = _
  rw [hpow]
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using hc5

/-- Inside the normal two-core, normalizing the five-subgroup is the same
as centralizing it. -/
public theorem LargeTerminalContext.five_normalizer_inter_core_le_centralizer
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hA : Nat.card A = 5) (hAP : A ≤ ctx.second) :
    twoCoreIn ctx.second ⊓ normalizer (A : Set G) ≤ centralizer (A : Set G) := by
  let Q := twoCoreIn ctx.second
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map ctx.second.subtype
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hd : Disjoint Q A := hQp.disjoint_of_coprime hAp (by decide)
  have hAQ : A ≤ normalizer (Q : Set G) := hAP.trans
    ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
      (twoCoreIn_normal ctx.second))
  rw [← commutator_eq_bot_iff_le_centralizer]
  apply bot_unique
  apply le_trans _ hd.le_bot
  exact le_inf ((commutator_mono inf_le_left le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hAQ))
    (le_normalizer_iff_commutator_le_right.mp inf_le_right)

/-- The square of a local five-normalizer element centralizes the cyclic
fixed subgroup of order four. This does not assert that the element itself
centralizes that subgroup. -/
public theorem LargeTerminalContext.five_normalizer_square_centralizes_cyclic_fixed
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (b : G) (hbP : b ∈ ctx.second) (hbN : b ∈ normalizer (A : Set G)) :
    b ^ 2 ∈ centralizer
      ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  let Q := twoCoreIn ctx.second
  let F := (centralizer (A : Set G)).subgroupOf Q
  let H := Q ⊓ centralizer (A : Set G)
  have hFH : F.map Q.subtype = H := by rw [subgroupOf_map_subtype, inf_comm]
  let _ : IsCyclic F := hcyc
  let _ : IsCyclic H := hFH ▸
    (F.equivMapOfInjective Q.subtype Q.subtype_injective).isCyclic.mp inferInstance
  have hH : Nat.card H = 4 := by
    rw [← hFH, card_map_of_injective Q.subtype_injective]
    exact hcard
  have hAut : Nat.card (MulAut H) = 2 := by
    rw [IsCyclic.card_mulAut, hH]
    decide
  have hQ : ctx.second ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
      (twoCoreIn_normal ctx.second)
  have hbH : b ∈ normalizer (H : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hQ hbP,
      normalizer_le_normalizer_centralizer A hbN⟩
  have ha2 := pow_card_eq_one' (x := H.normalizerMonoidHom ⟨b, hbH⟩)
  rw [hAut, ← map_pow] at ha2
  apply mem_centralizer_iff.mpr
  intro t ht
  have he := congrArg (fun f : MulAut H => (f ⟨t, ht⟩ : G)) ha2
  change b ^ 2 * t * (b ^ 2)⁻¹ = t at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The remaining central fourth power produces a specific inverting
involution outside the core. Its existence alone is not a contradiction. -/
public theorem LargeTerminalContext.order_eight_squaring_inverting_involution
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : G) (hbP : b ∈ ctx.second) (hbN : b ∈ normalizer (A : Set G))
    (hb4 : b ^ 4 = z) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) :
    ∃ t y : G,
      t ∈ twoCoreIn ctx.second ∧ t ∈ centralizer (A : Set G) ∧
      t ∉ ctx.firstResidual ∧ orderOf t = 4 ∧ t ^ 2 = z ∧
      y = b ^ 2 * t⁻¹ ∧ orderOf y = 2 ∧
      y ∈ ctx.second ∧ y ∈ normalizer (A : Set G) ∧
      y ∉ twoCoreIn ctx.second ∧
      y ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) ∧
      ∀ c ∈ A, y * c * y⁻¹ = c⁻¹ := by
  obtain ⟨t, htQ, htA, htR, ht4, ht2, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  let H := twoCoreIn ctx.second ⊓ centralizer (A : Set G)
  have hb2H := ctx.five_normalizer_square_centralizes_cyclic_fixed A hcard hcyc b hbP hbN
  have hbt : Commute (b ^ 2) t :=
    (mem_centralizer_iff.mp hb2H t ⟨htQ, htA⟩).symm
  let y := b ^ 2 * t⁻¹
  have hy2 : y ^ 2 = 1 := by
    dsimp [y]
    rw [hbt.inv_right.mul_pow, ← pow_mul, inv_pow, ht2, hb4, mul_inv_cancel]
  have hinv := square_squaring_inverts A hA b hb
  have hyinv : ∀ c ∈ A, y * c * y⁻¹ = c⁻¹ := by
    intro c hc
    have htc : t⁻¹ * c * (t⁻¹)⁻¹ = c :=
      mul_inv_eq_of_eq_mul (mem_centralizer_iff.mp
        ((centralizer (A : Set G)).inv_mem htA) c hc).symm
    change MulAut.conj (b ^ 2 * t⁻¹) c = _
    rw [map_mul, MulAut.mul_apply]
    change MulAut.conj (b ^ 2) (t⁻¹ * c * (t⁻¹)⁻¹) = _
    rw [htc]
    exact hinv c hc
  have hnotcentral : y ∉ centralizer (A : Set G) := by
    intro hyC
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    let _ : IsCyclic A := isCyclic_of_prime_card hA
    obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
    have hc5 : orderOf (c : G) = 5 := by
      rw [orderOf_submonoid, hc, hA]
    have he := hyinv c c.property
    have hcomm : Commute y (c : G) := (mem_centralizer_iff.mp hyC c c.property).symm
    rw [hcomm.eq, mul_inv_cancel_right] at he
    have hc2 : (c : G) ^ 2 = 1 := by
      calc
        (c : G) ^ 2 = (c : G)⁻¹ * c := by
          simpa only [pow_two] using congrArg (fun x : G => x * c) he
        _ = 1 := inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hc2
    rw [hc5] at hd
    norm_num at hd
  have hyN : y ∈ normalizer (A : Set G) :=
    (normalizer (A : Set G)).mul_mem (pow_mem hbN 2)
      ((normalizer (A : Set G)).inv_mem (Subgroup.centralizer_le_normalizer _ htA))
  have hyH : y ∈ centralizer (H : Set G) := by
    apply (centralizer (H : Set G)).mul_mem hb2H
    apply (centralizer (H : Set G)).inv_mem
    dsimp only [H]
    rw [← htgen, zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr rfl
  refine ⟨t, y, htQ, htA, htR, ht4, ht2, rfl, ?_, ?_, hyN, ?_, hyH, hyinv⟩
  · let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hy2 (fun he => hnotcentral (he ▸ (centralizer _).one_mem))
  · exact ctx.second.mul_mem (pow_mem hbP 2)
      (ctx.second.inv_mem (twoCoreIn_le ctx.second htQ))
  · intro hyQ
    exact hnotcentral (ctx.five_normalizer_inter_core_le_centralizer A hA hAP ⟨hyQ, hyN⟩)

end Stellmacher.Recognition
