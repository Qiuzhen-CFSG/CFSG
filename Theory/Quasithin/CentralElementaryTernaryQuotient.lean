module

public import Theory.GroupTheory.CentralElementaryRankTwoQuotient
public import Theory.Quasithin.CoprimeLocalRank

/-!
# Quasithinness through small elementary central three-kernels

Suppose q : G → H has central elementary kernel of order dividing nine, every
two-local subgroup of H has three-part at most nine, and G is quasithin.
Then every surjective image of G whose kernel is contained in ker(q) is
quasithin. Surjectivity of q is not needed.

Lift an actual two-local normalizer from the image to G. Its q-image normalizes
a nontrivial two-subgroup of H because the q-kernel has odd order. For an
elementary three-subgroup of the image local, its full preimage is a three-group;
the q-image therefore has order at most nine. The central elementary rank-two
quotient theorem bounds the original restricted image. Other odd primes are
handled by the coprime-kernel local-rank theorem.

The hypotheses concern every actual two-local subgroup of H, not merely
involution centralizers. The final application retains the literal quotient map.
Source application: the exceptional PSU₄(3) partial-central-quotient step in
Aschbacher–Smith A.2.17, with the ordinary-rank assertion of I.2.1 unchanged.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.Quasithin.CentralElementaryTernaryQuotient

private theorem restricted_kernel
    {G H R : Type*} [Group G] [Finite G] [Group H] [Group R] [Finite R]
    (q : G →* H) [IsElementaryAbelian 3 q.ker]
    (hq : q.ker ≤ center G) (hcard : Nat.card q.ker ∣ 9)
    (j : R →* G) (hj : Function.Injective j) :
    (q.comp j).ker ≤ center R ∧ IsElementaryAbelian 3 (q.comp j).ker ∧
      Nat.card (q.comp j).ker ∣ 9 := by
  have hc : (q.comp j).ker ≤ center R := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply hj
    simpa only [map_mul] using mem_center_iff.mp (hq hx) (j y)
  have he : IsElementaryAbelian 3 (q.comp j).ker := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (hc y.property) x)⟩⟩
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply hj
      change j ((x:R)^3)=j 1
      rw [map_pow,map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (A:=q.ker) (j x) x.property }
  let k : (q.comp j).ker →* q.ker := (j.comp (q.comp j).ker.subtype).codRestrict _
    (fun x => x.property)
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (hj (congrArg Subtype.val he))
  exact ⟨hc,he,(Subgroup.card_dvd_of_injective k hk).trans hcard⟩

private theorem three_rank_local_image
    {G H M : Type*} [Group G] [Finite G] [Group H] [Finite H] [Group M] [Finite M]
    (q : G →* H) [IsElementaryAbelian 3 q.ker]
    (hq : q.ker ≤ center G) (hcard : Nat.card q.ker ∣ 9)
    (hlocal : ∀ N : Subgroup H, IsTwoLocal N → ¬ 27 ∣ Nat.card N)
    (L : Subgroup G) (hL : IsTwoLocal L)
    (g : L →* M) (hg : Function.Surjective g)
    (hgker : g.ker ≤ (q.comp L.subtype).ker) (hLrank : primeRank 3 L ≤ 2) :
    primeRank 3 M ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T,hT,hTp,hLt⟩ := hL
  have hq2 : Nat.Coprime 2 (Nat.card q.ker) := (by decide : Nat.Coprime 2 9).of_dvd_right hcard
  have hTq : T.map q ≠ ⊥ := by
    intro he
    have hk : T ≤ q.ker := (T.map_eq_bot_iff).mp he
    have hd : Disjoint T q.ker := disjoint_of_coprime_natCard (by
      obtain ⟨n,hn⟩ := hTp.exists_card_eq
      rw [hn]
      exact hq2.pow_left n)
    exact hT (le_bot_iff.mp (fun x hx => hd.le_bot ⟨hx,hk hx⟩))
  let N := normalizer (T.map q : Set H)
  have hN : IsTwoLocal N := ⟨T.map q,hTq,hTp.map q,rfl⟩
  have hLN : L.map q ≤ N := by
    rw [hLt]
    exact T.le_normalizer_map q
  obtain ⟨_,hke,_⟩ := restricted_kernel q hq hcard L.subtype L.subtype_injective
  let : IsElementaryAbelian 3 (q.comp L.subtype).ker := hke
  have hgp : IsPGroup 3 g.ker :=
    (IsElementaryAbelian.isPGroup 3 (q.comp L.subtype).ker).to_le hgker
  apply (primeRank_le_iff_elementary_card_le M).mpr
  intro A hA
  let : IsElementaryAbelian 3 A := hA
  let R := A.comap g
  have hR : IsPGroup 3 R := (IsElementaryAbelian.isPGroup 3 A).comap_of_ker_isPGroup g hgp
  let j : R →* G := L.subtype.comp R.subtype
  have hj : Function.Injective j := L.subtype_injective.comp R.subtype_injective
  let u : R →* H := q.comp j
  let v : R →* A := g.subgroupComap A
  have hv : Function.Surjective v := g.subgroupComap_surjective_of_surjective _ hg
  obtain ⟨huc,hue,hud⟩ := restricted_kernel q hq hcard j hj
  let : IsElementaryAbelian 3 u.ker := hue
  have hRN : u.range ≤ N := by
    rintro x ⟨y,rfl⟩
    exact hLN ⟨y.val.val,y.val.property,rfl⟩
  have hrcard : Nat.card u.range ∣ Nat.card N := Subgroup.card_dvd_of_le hRN
  have hri : u.ker.index ≤ 9 := by
    rw [Subgroup.index_ker]
    have hup : IsPGroup 3 u.range := hR.of_surjective u.rangeRestrict u.rangeRestrict_surjective
    obtain ⟨n,hn⟩ := hup.exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra h
      have hd : 27 ∣ Nat.card u.range := by
        rw [hn]
        exact pow_dvd_pow 3 (by omega : 3 ≤ n)
      exact hlocal N hN (hd.trans hrcard)
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) hn2
  have hvker : v.ker ≤ u.ker := by
    intro x hx
    apply hgker
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hrR : primeRank 3 R ≤ 2 := (primeRank_subgroup_le 3 R).trans hLrank
  have hrA := CentralExtension.threeRank_le_two_of_surjective u.ker huc hud hri v hv hvker hrR
  have hc := (primeRank_le_iff_elementary_card_le A).mp hrA ⊤ (by
    exact {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p x.val) })
  simpa only [Subgroup.card_top] using hc

public theorem isQuasithin_of_surjective
    {G H S : Type*} [Group G] [Finite G] [Group H] [Finite H] [Group S] [Finite S]
    (q : G →* H) [IsElementaryAbelian 3 q.ker]
    (hq : q.ker ≤ center G) (hcard : Nat.card q.ker ∣ 9)
    (hlocal : ∀ N : Subgroup H, IsTwoLocal N → ¬ 27 ∣ Nat.card N)
    (f : G →* S) (hf : Function.Surjective f) (hker : f.ker ≤ q.ker)
    (hG : IsQuasithin G) : IsQuasithin S := by
  apply isQuasithin_iff_twoLocalPrimeRank.mpr
  intro r hr ho
  let : Fact r.Prime := ⟨hr⟩
  by_cases hr3 : r=3
  · subst r
    apply (twoLocalPrimeRank_le_iff 3 2).mpr
    intro M hM
    obtain ⟨L,hL,_,g,hg,he⟩ := hM.exists_surjective_of_surjective f hf
    apply three_rank_local_image q hq hcard hlocal L hL g hg ?_
      (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG L hL 3 Nat.prime_three (by decide))
    intro x hx
    apply hker
    change f (x:G)=1
    rw [← he x]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  · have hc : Nat.Coprime r (Nat.card f.ker) := by
      apply ((Nat.coprime_primes hr Nat.prime_three).mpr hr3).pow_right 2 |>.of_dvd_right
      exact (Subgroup.card_dvd_of_le hker).trans hcard
    exact (twoLocalPrimeRank_le_of_surjective_of_coprime r f hf hc).trans
      (isQuasithin_iff_twoLocalPrimeRank.mp hG r hr ho)

public theorem isQuasithin_quotient
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (q : G →* H) [IsElementaryAbelian 3 q.ker]
    (hq : q.ker ≤ center G) (hcard : Nat.card q.ker ∣ 9)
    (hlocal : ∀ N : Subgroup H, IsTwoLocal N → ¬ 27 ∣ Nat.card N)
    (B : Subgroup G) [B.Normal] (hB : B ≤ q.ker)
    (hG : IsQuasithin G) : IsQuasithin (G ⧸ B) := by
  exact isQuasithin_of_surjective q hq hcard hlocal (QuotientGroup.mk' B)
    (QuotientGroup.mk'_surjective B) (by simpa only [QuotientGroup.ker_mk'] using hB) hG

end Theory.Quasithin.CentralElementaryTernaryQuotient
