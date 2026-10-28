module
public import Theory.GroupTheory.CComponent.TwoCorePrimeActors
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# Full-rank C-component quotient actions

The intrinsic two-core quotient marking intertwines ambient conjugation
with conjugation on the actual image modulo the ambient two-core. Full
p-rank and a p-prime center make the latter action kernel p-prime. Thus
an outside order-p actor is outer on the full intrinsic quotient, and
that literal action image retains the ambient rank bound. Neither the
original two-core nor the component center is silently discarded.

The source application keeps the torus, full component quotient and
original action in NonblockEndgameSieveModelsFieldActors.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.12(2), p.617.
-/

public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace Theory.GroupTheory.CComponentPrimeRank
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic quotient marking intertwines the two literal conjugation actions. -/
theorem twoCoreQuotientAction_compatible (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent) (x : G) :
    let I := B.map (QuotientGroup.mk' (pCore 2 G))
    let : I.Normal := (inferInstance : B.Normal).map _ (QuotientGroup.mk'_surjective _)
    MulAut.congr (cComponentTwoCoreQuotientEquiv hB)
      (normalQuotientAction B (pCore 2 B) x) =
      MulAut.conjNormal (QuotientGroup.mk' (pCore 2 G) x) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := B.map q
  let : I.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  let e := cComponentTwoCoreQuotientEquiv hB
  have he (b : B) : e (QuotientGroup.mk' (pCore 2 B) b) = q.subgroupMap B b := rfl
  apply MulEquiv.ext
  intro y
  obtain ⟨b,rfl⟩ := q.subgroupMap_surjective B y
  change e (normalQuotientAction B (pCore 2 B) x (e.symm (q.subgroupMap B b))) = _
  rw [←he b,e.symm_apply_apply,normalQuotientAction_apply_mk,he]
  apply Subtype.ext
  change q (x * b.val * x⁻¹) = q x * q b.val * (q x)⁻¹
  simp only [map_mul,map_inv]

variable {p : ℕ} [Fact p.Prime]

/-- A prime-order actor outside a full-rank C-component is outer on its full two-core quotient. -/
theorem quotientAction_not_inner_of_outside (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent)
    (hz : Nat.Coprime p (Nat.card (center (B ⧸ pCore 2 B))))
    (hr : 2 ≤ primeRank p B) (hG : primeRank p G ≤ 2)
    (ho : Odd p) (x : G) (hx : orderOf x = p) (hxn : x ∉ B) :
    normalQuotientAction B (pCore 2 B) x ∉ MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := B.map q
  let : I.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  let e := cComponentTwoCoreQuotientEquiv hB
  have hzI : Nat.Coprime p (Nat.card (center I)) := by
    rw [←Nat.card_congr (centerCongr e).toEquiv]
    exact hz
  have hrI : 2 ≤ primeRank p I := by
    rw [←primeRank_congr p e,primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    exact hr
  have hQ : primeRank p (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans hG
  have hqx : q x ∉ I := fun hi => hxn (prime_actor_mem_of_twoGroup_image _ _ pCore_isPGroup ho x hx hi)
  have hxq : orderOf (q x) = p := by
    apply orderOf_eq_prime
    · rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]
    · exact fun he => hqx (he ▸ I.one_mem)
  intro hi
  have hiI : (MulAut.conjNormal (q x) : MulAut I) ∈ MulAut.innerSubgroup I := by
    rw [←twoCoreQuotientAction_compatible B hB x,←MulAut.map_innerSubgroup_congr e]
    exact mem_map_of_mem _ hi
  let f : (G ⧸ pCore 2 G) →* MulAut I := MulAut.conjNormal
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    rw [show f.ker = centralizer (I : Set (G ⧸ pCore 2 G)) from MulAut.conjNormal_ker_eq_centralizer I]
    exact Theory.GroupAction.ComponentRankAction.centralizer_coprime I hzI hrI hQ
  apply hqx
  apply Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem f hk I (q x) hxq
  obtain ⟨b,hb⟩ := hiI
  exact ⟨b,b.property,MulAut.conjNormal_val.trans hb⟩

/-- The literal full quotient action image retains the ambient rank bound. -/
theorem quotientAction_rank_le_two (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent)
    (hz : Nat.Coprime p (Nat.card (center (B ⧸ pCore 2 B))))
    (hr : 2 ≤ primeRank p B) (hG : primeRank p G ≤ 2) (ho : Odd p) :
    primeRank p (normalQuotientAction B (pCore 2 B)).range ≤ 2 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := B.map q
  let : I.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  let e := cComponentTwoCoreQuotientEquiv hB
  let f : (G ⧸ pCore 2 G) →* MulAut I := MulAut.conjNormal
  have hzI : Nat.Coprime p (Nat.card (center I)) := by
    rw [←Nat.card_congr (centerCongr e).toEquiv]
    exact hz
  have hrI : 2 ≤ primeRank p I := by
    rw [←primeRank_congr p e,primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    exact hr
  have hQ : primeRank p (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans hG
  have hk : Nat.Coprime p (Nat.card f.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict,
      show f.ker = centralizer (I : Set (G ⧸ pCore 2 G)) from MulAut.conjNormal_ker_eq_centralizer I]
    exact Theory.GroupAction.ComponentRankAction.centralizer_coprime I hzI hrI hQ
  have hb := (primeRank_le_of_surjective_of_coprime p f.rangeRestrict f.rangeRestrict_surjective hk).trans hQ
  let a := normalQuotientAction B (pCore 2 B)
  have he : a.range.map (MulAut.congr e).toMonoidHom = f.range := by
    ext y
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨q x,twoCoreQuotientAction_compatible B hB x |>.symm⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
      exact ⟨a z,⟨z,rfl⟩,twoCoreQuotientAction_compatible B hB z⟩
  rw [←he,←primeRank_congr p (a.range.equivMapOfInjective
    (MulAut.congr e).toMonoidHom (MulAut.congr e).injective)] at hb
  exact hb
end Theory.GroupTheory.CComponentPrimeRank
