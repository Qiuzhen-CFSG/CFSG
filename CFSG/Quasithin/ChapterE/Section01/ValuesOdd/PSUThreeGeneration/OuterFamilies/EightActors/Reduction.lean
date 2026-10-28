module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.SylowNormalCenterIntersection

/-!
# Central involutions and quotient kernels for outer eight-group actors

The ambient two-rank bound forces each Sylow-central socle involution into
every elementary actor of order eight. A normal socle with an inner four-group
supplies such an involution. Together with any outer actor involution it
generates a genuine mixed four-group inside the original actor. No assertion
of membership of that four-group in the conjugation-invariant family is made.

The exact rank-one test for a local radical quotient is that its intersection
with the actor has order at least four. A normal four-group in a local subgroup
supplies this kernel. For such a local subgroup the E0 and intrinsic Sylow
conditions are also discharged when it contains the ambient Sylow. The full
component condition, including its corrected local tau orbit, remains explicit.

Source: Aschbacher--Smith E.1.1--2, E.1.5 and E.1.14(7), pp.209--210, 214;
the last result refers to Aschbacher, GF(2)-representations of finite groups,
Amer. J. Math. 104 (1982), Lemma 4.11. These are reductions for that branch,
not its final local-geometry exclusion.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- A full-rank eight-group contains every involution centralizing its Sylow. -/
theorem member_contains_central_involution [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hz2 : z ^ 2 = 1)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) : z ∈ A := by
  let : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hzC : z ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hTz (hAT ha))
  let : IsElementaryAbelian 2 (A ⊔ zpowers z : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hzC)
  have hc : Nat.card (A ⊔ zpowers z : Subgroup G) ≤ 8 :=
    (primeRank_le_iff_elementary_card_le G).mp
      (ambient_primeRank_two_le_three hp ho hmodel) _ inferInstance
  have he : A = A ⊔ zpowers z := eq_of_le_of_card_ge le_sup_left (hcard.symm ▸ hc)
  rw [he]
  exact (show zpowers z ≤ A ⊔ zpowers z from le_sup_right) (mem_zpowers z)

/-- An inner four-group supplies a common Sylow-central socle involution.
The final quantifier covers actual family actors of order eight, without
assuming that their intersections with the socle are family members. -/
theorem exists_common_central_involution [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ generalizedFitting G ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      ∀ B ∈ d.family, B ≤ (T : Subgroup G) → Nat.card B = 8 → z ∈ B := by
  have hd : 2 ∣ Nat.card (generalizedFitting G) := by
    have hh := card_dvd_of_le (show A ⊓ generalizedFitting G ≤ generalizedFitting G
      from inf_le_right)
    rw [hinner] at hh
    exact dvd_trans (by decide : 2 ∣ 4) hh
  obtain ⟨x, hxC, hx1, hxL⟩ :=
    T.exists_ne_one_mem_center_of_normal (generalizedFitting G) hd
  let n := orderOf x / 2
  have hx2 : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (T.isPGroup'.dvd_orderOf hx1)
  let z : G := (x ^ n : T)
  have hz2 : orderOf z = 2 := by simpa only [z, orderOf_coe] using hx2
  have hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp ((center T).pow_mem hxC n) ⟨t, ht⟩)
  refine ⟨z, hz2, (generalizedFitting G).pow_mem hxL n, (x ^ n : T).property, hTz, ?_⟩
  intro B hB hBT hc
  let := d.elementary.1 B hB
  exact member_contains_central_involution hp ho hmodel hBT hc
    (hz2 ▸ pow_orderOf_eq_one z) hTz

/-- A central socle involution and an outer actor involution give an actual
four-group in the actor. It is not added to the source family. -/
theorem mixed_four_group [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    {z t : G} (hzA : z ∈ A) (hzL : z ∈ generalizedFitting G)
    (hz2 : orderOf z = 2) (htA : t ∈ A) (htL : t ∉ generalizedFitting G) :
    let B := zpowers z ⊔ zpowers t
    B ≤ A ∧ Nat.card B = 4 ∧ B ⊓ generalizedFitting G = zpowers z := by
  let Z := zpowers z
  let : IsElementaryAbelian 2 Z :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hz2 ▸ pow_orderOf_eq_one z)
  have hZL : Z ≤ generalizedFitting G := zpowers_le.mpr hzL
  have ht2 : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA)
    (fun h => htL (h ▸ (generalizedFitting G).one_mem))
  have hdis : Disjoint Z (zpowers t) :=
    Z.disjoint_zpowers_of_prime_order_not_mem t ht2 (fun ht => htL (hZL ht))
  have hZt : Z ≤ centralizer ({t} : Set G) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨z, hzA⟩ : A) (⟨t, htA⟩ : A)))
  have hZcard : Nat.card Z = 2 ^ 1 := by simp only [Z, Nat.card_zpowers, hz2, pow_one]
  obtain ⟨hE, hcard⟩ := IsElementaryAbelian.fixed_join_card Z t ht2 hdis hZt hZcard
  let B := Z ⊔ zpowers t
  let : IsElementaryAbelian 2 B := hE
  have hBcard : Nat.card B = 4 := hcard
  have hout : ¬ B ≤ generalizedFitting G := fun h =>
    htL (h ((show zpowers t ≤ B from le_sup_right) (mem_zpowers t)))
  have hdouble := outer_member_intersection_card hp ho hmodel B hout
  have hinter : Nat.card (B ⊓ generalizedFitting G : Subgroup G) = 2 := by omega
  have he : Z = B ⊓ generalizedFitting G :=
    eq_of_le_of_card_ge (le_inf le_sup_left hZL) (by rw [hinter, hZcard]; decide)
  exact ⟨sup_le (zpowers_le.mpr hzA) (zpowers_le.mpr htA), hBcard, he.symm⟩

/-- Mark the actual eight-actor by a common central socle involution and an
outer involution. Their mixed plane is centralized by the ambient tau, so
its normalizer has the required tau containment. This constructs the plane
without making it a new family member. -/
theorem exists_marked_actor [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T) {A : Subgroup G}
    (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hcard : Nat.card A = 8)
    (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)
    (hout : ¬ A ≤ generalizedFitting G) :
    ∃ z t : G, orderOf z = 2 ∧ z ∈ generalizedFitting G ∧ z ∈ A ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      t ∈ A ∧ t ∉ generalizedFitting G ∧ orderOf t = 2 ∧
      (zpowers z ⊔ zpowers t : Subgroup G) ≤ A ∧
      Nat.card (zpowers z ⊔ zpowers t : Subgroup G) = 4 ∧
      (zpowers z ⊔ zpowers t : Subgroup G) ⊓ generalizedFitting G = zpowers z ∧
      tau (T : Subgroup G) A ≤ centralizer (zpowers z ⊔ zpowers t : Subgroup G) := by
  let := d.elementary.1 A hA
  obtain ⟨z, hz2, hzL, _, hTz, hall⟩ :=
    exists_common_central_involution hp ho hmodel d hinner
  have hzA := hall A hA hAT hcard
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hout
  have ht2 : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA)
    (fun h => htL (h ▸ (generalizedFitting G).one_mem))
  obtain ⟨hBA, hBcard, hBL⟩ := mixed_four_group hp ho hmodel A hzA hzL hz2 htA htL
  have hO := (SimpleSocle.structure_of_sylow_supplement
    (nonabelian_of_model hp ho hmodel) T hLT).2.2.1
  refine ⟨z, t, hz2, hzL, hzA, hTz, htA, htL, ht2, hBA, hBcard, hBL, ?_⟩
  intro x hx
  rw [mem_centralizer_iff]
  intro b hb
  have hc := (mem_centralizerModulo_iff.mp hx).2 b (hBA hb)
  rw [hO, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

/-- The exact radical intersection needed by E.1.5 for the original eight-group. -/
theorem radical_rank_le_one_iff {A K : Subgroup G} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hcard : Nat.card A = 8) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) ≤ 1 ↔
      4 ≤ Nat.card (A.subgroupOf K ⊓ solvableRadical K : Subgroup K) :=
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  IsElementaryAbelian.rank_quotient_image_le_one_iff_of_card_eight _ _
    ((Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hcard)

/-- The analogous literal two-core quotient test, for the solvable E1 branch. -/
theorem twoCore_rank_le_one_iff {A K : Subgroup G} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hcard : Nat.card A = 8) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤ 1 ↔
      4 ≤ Nat.card (A.subgroupOf K ⊓ pCore 2 K : Subgroup K) :=
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  IsElementaryAbelian.rank_quotient_image_le_one_iff_of_card_eight _ _
    ((Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hcard)

/-- A four-group killed by the local radical supplies the rank clause for E2. -/
theorem component_member_of_radical_four {T A K B : Subgroup G}
    (hmember : IsEMember T A K) (hcase : ECaseComponent T A K)
    (hcard : Nat.card A = 8) (hBA : B ≤ A) (hBcard : Nat.card B = 4)
    (hBR : B.subgroupOf K ≤ solvableRadical K) : IsEMemberAt 1 T A K := by
  let := hmember.1
  have hAK := hmember.2.2.1
  have hBK := hBA.trans hAK
  refine ⟨hmember, Or.inr ⟨hcase, (radical_rank_le_one_iff hAK hcard).mpr ?_⟩⟩
  have hc : Nat.card (B.subgroupOf K) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).trans hBcard
  rw [← hc]
  exact Nat.card_le_card_of_injective (inclusion (le_inf (comap_mono hBA) hBR))
    (inclusion_injective _)

/-- Consumer for the solvable branch: a four-group in the actual two-core
gives the rank bound, and the nontrivial odd-core action makes the rank
exactly one. The intrinsic Sylow intersection is retained explicitly. -/
theorem odd_member_le_of_twoCore_four {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A B K : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hAK : A ≤ K) (hcard : Nat.card A = 8)
    (hBA : B ≤ A) (hBcard : Nat.card B = 4)
    (hBcore : B.subgroupOf K ≤ pCore 2 K)
    (htau : tau (T : Subgroup G) A ≤ K)
    (hSylow : ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K)
    {r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hquot : IsPGroup 2 ((K ⧸ pCore 2 K) ⧸ pCore r (K ⧸ pCore 2 K)))
    (hcore : pCore r (K ⧸ pCore 2 K) ≠ ⊥)
    (hcomm : pCore r (K ⧸ pCore 2 K) =
      ⁅pCore r (K ⧸ pCore 2 K),
        (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))⁆) :
    K ≤ d.overgroup := by
  let := d.elementary.1 A hA
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
  have hbound : Group.rank a ≤ 1 := (twoCore_rank_le_one_iff hAK hcard).mpr (by
    have hc : Nat.card (B.subgroupOf K) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe (hBA.trans hAK)).toEquiv).trans hBcard
    rw [← hc]
    exact Nat.card_le_card_of_injective (inclusion (le_inf (comap_mono hBA) hBcore))
      (inclusion_injective _))
  have hane : a ≠ ⊥ := by
    intro he
    change pCore r (K ⧸ pCore 2 K) = ⁅pCore r (K ⧸ pCore 2 K), a⁆ at hcomm
    rw [he, commutator_bot_right] at hcomm
    exact hcore hcomm
  let : Nontrivial a := (nontrivial_iff_ne_bot a).mpr hane
  have hrank : Group.rank a = 1 := Nat.le_antisymm hbound (Group.rank_pos (G := a))
  have hcase : ECaseOdd A K := ⟨r, hr, hro, hquot, hcore, hcomm, hrank⟩
  exact d.members_le A hA hAT K
    ⟨⟨inferInstance, hAT, hAK, le_inf (tau_le _ _) htau, hSylow, Or.inl hcase⟩,
      Or.inl ⟨hcase, hbound⟩⟩

/-- Normality of an actual four-group in K kills both ranks in its two-core,
and hence in its radical. All normality here is relative to K. -/
theorem four_le_radical_of_normalized {A B K : Subgroup G}
    [IsElementaryAbelian 2 A] (hBA : B ≤ A) (hKB : K ≤ normalizer (B : Set G)) :
    B.subgroupOf K ≤ solvableRadical K := by
  let : (B.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKB
  have hB : IsPGroup 2 (B.subgroupOf K) :=
    ((IsElementaryAbelian.isPGroup 2 A).to_le hBA).comap_subtype
  let : Group.IsSolvable (B.subgroupOf K) := @IsNilpotent.to_isSolvable _ _ hB.isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

/-- Consumer: a Sylow overgroup normalizing a four-group in the actor is
trapped once its full E2 structure is established. This proves E0, the
literal Sylow intersection and the quotient-rank bound, not the E2 structure. -/
theorem component_sylow_overgroup_le {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A B K : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hcard : Nat.card A = 8) (hBA : B ≤ A) (hBcard : Nat.card B = 4)
    (hTK : (T : Subgroup G) ≤ K) (hKB : K ≤ normalizer (B : Set G))
    (hcase : ECaseComponent (T : Subgroup G) A K) : K ≤ d.overgroup := by
  let := d.elementary.1 A hA
  have hmember : IsEMember (T : Subgroup G) A K :=
    ⟨inferInstance, hAT, hAT.trans hTK,
      le_inf (tau_le _ _) ((tau_le _ _).trans hTK),
      ⟨T.subtype hTK, rfl⟩, Or.inr hcase⟩
  exact d.members_le A hA hAT K (component_member_of_radical_four hmember hcase
    hcard hBA hBcard (four_le_radical_of_normalized hBA hKB))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
