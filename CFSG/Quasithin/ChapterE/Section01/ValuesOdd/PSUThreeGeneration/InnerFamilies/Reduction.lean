module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.GroupTheory.SylowNormalCenterIntersection
public import Theory.ElementaryAbelian.Join

/-!
# Central involutions and local containment for inner PSU₃ families

A normal socle meets the center of the ambient Sylow two-subgroup in an
involution. Every nontrivial inner actor in a large-family obstruction is
an elementary group of order four. Adjoining the central involution cannot
increase its order, by the actual PSU₃ two-rank bound, so all such actors
contain the same involution.

The obstruction also traps every solvable Sylow overgroup, by the proved
solvable E-generation and literal E-member inheritance. A minimal supplement
then shows that it traps any Sylow overgroup whose solvable residual is already
trapped. For an involution centralizer C, this permits using C^∞T instead of C
in E.1.2(E2): an odd determinant quotient can prevent C itself from satisfying
the equality O²(C) = C^∞. Given the component conditions on C^∞T, we prove E₀,
the intrinsic Sylow condition, and the rank-one radical quotient, then recover
all of C. The involution is central in this local subgroup, hence lies in its
solvable radical.

These are local reductions, not the exclusion of the obstruction. The actual
component conditions, the solvable p = 3 centralizer, and the unitary geometry
forcing generation remain separate model calculations. The arguments retain
all actors of the original family, including any outer actors.

Source: Aschbacher--Smith, E.1.2, E.1.5, E.1.10, E.1.13 and E.1.14(7),
printed pp.210--214; A.3.21, printed p.55. The last source theorem refers to
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
variable {G : Type*} [Group G] [Finite G]

/-- Maximal elementary rank forces every central socle involution into each
nontrivial inner actor. No new subgroup is added to the family. -/
theorem inner_member_contains_central_involution (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hne : A ≠ ⊥) (hAL : A ≤ L) {z : G} (hzL : z ∈ L)
    (hz2 : z ^ 2 = 1) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    z ∈ A := by
  let := d.elementary.1 A hA
  let : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hzC : z ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hTz (hAT ha))
  let : IsElementaryAbelian 2 (A ⊔ zpowers z : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hzC)
  have hjoinL : A ⊔ zpowers z ≤ L := sup_le hAL (zpowers_le.mpr hzL)
  let : IsElementaryAbelian 2 ((A ⊔ zpowers z).subgroupOf L) :=
    IsElementaryAbelian.subgroupOf hjoinL
  have hc : Nat.card (A ⊔ zpowers z : Subgroup G) ≤ 4 := by
    have h := (primeRank_le_iff_elementary_card_le L).mp
      (primeRank_two_le_of_model L hp hodd hmodel)
      ((A ⊔ zpowers z).subgroupOf L) inferInstance
    rwa [Nat.card_congr (subgroupOfEquivOfLe hjoinL).toEquiv] at h
  have he : A = A ⊔ zpowers z :=
    eq_of_le_of_card_ge le_sup_left
      ((inner_member_card_eq_four L hp hodd hmodel d hA hAT hne hAL).symm ▸ hc)
  have hzjoin : z ∈ A ⊔ zpowers z :=
    (show zpowers z ≤ A ⊔ zpowers z from le_sup_right) (mem_zpowers z)
  rwa [← he] at hzjoin

/-- Choose a single ambient Sylow-central involution lying in every nontrivial
inner member of the given family, including when p = 3. -/
theorem exists_common_inner_involution (L : Subgroup G) [L.Normal] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ L ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      ∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ → A ≤ L → z ∈ A := by
  obtain ⟨A, hA, hAT, hne, hAL⟩ := hi
  have hfour := inner_member_card_eq_four L hp hodd hmodel d hA hAT hne hAL
  have hd : 2 ∣ Nat.card L := by
    have h := card_dvd_of_le hAL
    rw [hfour] at h
    exact dvd_trans (by decide : 2 ∣ 4) h
  obtain ⟨x, hx, hx1, hxL⟩ := T.exists_ne_one_mem_center_of_normal L hd
  let n := orderOf x / 2
  have hxn : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (T.isPGroup'.dvd_orderOf hx1)
  let z : G := (x ^ n : T)
  have hz : orderOf z = 2 := by simpa only [z, orderOf_coe] using hxn
  have hzL : z ∈ L := L.pow_mem hxL n
  have hzT : z ∈ (T : Subgroup G) := (x ^ n : T).property
  have hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp ((center T).pow_mem hx n) ⟨t, ht⟩)
  refine ⟨z, hz, hzL, hzT, hTz, ?_⟩
  intro B hB hBT hne hBL
  exact inner_member_contains_central_involution L hp hodd hmodel d hB hBT hne hBL
    hzL (hz ▸ pow_orderOf_eq_one z) hTz

/-- The obstruction traps the literal E-generation target of its family. -/
theorem generationTarget_le_overgroup {T : Sylow 2 G} (d : LargeFamilyObstruction T) :
    ChiefOrbit.generationTarget 1 T d.family ≤ d.overgroup := by
  apply sup_le _ d.normalizer_le
  apply iSup_le
  intro A
  exact sSup_le fun K hK => d.members_le A.val A.property.1 A.property.2 K hK

/-- Solvable Sylow overgroups are forced into the obstruction by E.1.13. -/
theorem solvable_sylow_overgroup_le {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) [Group.IsSolvable H] :
    H ≤ d.overgroup :=
  (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T H hTH d.elementary).trans
    (generationTarget_le_overgroup d)

/-- Once a normal subgroup is trapped, a solvable quotient adds no obstruction:
a minimal Sylow supplement is solvable and is trapped as well. -/
theorem sylow_overgroup_le_of_solvable_quotient {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (Y : Subgroup H) [Y.Normal] [Group.IsSolvable (H ⧸ Y)]
    (hYM : Y.map H.subtype ≤ d.overgroup) : H ≤ d.overgroup := by
  let S := T.subtype hTH
  obtain ⟨K, hK⟩ := exists_minimalSupplement (S : Subgroup H) ⊤ Y le_top
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hk : f.ker = Y.subgroupOf K := by
    ext k
    change f k = 1 ↔ (k : H) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : H)
  let _ : Group.IsSolvable f.ker := hk ▸ hK.isSolvable_kernel S
  let _ : Group.IsSolvable K := Group.isSolvable_of_ker_le_range
    f.ker.subtype f (by rw [f.ker.range_subtype])
  let _ : Group.IsSolvable (K.map H.subtype) :=
    Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective K)
  have hTK : (T : Subgroup G) ≤ K.map H.subtype := by
    have h := map_mono (f := H.subtype) hK.1.1
    simpa only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using h
  have hKM := solvable_sylow_overgroup_le d (K.map H.subtype) hTK
  have hcover : K ⊔ Y = ⊤ := by simpa using hK.1.2.2
  have he := congrArg (map H.subtype) hcover
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  rw [← he]
  exact sup_le hKM hYM

/-- The Sylow supplement of the involution centralizer's solvable residual.
This definition uses the intrinsic centralizer carrier and its actual inclusion. -/
@[expose] def centralizerResidualOvergroup (T : Sylow 2 G) (z : G) : Subgroup G :=
  (solvableResidual (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ⊔
    (T : Subgroup G)

/-- A central nonidentity actor element discharges the radical-rank condition.
Sylow containment proves E₀ and the intrinsic Sylow equality. Only the local
component structure remains an input to this containment theorem. -/
theorem inner_component_sylow_overgroup_le (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hne : A ≠ ⊥) (hAL : A ≤ L) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ K) {z : G} (hzA : z ∈ A) (hz : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hcase : ECaseComponent (T : Subgroup G) A K) : K ≤ d.overgroup := by
  let w : K := ⟨z, hTK (hAT hzA)⟩
  have hwC : w ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKz k.property))
  let : Group.IsSolvable (center K) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hwR : w ∈ solvableRadical K :=
    le_solvableRadical (center K) inferInstance inferInstance hwC
  have hmem : IsEMember (T : Subgroup G) A K :=
    ⟨d.elementary.1 A hA, hAT, hAT.trans hTK,
      le_inf (tau_le _ _) ((tau_le _ _).trans hTK),
      ⟨T.subtype hTK, rfl⟩, Or.inr hcase⟩
  exact inner_component_member_le L hp hodd hmodel d hA hAT hne hAL hmem hcase w hzA
    (fun h => hz (congrArg Subtype.val h)) hwR

/-- Actual consumer of the local construction: the component conditions on
C_G(z)^∞T force the entire involution centralizer into the obstruction overgroup.
The solvable quotient is discharged by the preceding minimal-supplement result. -/
theorem inner_centralizer_le_of_residual_component (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hne : A ≠ ⊥) (hAL : A ≤ L) {z : G} (hzA : z ∈ A) (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcase : ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  have hKz : centralizerResidualOvergroup T z ≤ centralizer ({z} : Set G) :=
    sup_le (map_subtype_le _) hTz
  have hKM := inner_component_sylow_overgroup_le L hp hodd hmodel d hA hAT hne hAL
    (centralizerResidualOvergroup T z) le_sup_right hzA hz hKz hcase
  exact sylow_overgroup_le_of_solvable_quotient d (centralizer ({z} : Set G)) hTz
    (solvableResidual _) (le_sup_left.trans hKM)

/-- Combine the actual common-involution construction with the local structure
input. The solvable alternative allows p = 3 without imposing a nonexistent
component; the other alternative uses the literal residual supplement.
The unitary model calculation must still supply `hlocal`. -/
theorem exists_inner_centralizer_le_of_local_structure (L : Subgroup G) [L.Normal]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L)
    (hlocal : ∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ → A ≤ L →
      ∀ z : G, orderOf z = 2 → z ∈ L →
        (T : Subgroup G) ≤ centralizer ({z} : Set G) → z ∈ A →
        Group.IsSolvable (centralizer ({z} : Set G)) ∨
          ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z)) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ L ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≤ d.overgroup := by
  obtain ⟨z, hz, hzL, hzT, hTz, hall⟩ :=
    exists_common_inner_involution L hp hodd hmodel d hi
  obtain ⟨A, hA, hAT, hne, hAL⟩ := hi
  have hzA := hall A hA hAT hne hAL
  refine ⟨z, hz, hzL, hzT, hTz, ?_⟩
  rcases hlocal A hA hAT hne hAL z hz hzL hTz hzA with hs | hc
  · let := hs
    exact solvable_sylow_overgroup_le d _ hTz
  · have hz1 : z ≠ 1 := by
      intro h
      simp [h] at hz
    exact inner_centralizer_le_of_residual_component L hp hodd hmodel d
      hA hAT hne hAL hzA hz1 hTz hc

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
