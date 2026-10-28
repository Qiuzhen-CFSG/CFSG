module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.OrderObstruction
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# Local obstructions for the small selection models

Put X = I/C_I(L), D = L⁺ and H = M_I⁺ ∩ D, viewed intrinsically in D.
The quotient X/D is a two-group. The full O₂,Φ shadow therefore forces
nine to divide |H| and gives three-rank at least two. For the rank assertion,
odd rank one implies cyclic Sylow subgroups, and cyclicity passes to the
shadow quotient. Characteristic two passes to the normal intersection in
M_I⁺; its nontrivial order then makes its two-core nontrivial.

The Sylow and properness lemmas retain the actual subgroup markings.
These are consequences of the published selection inputs, without any
model coverage or source conclusion added as a hypothesis.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.41 and the initial selection on printed pp.1138--1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.SmallModelExclusion

variable {X : Type*} [Group X] [Finite X]

private def intersectionSwap (M D : Subgroup X) : D.subgroupOf M ≃* M.subgroupOf D where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The shadow forces nine into the component intersection; the outer quotient is a two-group. -/
theorem local_nine {D M Y S : Subgroup X} [D.Normal]
    (c : LocalConfiguration D M Y S) (hq : IsPGroup 2 (X ⧸ D)) :
    9 ∣ Nat.card (M.subgroupOf D) := by
  have h36 : 36 ∣ Nat.card M := by
    obtain ⟨e⟩ := c.shadow
    have he : Nat.card ((Y ⊔ S : Subgroup X) ⧸ twoFrattiniCore (Y ⊔ S : Subgroup X)) = 36 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [← he]
    exact (card_quotient_dvd_card _).trans
      (card_dvd_of_le (sup_le (c.yplus_le.trans inf_le_left) c.sylow_le))
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have hcop : Nat.Coprime 9 (D.subgroupOf M).index :=
    Nat.Coprime.of_dvd_right (D.relIndex_dvd_index_of_normal M)
      (by change Nat.Coprime 9 (Nat.card (X ⧸ D)); rw [hn]; exact (by decide : Nat.Coprime 9 2).pow_right n)
  have hd : 9 ∣ Nat.card (D.subgroupOf M) := by
    apply hcop.dvd_of_dvd_mul_right
    rw [card_mul_index]
    exact (by decide : 9 ∣ 36).trans h36
  rwa [Nat.card_congr (intersectionSwap M D).toEquiv] at hd

/-- Characteristic two passes to the normal component intersection, whose two-core is nontrivial. -/
theorem local_core_ne_bot {D M Y S : Subgroup X} [D.Normal]
    (c : LocalConfiguration D M Y S) (hq : IsPGroup 2 (X ⧸ D)) :
    pCore 2 (M.subgroupOf D) ≠ ⊥ := by
  have hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    rw [← c.characteristicTwo]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hn := normal_core_selfCentralizing hc (D.subgroupOf M)
  have hm := (Theory.Quasithin.centralizer_pCore_le_iff 2 (intersectionSwap M D)).mp hn
  intro hb
  rw [hb] at hm
  have ht : (⊤ : Subgroup (M.subgroupOf D)) ≤ ⊥ := by
    intro x _
    apply hm
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  have hu : Subsingleton (M.subgroupOf D) := ⟨fun x y => by
    have hx : x = 1 := ht (mem_top x)
    have hy : y = 1 := ht (mem_top y)
    exact hx.trans hy.symm⟩
  let := hu
  have hd := local_nine c hq
  have hcard : Nat.card (M.subgroupOf D) = 1 := Nat.card_unique
  rw [hcard] at hd
  norm_num at hd

/-- The full shadow has noncyclic Sylow three-subgroups, forcing three-rank at least two. -/
theorem shadow_threeRank {Y S : Subgroup X} (hs : RankTwoShadow Y S) :
    2 ≤ primeRank 3 (Y ⊔ S : Subgroup X) := by
  obtain ⟨e⟩ := hs
  by_contra! h
  let P : Sylow 3 (Y ⊔ S : Subgroup X) := default
  have hc : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  have hr := P.primeRank_quotient_le_one hc (twoFrattiniCore (Y ⊔ S : Subgroup X))
  rw [primeRank_equiv 3 e, primeRank_prod_eq_add] at hr
  have hz : primeRank 3 (Equiv.Perm (Fin 3)) = 0 := by omega
  have hd := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hd

/-- A two-group outer quotient cannot contribute to the three-rank of the local subgroup. -/
theorem local_threeRank {D M Y S : Subgroup X} [D.Normal]
    (c : LocalConfiguration D M Y S) (hq : IsPGroup 2 (X ⧸ D)) :
    2 ≤ primeRank 3 (M.subgroupOf D) := by
  have hrM : 2 ≤ primeRank 3 M := (shadow_threeRank c.shadow).trans
    (primeRank_le_of_injective 3 (inclusion (sup_le (c.yplus_le.trans inf_le_left) c.sylow_le))
      (inclusion_injective _))
  have hzero : primeRank 3 (X ⧸ D) = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hq.exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have h := primeRank_le_ker_add (p := 3) ((QuotientGroup.mk' D).comp M.subtype)
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hzero, add_zero] at h
  change primeRank 3 M ≤ primeRank 3 (D.subgroupOf M) at h
  rw [primeRank_equiv 3 (intersectionSwap M D)] at h
  exact hrM.trans h

/-- The local component intersection contains an actual Sylow two-subgroup of the component. -/
theorem local_sylow {D M Y S : Subgroup X} [D.Normal]
    (c : LocalConfiguration D M Y S) :
    ∃ Q : Sylow 2 D, (Q : Subgroup D) ≤ M.subgroupOf D := by
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal D
  refine ⟨Q, ?_⟩
  rw [hQ, hP]
  exact comap_mono c.sylow_le

variable {G : Type*} [Group G] [Finite G]
variable {L MI Y S : Subgroup G} [L.Normal]

local instance component_normal : (centralizerQuotientComponent L).Normal :=
  (inferInstance : L.Normal).map (centralizerQuotientMap L) (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- The given Sylow supplement makes the centralizer quotient modulo its component a two-group. -/
theorem quotient_two (d : Setup L MI Y S) :
    IsPGroup 2 (CentralizerQuotient L ⧸ centralizerQuotientComponent L) := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := d.sylow
  apply isPGroup_quotient_of_sup_eq_top D (S.map q) ((hP ▸ P.isPGroup').map q)
  change L.map q ⊔ S.map q = ⊤
  rw [← Subgroup.map_sup, d.generated]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- The selected proper parabolic remains proper as a subgroup of the component. -/
theorem local_proper (_d : Setup L MI Y S) (hp : QuotientParabolic L MI S) :
    (MI.map (centralizerQuotientMap L)).subgroupOf (centralizerQuotientComponent L) ≠ ⊤ := by
  intro he
  have hle := subgroupOf_eq_top.mp he
  exact (not_le_of_gt hp.proper) (le_inf hle le_rfl)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.SmallModelExclusion
