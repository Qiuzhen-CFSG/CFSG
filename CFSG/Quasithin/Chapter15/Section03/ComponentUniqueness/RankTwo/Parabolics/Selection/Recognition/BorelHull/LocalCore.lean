module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.Reduction
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The actual inner two-subgroup for Borel-hull coverage

Characteristic two passes from N to its normal intersection with the component
D. The full S₃ × S₃ Frattini quotient forces Y₊, hence N ∩ D, to be nontrivial.
Consequently the intrinsic two-core of N ∩ D is nontrivial. Its image in D is
the actual two-subgroup normalized by N ∩ D that model coverage will use.
No four-group or recognition conclusion is assumed.

Source: Aschbacher--Smith, 15.3.41(2), printed p.1138, and the first paragraph
of the final proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

variable {H : Type*} [Group H] [Finite H]

private theorem yplus_ne_bot {D N Y T : Subgroup H} (h : LocalConfiguration D N Y T) :
    Y ≠ ⊥ := by
  intro hy
  have h36 : 36 ∣ Nat.card T := by
    obtain ⟨e⟩ := h.shadow
    have he : Nat.card ((Y ⊔ T : Subgroup H) ⧸ twoFrattiniCore (Y ⊔ T : Subgroup H)) = 36 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    have hd := card_quotient_dvd_card (twoFrattiniCore (Y ⊔ T : Subgroup H))
    rw [he, hy, bot_sup_eq] at hd
    exact hd
  obtain ⟨P, hP⟩ := h.sylow
  have ht : IsPGroup 2 T := hP ▸ P.isPGroup'
  obtain ⟨n, hn⟩ := ht.exists_card_eq
  have hd : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 36) h36)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem component_intersection_core {D N Y T : Subgroup H} [D.Normal]
    (h : LocalConfiguration D N Y T) :
    centralizer (pCore 2 (N.subgroupOf D) : Set (N.subgroupOf D)) ≤
      pCore 2 (N.subgroupOf D) := by
  have hN : centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
    rw [← h.characteristicTwo]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hD := normal_core_selfCentralizing hN (D.subgroupOf N)
  let e : D.subgroupOf N ≃* N.subgroupOf D :=
    { toFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hD

/-- The local intersection normalizes a nonidentity two-subgroup of D. -/
theorem component_twoSubgroup_for_cover {D N Y T : Subgroup H} [D.Normal]
    (h : LocalConfiguration D N Y T) :
    ∃ R : Subgroup D, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      N.subgroupOf D ≤ normalizer (R : Set D) := by
  let M := N.subgroupOf D
  have hM : M ≠ ⊥ := by
    intro he
    apply yplus_ne_bot h
    apply bot_unique
    intro y hy
    have hyM : (⟨y, (h.yplus_le hy).2⟩ : D) ∈ M := (h.yplus_le hy).1
    have hy1 := mem_bot.mp (he ▸ hyM)
    exact congrArg Subtype.val hy1
  let : Nontrivial M := (nontrivial_iff_ne_bot M).mpr hM
  have hcore : pCore 2 M ≠ ⊥ := by
    intro he
    have hc := component_intersection_core h
    change centralizer (pCore 2 M : Set M) ≤ pCore 2 M at hc
    rw [he] at hc
    have ht : (⊤ : Subgroup M) ≤ ⊥ := by
      intro x _
      apply hc
      intro y hy
      rw [mem_bot.mp hy]
      simp
    exact top_ne_bot (le_bot_iff.mp ht)
  refine ⟨M.pCoreIn 2, ?_, isPGroup_pCoreIn 2 M, ?_⟩
  · intro he
    exact hcore (((pCore 2 M).map_eq_bot_iff_of_injective M.subtype_injective).mp he)
  · exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
