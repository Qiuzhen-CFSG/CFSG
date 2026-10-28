module
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree

/-!
# Ree and Tits exclusions for a local A₅ section

A subgroup with nontrivial two-core and A₅ two-core quotient normalizes a
nonidentity two-subgroup, and its order is divisible by fifteen. The proved
Ree and Tits two-local order bounds exclude both containing families.
The input retains the full smaller subgroup and its actual two-core, so
no simplicity or deleted-block hypothesis is imposed on that subgroup.

Source: Aschbacher–Smith A.3.12 and the point-component inspection in
10.2.9, printed pp.47–48 and 750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.ExceptionalSmall
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem not_section_of_fifteen_free_normalizers
    {H : Type*} [Group H] [Finite H] (e : G ≃* H)
    (hH : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup 2 R →
      ¬ 15 ∣ Nat.card (normalizer (R : Set H)))
    (B : Subgroup G) (hcore : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let R := (pCore 2 B).map B.subtype
  have hR : R ≠ ⊥ := fun h => hcore
    ((map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp h)
  have hRe : R.map e.toMonoidHom ≠ ⊥ := fun h => hR
    ((map_eq_bot_iff_of_injective R (f := e.toMonoidHom) e.injective).mp h)
  have hBR : B.map e.toMonoidHom ≤ normalizer (R.map e.toMonoidHom : Set H) :=
    (map_mono (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))).trans
        (le_normalizer_map e.toMonoidHom)
  apply hH (R.map e.toMonoidHom) hRe
    ((pCore_isPGroup.map B.subtype).map e.toMonoidHom)
  have hdiv := card_quotient_dvd_card (pCore 2 B)
  rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup] at hdiv
  norm_num at hdiv
  have hN := card_dvd_of_le hBR
  rw [card_map_of_injective e.injective] at hN
  exact (by decide : 15 ∣ 60).trans (hdiv.trans hN)

omit [Finite G] in
/-- A nontrivial two-core with A₅ quotient cannot occur in a large Ree group. -/
theorem not_ree (B : Subgroup G) (hcore : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* ReeF4.Model m) : False :=
  not_section_of_fifteen_free_normalizers e
    (ReeF4.ConverseParabolics.normalizer_fifteen_free hm) B hcore eB

omit [Finite G] in
/-- The same literal section is excluded by the Tits two-local order bound. -/
theorem not_tits (B : Subgroup G) (hcore : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (e : G ≃* Tits.ParrottGroup) : False :=
  not_section_of_fifteen_free_normalizers e Tits.normalizer_fifteen_free B hcore eB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.ExceptionalSmall
