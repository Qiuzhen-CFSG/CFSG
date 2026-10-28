module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.Hall.SylowConjugateContainment
public import Stellmacher.BaumannMap
/-!
# Positive alpha fixed points survive prescribed Hall placement

An odd cubic in a solvable Sylow overgroup has a conjugate in the prescribed
odd Hall subgroup by an element of the original Sylow. The characteristic
alpha subgroup is preserved by that conjugation, so a nontrivial alpha fixed
subgroup is retained for the literal Hall cubic used in axis alignment.
Source: Aschbacher--Smith 10.2.3(4), pp.746--747.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem alpha_fixed_subgroup_sylow_conjugate_nontrivial
    (T : Sylow 2 G) (A : Subgroup G)
    (hfix : thompsonAlpha (T : Subgroup G) ⊓ centralizer (A : Set G) ≠ ⊥)
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    thompsonAlpha (T : Subgroup G) ⊓
      centralizer (A.map (MulAut.conj t).toMonoidHom : Set G) ≠ ⊥ := by
  let f := (MulAut.conj t).toMonoidHom
  have hT : (T : Subgroup G).map f = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  have halpha : (thompsonAlpha (T : Subgroup G)).map f = thompsonAlpha (T : Subgroup G) := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))).map f = _
    rw [←omegaOneCenterAmbient_map_injective f (MulAut.conj t).injective,
      ←elementaryAbelianMaxJ_map_equiv,hT]
    rfl
  have hle : (thompsonAlpha (T : Subgroup G) ⊓ centralizer (A : Set G)).map f ≤
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (A.map f : Set G) := by
    apply le_inf ((map_mono inf_le_left).trans halpha.le)
    exact (map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ f)
  intro he
  have hm := bot_unique (hle.trans he.le)
  exact hfix ((map_eq_bot_iff_of_injective _ (MulAut.conj t).injective).mp hm)

theorem exists_hall_cubic_with_alpha_fixed
    (T : Sylow 2 G) (M A B : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hAM : A ≤ M)
    (hsolv : Group.IsSolvable M)
    (hB : IsHallSubgroup Subgroup.OddHall.oddPrimes (B.subgroupOf M))
    (hA : Nat.card A = 3)
    (hfix : thompsonAlpha (T : Subgroup G) ⊓ centralizer (A : Set G) ≠ ⊥) :
    ∃ t ∈ (T : Subgroup G),
      A.map (MulAut.conj t).toMonoidHom ≤ B ∧
      Nat.card (A.map (MulAut.conj t).toMonoidHom) = 3 ∧
      thompsonAlpha (T : Subgroup G) ⊓
        centralizer (A.map (MulAut.conj t).toMonoidHom : Set G) ≠ ⊥ := by
  obtain ⟨t,ht,hm⟩ := Subgroup.OddHall.exists_sylow_conjugate_le_hall T M A B
    hTM hAM hsolv (by rw [hA]; decide) hB
  exact ⟨t,ht,hm,by rw [card_map_of_injective (MulAut.conj t).injective,hA],
    alpha_fixed_subgroup_sylow_conjugate_nontrivial T A hfix t ht⟩

omit [Finite G] in
theorem alpha_fixed_subtype_nontrivial
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (A : Subgroup H)
    (hfix : thompsonAlpha (T.subtype hTH : Subgroup H) ⊓ centralizer (A : Set H) ≠ ⊥) :
    thompsonAlpha (T : Subgroup G) ⊓ centralizer (A.map H.subtype : Set G) ≠ ⊥ := by
  have halpha : (thompsonAlpha (T.subtype hTH : Subgroup H)).map H.subtype =
      thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      show (T.subtype hTH : Subgroup H).map H.subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le hTH]
  have hle : (thompsonAlpha (T.subtype hTH : Subgroup H) ⊓ centralizer (A : Set H)).map H.subtype ≤
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (A.map H.subtype : Set G) :=
    le_inf ((map_mono inf_le_left).trans halpha.le)
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ H.subtype))
  intro he
  exact hfix ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp (bot_unique (hle.trans he.le)))
end CFSG.Quasithin.ChapterB
