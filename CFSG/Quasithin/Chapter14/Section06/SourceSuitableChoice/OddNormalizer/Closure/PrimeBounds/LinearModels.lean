module
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.ComponentSolvableBorelExtension
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Concrete binary PSL₂ Borels in solvable overgroups

The normalizer of every Sylow two-subgroup of PSL₂(2^m) is conjugate
to the upper triangular Borel, whose torus has order 2^m-1. The concrete
proper-overgroup theorem gives solvable Sylow control. For an actual
component, its Borel therefore has solvable join with any solvable
overgroup of the ambient Sylow, even when that overgroup permutes components.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033;
F.1.3(1), printed pp.259--260, for the concrete Borel facts.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.Converse
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The defining split torus divides every actual binary PSL₂ Sylow normalizer. -/
theorem binary_psl2_sylow_normalizer_torus_dvd
    (F : Type*) [Field F] [Finite F] {m : ℕ} (_hm : 0 < m)
    (hF : Nat.card F = 2 ^ m) (P : Sylow 2 (PSL2 F)) :
    2 ^ m - 1 ∣ Nat.card (normalizer (P : Set (PSL2 F))) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (PSL2 F) (ChapterF.Source.Linear.projectiveSylow F) P
  have hmap : (ChapterF.Source.Linear.projectiveSylow F : Subgroup (PSL2 F)).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup (PSL2 F)) := by
    rw [← hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    rfl
  have he := Subgroup.map_equiv_normalizer_eq
    (ChapterF.Source.Linear.projectiveSylow F : Subgroup (PSL2 F)) (MulAut.conj g)
  rw [hmap] at he
  simp only [Sylow.coe_coe] at he
  rw [← he,card_map_of_injective (MulAut.conj g).injective,
    ChapterF.Source.Linear.projectiveSylow_normalizer]
  have ht : Nat.card (PTorus F) = 2 ^ m - 1 := by rw [PTorus_card,Nat.card_units,hF]
  rw [← ht]
  exact card_dvd_of_le (PTorus_le_PBorel (F := F))

/-- A binary PSL₂ component supplies a solvable extension with its torus divisor. -/
theorem binary_psl2_component_solvable_extension
    (T : Sylow 2 G) (H L : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hH : Group.IsSolvable H) (hL : L.IsCComponent)
    (F : Type*) [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m) (e : L ≃* PSL2 F) :
    ∃ J : Subgroup G, H ≤ J ∧ Group.IsSolvable J ∧ 2 ^ m - 1 ∣ Nat.card J := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ)^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm)
  let : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup L := e.isSimpleGroup
  let := hL.perfect
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple L := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  have he (P : Sylow 2 L) : (normalizer (P : Set L)).map e.toMonoidHom =
      normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set (PSL2 F)) := by
    exact map_normalizer_eq_of_bijective (P : Subgroup L) e.bijective
  have hc : SolvableSylowControl 2 L := by
    apply SolvableSylowControl.of_proper_overgroups hL.not_isSolvable
    intro P A hPA hA
    have hlt : A.map e.toMonoidHom < ⊤ := by
      rw [← map_top_of_surjective e.toMonoidHom e.surjective]
      exact (map_lt_map_iff_of_injective e.injective).mpr hA
    have hb := (ChapterF.Source.rankOneSylowFacts_psl2 F m (by omega) hF
      (P.mapSurjective (f := e.toMonoidHom) e.surjective)).unique_maximal
      (A.map e.toMonoidHom) (map_mono hPA) hlt
    rw [← he P] at hb
    exact (map_le_map_iff_of_injective e.injective).mp hb
  have hs (P : Sylow 2 L) : Group.IsSolvable (normalizer (P : Set L)) := by
    let := (ChapterF.Source.rankOneSylowFacts_psl2 F m (by omega) hF
      (P.mapSurjective (f := e.toMonoidHom) e.surjective)).solvable
    let f := (normalizer (P : Set L)).equivMapOfInjective e.toMonoidHom e.injective
    let : Group.IsSolvable ((normalizer (P : Set L)).map e.toMonoidHom) := he P ▸ inferInstance
    exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  obtain ⟨P,_,hsP⟩ := (show IsComponent G L from ⟨hL.subnormal,inferInstance⟩).solvable_borel_extension
    T H L hTH hH hc hs
  let B := (normalizer (P : Set L)).map L.subtype
  refine ⟨B ⊔ H,le_sup_right,hsP,?_⟩
  have hd : 2 ^ m - 1 ∣ Nat.card B := by
    rw [card_map_of_injective L.subtype_injective,
      ← card_map_of_injective (K := normalizer (P : Set L)) (f := e.toMonoidHom) e.injective,he P]
    exact binary_psl2_sylow_normalizer_torus_dvd F (by omega) hF _
  exact hd.trans (card_dvd_of_le (show B ≤ B ⊔ H from le_sup_left))
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
