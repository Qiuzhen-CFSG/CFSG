module
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# Odd generation of a parabolic in a binary linear-three cover

In a finite group with two-core quotient PSL₃(2), a proper subgroup
containing a Sylow two-subgroup and a nontrivial odd subgroup is maximal.
Its Sylow subgroup has index three, and the two indicated subgroups generate
it. Pass to the two-core quotient, mark the actual parabolic, then lift
maximality and the index through the kernel contained in the Sylow subgroup.

This supplies the centralizer marking in the preliminary reduction of
Aschbacher--Smith 15.2.23, printed p.1115, refs/quasithin.pdf.
-/

public section
open Subgroup
namespace Matrix.PSL3Two
variable {A : Type*} [Group A] [Finite A]

/-- An odd nontrivial subgroup generates a proper Sylow overgroup in a
binary linear-three cover, together with the specified Sylow subgroup. -/
theorem cover_parabolic_generated_by_sylow_and_odd
    (e₀ : (A ⧸ pCore 2 A) ≃* PSL) (P : Sylow 2 A)
    (B D : Subgroup A) (hPB : (P : Subgroup A) ≤ B) (hB : B ≠ ⊤)
    (hDB : D ≤ B) (ho : Odd (Nat.card D)) (hd : D ≠ ⊥) :
    IsCoatom B ∧ (P : Subgroup A).relIndex B = 3 ∧
      B = (P : Subgroup A) ⊔ D := by
  let q := e₀.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e₀.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e₀.injective,QuotientGroup.ker_mk']
  have hkP : q.ker ≤ (P : Subgroup A) := hk ▸ pCore_isPGroup.le_sylow_of_normal P
  have hkB : q.ker ≤ B := hkP.trans hPB
  have hnot : ¬ IsPGroup 2 D := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hz : n = 0 := by
      by_contra hz
      exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hz)
    exact hd (card_eq_one.mp (by simpa only [hz,pow_zero] using hn))
  let P' := P.mapSurjective hq
  let B' := B.map q
  have hP'B' : (P' : Subgroup PSL) ≤ B' := map_mono hPB
  have hB' : B' ≠ ⊤ := by
    intro he
    have hh := congrArg (comap q) he
    rw [comap_map_eq,sup_eq_left.mpr hkB,comap_top] at hh
    exact hB hh
  have htwo : ¬ IsPGroup 2 B' := by
    intro hp
    apply hnot
    have hh := hp.comap_of_ker_isPGroup q (hk ▸ pCore_isPGroup)
    rw [comap_map_eq,sup_eq_left.mpr hkB] at hh
    exact hh.to_le hDB
  obtain ⟨hc,e,Q,hP,hBmap,_⟩ := exists_compatible_parabolic_marking
    (MulEquiv.refl PSL) P' B' hP'B' hB' htwo
  have hcoat : IsCoatom B := by
    refine ⟨hB,?_⟩
    intro C hBC
    have hkC : q.ker ≤ C := hkB.trans hBC.le
    have hlt : B' < C.map q := lt_of_le_of_ne (map_mono hBC.le) (by
      intro he
      have hh := congrArg (comap q) he
      rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hkB,sup_eq_left.mpr hkC] at hh
      exact hBC.ne hh)
    have hh := congrArg (comap q) (hc.2 _ hlt)
    simpa only [comap_map_eq,sup_eq_left.mpr hkC,comap_top] using hh
  have hri : (P : Subgroup A).relIndex B = 3 := by
    have hr := relIndex_map_map q (P : Subgroup A) B
    rw [sup_eq_left.mpr hkP,sup_eq_left.mpr hkB] at hr
    rw [← hr]
    change (P' : Subgroup PSL).relIndex B' = 3
    rw [← relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective,hP,hBmap]
    have hh := (borelSL.subgroupOf lineParabolicSL).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show borelSL ≤ lineParabolicSL from inf_le_right)).toEquiv,
      card_borelSL,card_lineParabolicSL] at hh
    change 8 * borelSL.relIndex lineParabolicSL = 24 at hh
    omega
  have hgen : (P : Subgroup A).subgroupOf B ⊔ D.subgroupOf B = ⊤ := by
    apply (isCoatom_of_index_three _ hri).2
    apply lt_of_le_of_ne le_sup_left
    intro he
    apply hnot
    apply P.isPGroup'.to_le
    intro a ha
    exact (le_sup_right.trans_eq he.symm) (show (⟨a,hDB ha⟩ : B) ∈ D.subgroupOf B from ha)
  refine ⟨hcoat,hri,?_⟩
  have hm := congrArg (Subgroup.map B.subtype) hgen
  simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hPB,
    map_subgroupOf_eq_of_le hDB,← MonoidHom.range_eq_map,range_subtype] using hm.symm
end Matrix.PSL3Two
