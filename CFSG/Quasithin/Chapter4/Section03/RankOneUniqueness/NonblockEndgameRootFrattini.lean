module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCentralizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameBoundedCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryNormalizer

/-!
# The original component core is special with source-root center

The perfect component fixes the center of its two-core P. The secondary
centralizer identity therefore puts Z(P) inside the original root Z_S,
which has order at most four. The earlier Frattini argument gives
P'≤Φ(P)≤Z(P). The moved section of degree at least sixteen rules out P'=1.
The original cubic normalizes P' and fixes no nonidentity root element;
orbit counting forces P' to have order four. Consequently P'=Φ(P)=Z(P)=Z_S,
with all three equalities made through the original ambient subtype map.

This replaces the earlier upper bound 64 for Φ(P) by its exact order four.
It does not exclude this special core. Strict secondary-core enlargement,
actual MS construction, the remaining terminal exclusion and discharge of
the independently owned nonbinary input remain with
qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith, C.1.34(3), pp.136--137, and the terminal argument
of original 4.3.2, pp.618--619; Burnside's basis theorem and cubic orbit counting.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
namespace RootCoordinates
variable (m : RootCoordinates d)
  (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hXr : X ≤ rootNormalizer c) (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
include m hX hfix

private theorem invariant_root_eq (A : Subgroup G) (hA : A ≤ root c)
    (hN : X ≤ normalizer (A : Set G)) (hne : A ≠ ⊥) : A = root c := by
  have hR : Nat.card (root c) ≤ 4 := by
    have hh := m.root_card_le
    simpa only [d.field.card_eq,d.degree_eq,Nat.reducePow] using hh
  have hAc : Nat.card A ≤ 4 :=
    (Nat.card_le_card_of_injective (inclusion hA) (inclusion_injective hA)).trans hR
  have hc : A ⊓ centralizer (X : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (hA.trans (d.root_le_center.trans (map_subtype_le _)))).trans_eq hfix)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX)
  have hmod := Subgroup.card_modEq_card_inf_centralizer X A hp hN
  change Nat.card A % 3 = Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) % 3 at hmod
  rw [hc,Subgroup.card_bot] at hmod
  have hpos : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  apply eq_of_le_of_card_ge hA
  omega

include m s D hX hXK hXr hfix hcomm e

theorem component_center_le_root :
    let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
    (center P).map P.subtype ≤ root c := by
  let M := s.component.map (rootNormalizer c).subtype
  let P := M.pCoreIn 2
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  have hn : rootNormalizer c ≤ normalizer (P : Set G) :=
    s.component_normalized.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hc := m.abelian_core_centralizes_component s D X hX hXK hXr hfix hcomm e
    ((center P).map P.subtype) ((map_subtype_le _).trans hcore.le)
    ((sup_le (map_subtype_le _) hXr).trans
      (hn.trans (normalizer_le_normalizer_characteristic_image P (center P))))
  have hK : (center P).map P.subtype ≤ centralizer (secondary c : Set G) :=
    le_centralizer_iff.mp (s.secondary_le.trans hc)
  exact (le_inf ((map_subtype_le _).trans (s.component_core_le D)) hK).trans_eq
    (m.radical_centralizer_secondary (by decide) D s)

theorem component_special_root
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
    (commutator P).map P.subtype = root c ∧
      (frattini P).map P.subtype = root c ∧
      (center P).map P.subtype = root c ∧ Nat.card (frattini P) = 4 := by
  let M := s.component.map (rootNormalizer c).subtype
  let P := M.pCoreIn 2
  let C := (commutator P).map P.subtype
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  have hz := m.component_center_le_root s D X hX hXK hXr hfix hcomm e
  change (center P).map P.subtype ≤ root c at hz
  obtain ⟨_,_,hf⟩ := m.component_frattini_structure s D X hX hXK hXr hfix hcomm e h
  let : Fact (IsPGroup 2 P) := ⟨isPGroup_pCoreIn 2 M⟩
  have hcf : commutator P ≤ frattini P := commutator_le_frattini_of_isPGroup (p := 2)
  have hC : C ≤ root c := (map_mono (hcf.trans hf)).trans hz
  have hn : rootNormalizer c ≤ normalizer (P : Set G) :=
    s.component_normalized.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hNC : X ≤ normalizer (C : Set G) :=
    hXr.trans (hn.trans (normalizer_le_normalizer_characteristic_image P (commutator P)))
  have hCne : C ≠ ⊥ := by
    intro hb
    have hcb : commutator P = ⊥ := (map_eq_bot_iff_of_injective _ P.subtype_injective).mp hb
    have hzt : center P = ⊤ := (commutator_eq_bot_iff_center_eq_top P).mp hcb
    have hP : P ≤ root c := by
      simpa only [hzt,←MonoidHom.range_eq_map,range_subtype] using hz
    have hPc : Nat.card P ≤ 4 := by
      have hh := (Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)).trans
        m.root_card_le
      simpa only [d.field.card_eq,d.degree_eq,Nat.reducePow] using hh
    obtain ⟨A,B,hBA,hA,_,_,_,_,hd⟩ :=
      m.exists_moved_core_section s D X hX hXK hXr hfix hcomm e h
    have hAc : Nat.card A ≤ 4 :=
      (Nat.card_le_card_of_injective (inclusion (hA.trans hcore.ge))
        (inclusion_injective (hA.trans hcore.ge))).trans hPc
    have hb := Nat.le_of_dvd (Nat.card_pos (α := A)) (B.subgroupOf A).index_dvd_card
    change B.relIndex A ≤ Nat.card A at hb
    rcases hd with hd | hd <;> rw [hd] at hb <;> norm_num at hb <;> omega
  have heq : C = root c := m.invariant_root_eq X hX hfix C hC hNC hCne
  have hF : (frattini P).map P.subtype = root c :=
    le_antisymm ((map_mono hf).trans hz) (heq.ge.trans (map_mono hcf))
  have hZ : (center P).map P.subtype = root c :=
    le_antisymm hz (hF.ge.trans (map_mono hf))
  have hR : Nat.card (root c) = 4 := by
    have hle : Nat.card (root c) ≤ 4 := by
      simpa only [d.field.card_eq,d.degree_eq,Nat.reducePow] using m.root_card_le
    have hmod := m.invariant_cubic_card_mod_three s D X hX hXK hfix hcomm
      C (hC.trans ((d.root_le_center.trans (map_subtype_le _)).trans (core_le_radical c)))
      ((inf_le_left.trans s.secondary_le).trans ((map_subtype_le _).trans
        (hn.trans (normalizer_le_normalizer_characteristic_image P (commutator P))))) hNC
    have hpos := (Subgroup.one_lt_card_iff_ne_bot C).mpr hCne
    rw [heq] at hmod hpos
    omega
  refine ⟨heq,hF,hZ,?_⟩
  have hh := congrArg (fun H : Subgroup G => Nat.card H) hF
  rwa [card_map_of_injective P.subtype_injective,hR] at hh
end RootCoordinates

/-- The original component core is special, with its entire center and
Frattini subgroup equal to the original four-element source root. -/
theorem MSData.linearFour_special_root (d : MSData c 2) (m : RootCoordinates d)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL) :
    let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
    (commutator P).map P.subtype = root c ∧
      (frattini P).map P.subtype = root c ∧
      (center P).map P.subtype = root c ∧ Nat.card (frattini P) = 4 := by
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  exact m.component_special_root s D X hX hXK hr hfix hcomm e h
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
