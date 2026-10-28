module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveActions
public import Theory.GroupTheory.CComponent.QuotientActionDetection

/-!
# Strictness and nontrivial action in the secondary source construction

If the original L and K₂ generate K, then T cannot normalize K₂: it
would normalize K, contradicting the strict Sylow intersection T∩H<T.
Consequently every normal component K_Z of the root normalizer containing
K₂ contains it properly. The same generation identity proves K₂≠1.

The source bound O₂(K_Z T)≤R₂ puts the embedded intrinsic O₂(K_Z) in R₂.
If the literal R₂-action on K_Z/O₂(K_Z) were trivial, K_Z would normalize
R₂. The source normalizer control then makes K_Z normalize K₂. Since K₂
is perfect, component minimality contradicts the strict containment.
All inclusions and actions retain the original root normalizer and both
subtype maps. The final application rederives SecondaryData.radical_action
from its earlier fields and its PSL₂ model, without using radical_action.

Generation, extraction of the actual normal component, and the preceding
radical-normalizer/core bounds remain explicit source obligations of
qt-d-1222-rankone-uniqueness-nonblock. This module discharges their strictness
and quotient-action consequences; it does not construct SecondaryData.
Source: Aschbacher--Smith, original 4.3.13--15, printed pp.617--618.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L}

omit [Finite G] in
theorem secondary_ne_bot_of_generation (hgen : L ⊔ secondary c = K c) :
    secondary c ≠ ⊥ := by
  intro he
  have hLK : L = K c := by simpa only [he, sup_bot_eq] using hgen
  apply c.component_outside
  change K c ≤ normalizer (L : Set G)
  rw [←hLK]
  exact L.le_normalizer

omit [Finite G] in
theorem sylow_not_le_secondary_normalizer
    (D : Chapter12.Section02.ChosenModule T L V)
    (hgen : L ⊔ secondary c = K c) :
    ¬ (T : Subgroup G) ≤ normalizer (secondary c : Set G) := by
  intro hn
  have hTK : (T : Subgroup G) ≤ normalizer (K c : Set G) := by
    rw [←hgen]
    exact (le_inf D.sylow_normalizes_component hn).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTH : (T : Subgroup G) ≤ c.H := hTK.trans c.normalizer_component.ge
  exact c.sylow_strict.ne (inf_eq_left.mpr hTH)

omit [Finite G] in
theorem secondary_lt_component_of_generation
    (D : Chapter12.Section02.ChosenModule T L V)
    (hgen : L ⊔ secondary c = K c)
    (B : Subgroup (rootNormalizer c)) (hn : B.Normal)
    (hB : secondary c ≤ B.map (rootNormalizer c).subtype) :
    secondary c < B.map (rootNormalizer c).subtype := by
  refine lt_of_le_of_ne hB ?_
  intro he
  let := hn
  have hnorm : rootNormalizer c ≤
      normalizer (B.map (rootNormalizer c).subtype : Set G) := by
    have hh := B.le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using hh
  rw [←he] at hnorm
  exact sylow_not_le_secondary_normalizer D hgen ((root_normalized c D).trans hnorm)

omit [Finite G] in
/-- The core of an actual normal component of the root normalizer lies in R₂
once its join with T has the source enlarged-core bound. -/
theorem root_component_core_le_radical
    (D : Chapter12.Section02.ChosenModule T L V)
    (B : Subgroup (rootNormalizer c)) (hn : B.Normal)
    (hcore : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c) :
    (pCore 2 B).map B.subtype ≤ (R₂ c).subgroupOf (rootNormalizer c) := by
  let := hn
  have hnB : rootNormalizer c ≤ normalizer (B.map (rootNormalizer c).subtype : Set G) := by
    have hh := B.le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using hh
  have hle : (B.map (rootNormalizer c).subtype).pCoreIn 2 ≤ R₂ c :=
    (pCoreIn_mono_of_normalizes le_sup_left
      ((sup_le (map_subtype_le _) (root_normalized c D)).trans hnB)).trans hcore
  have hm : ((pCore 2 B).map B.subtype).map (rootNormalizer c).subtype ≤ R₂ c := by
    rw [←map_pCoreIn_of_injective 2 B _ (rootNormalizer c).subtype_injective] at hle
    exact hle
  exact (map_le_iff_le_comap).mp hm

/-- Original 4.3.15 from strict component containment and the preceding
core/normalizer geometry, without any nontrivial-action premise. -/
theorem secondary_radical_action_of_strict_component
    (D : Chapter12.Section02.ChosenModule T L V)
    (hne : secondary c ≠ ⊥)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hn : B.Normal)
    (hsec : secondary c < B.map (rootNormalizer c).subtype)
    (hcore : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hr : R₂ c ≤ rootNormalizer c)
    (hnorm : normalizer (R₂ c : Set G) ≤ normalizer (secondary c : Set G)) :
    letI := hn
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction B (pCore 2 B)) ≠ ⊥ := by
  let := hn
  let C := (secondary c).subgroupOf (rootNormalizer c)
  have hsecR : secondary c ≤ rootNormalizer c := hsec.le.trans (map_subtype_le _)
  have hCB : C ≤ B := by
    intro x hx
    obtain ⟨b,hb,he⟩ := hsec.le hx
    exact (Subtype.ext he : b = x) ▸ hb
  have hClt : C < B := by
    refine lt_of_le_of_ne hCB ?_
    intro he
    have hm := congrArg (map (rootNormalizer c).subtype) he
    rw [map_subgroupOf_eq_of_le hsecR] at hm
    exact hsec.ne hm
  have hCne : C ≠ ⊥ := by
    intro he
    apply hne
    have hm := congrArg (map (rootNormalizer c).subtype) he
    simpa only [C, map_subgroupOf_eq_of_le hsecR, Subgroup.map_bot] using hm
  let : Group.IsPerfect (secondary c) := EndgameSieve.secondary_perfect c
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hsecR).symm.toMonoidHom)
    (subgroupOfEquivOfLe hsecR).symm.surjective
  apply hB.quotient_action_ne_bot hClt hCne (pCore 2 B)
    (root_component_core_le_radical D B hn hcore)
  intro x hx
  have hxR : (x : G) ∈ normalizer (R₂ c : Set G) := by
    rw [←map_subgroupOf_eq_of_le hr]
    exact ((R₂ c).subgroupOf (rootNormalizer c)).le_normalizer_map
      (rootNormalizer c).subtype (mem_map_of_mem _ hx)
  apply mem_normalizer_iff.mpr
  intro y
  exact mem_normalizer_iff.mp (hnorm hxR) (y : G)

/-- Generation by L and K₂ supplies strictness, and the literal radical
therefore acts nontrivially on the full quotient of the selected component. -/
theorem secondary_radical_action_ne_bot
    (D : Chapter12.Section02.ChosenModule T L V)
    (hgen : L ⊔ secondary c = K c)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hn : B.Normal)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hr : R₂ c ≤ rootNormalizer c)
    (hnorm : normalizer (R₂ c : Set G) ≤ normalizer (secondary c : Set G)) :
    letI := hn
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction B (pCore 2 B)) ≠ ⊥ :=
  secondary_radical_action_of_strict_component D (secondary_ne_bot_of_generation hgen)
    B hB hn (secondary_lt_component_of_generation D hgen B hn hsec) hcore hr hnorm

omit [Finite G] in
/-- The existing data's PSL₂ quotient makes its original secondary group
nontrivial; no quotient-action nontriviality is used. -/
theorem SecondaryData.secondary_ne_bot_from_model {n : ℕ} (s : SecondaryData c n) :
    secondary c ≠ ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := s.secondary_model
  let : Nontrivial (secondary c ⧸ pCore 2 (secondary c)) := e.surjective.nontrivial
  let : Nontrivial (secondary c) := (QuotientGroup.mk'_surjective (pCore 2 (secondary c))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

/-- Application to the literal existing action, deriving the radical_action
clause from the earlier geometry rather than projecting that field. -/
theorem SecondaryData.radical_action_from_geometry {n : ℕ} (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((R₂ c).subgroupOf (rootNormalizer c)).map s.action ≠ ⊥ :=
  secondary_radical_action_of_strict_component D s.secondary_ne_bot_from_model
    s.component s.isComponent s.normal s.secondary_lt s.enlarged_core_le
    s.radical_le (s.radical_normalizer.trans inf_le_right)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
