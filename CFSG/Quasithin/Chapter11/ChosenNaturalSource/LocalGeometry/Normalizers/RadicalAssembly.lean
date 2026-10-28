module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.CoreSplit
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Assembly of the point-radical alternative

A nontrivial normal subgroup of a finite two-group meets its omega center.
Applied to the literal C_T(L) inside R1, this shows the fixed omega-center
is nontrivial whenever C_T(L) is. If the radical normalizer preserves that
fixed summand, maximal-local uniqueness forces the entire normalizer into M.
The escaping case therefore has C_T(L)=1; the center calculation then gives
V1=Omega1(Z(R1)). Characteristic exclusion is supplied for both LT and LR1.

The final implication retains three source prerequisites: point-block
recognition, the corrected cohomology center calculation, and the
Goldschmidt--O'Nan fixed-summand argument. It assembles the exact
RadicalNormalizerAlternative but is not a proof of 11.1.5 until those
premises are discharged. The original flags, relative radicals and actual
SL3/Sp4 block predicates are unchanged.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.5, printed pp.765--766.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial normal two-subgroup of R centralizing L meets Ω₁Z(R)
nontrivially. No representation-theoretic center calculation is used. -/
theorem omega_center_fixed_ne_bot {R C L : Subgroup G}
    (hR : IsPGroup 2 R) (hCR : C ≤ R) (hn : R ≤ normalizer (C : Set G))
    (hne : C ≠ ⊥) (hCL : C ≤ centralizer (L : Set G)) :
    omegaOneAmbient ((center R).map R.subtype) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  let N := C.subgroupOf R
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hCR).mpr hn
  have hNne : N ≠ ⊥ := by
    intro he
    apply hne
    have hh := congrArg (map R.subtype) he
    simpa only [N, map_subgroupOf_eq_of_le hCR, Subgroup.map_bot] using hh
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hNne
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  obtain ⟨Z, _, hZN, hZcard, hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard])
  have hz2 : ((z : R) : G) ^ 2 = 1 := by
    have hpow : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    exact congrArg (fun x : Z => ((x : R) : G)) hpow
  have hzC : ((z : R) : G) ∈ C := hZN z.property
  have hzO : ((z : R) : G) ∈ omegaOneAmbient ((center R).map R.subtype) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl _
      (mem_map_of_mem R.subtype (hZcenter z.property)) hz2
  intro he
  have hz1 : ((z : R) : G) = 1 := mem_bot.mp (he ▸ (show
    ((z : R) : G) ∈ omegaOneAmbient ((center R).map R.subtype) ⊓
      centralizer (L : Set G) from ⟨hzO, hCL hzC⟩))
  have hz1' : z = 1 := Subtype.ext (Subtype.ext hz1)
  have : (1 : ℕ) = 2 := by simpa only [hz1', orderOf_one] using hz
  omega

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The radical and its omega center retain the original ambient maps. -/
def radicalOmegaCenter (R : Subgroup G) : Subgroup G :=
  omegaOneAmbient ((center R).map R.subtype)

/-- The fixed summand in the repaired 11.1.5 argument. -/
def radicalFixedCenter (R L : Subgroup G) : Subgroup G :=
  radicalOmegaCenter R ⊓ centralizer (L : Set G)

/-- The source Sylow subgroup normalizes each literal point radical. -/
theorem sylow_normalizes_Ri {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer (f.Ri i : Set G) :=
  (le_sup_right.trans (f.Li i ⊔ (T : Subgroup G)).le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The characteristic exclusion also holds in LR1, the actual ambient
group for the MS-pair. Characteristicity supplies the extra T-invariance. -/
theorem point_ms_no_characteristic_normal (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup (f.Ri 0)) (hchar : C.Characteristic) (hne : C ≠ ⊥) :
    ¬ ((C.map (f.Ri 0).subtype).subgroupOf (L ⊔ f.Ri 0)).Normal := by
  intro hn
  let := hchar
  apply no_characteristic_normal_of_escape D S f hescape C hchar hne
  apply normal_subgroupOf_of_le_normalizer
  apply sup_le
  · exact le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
      ((map_subtype_le C).trans le_sup_right)).mp hn)
  · exact (sylow_normalizes_Ri f 0).trans
      (normalizer_le_normalizer_characteristic_image (f.Ri 0) C)

/-- C_T(L) belongs to every local radical, not merely to the original two-core. -/
theorem componentCentralizer_le_Ri (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c) (i : Fin 2) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ f.Ri i := by
  apply le_pCoreIn_of_normalizes
    (T.isPGroup'.of_injective
      (inclusion (show (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ T from inf_le_left))
      (inclusion_injective _)) (inf_le_left.trans le_sup_right)
  exact (sup_le ((localResidual_le _).trans inf_le_left |>.trans le_sup_left)
    le_sup_right).trans (join_normalizes_componentCentralizer D)

/-- The fixed omega-center is nontrivial whenever C_T(L) is nontrivial. -/
theorem radicalFixedCenter_ne_bot (D : ChosenModule T L V) {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)
    (hne : (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥) :
    radicalFixedCenter (f.Ri 0) L ≠ ⊥ :=
  omega_center_fixed_ne_bot (isPGroup_pCoreIn _ _) (componentCentralizer_le_Ri D f 0)
    (((localRadical_le_sylow _).trans le_sup_right).trans
      (join_normalizes_componentCentralizer D)) hne inf_le_right

/-- Once the Goldschmidt--O'Nan step preserves the fixed summand, maximal-local
uniqueness forces it to vanish in the escaping-normalizer branch. -/
theorem radicalFixedCenter_eq_bot_of_preserved (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hfixed : normalizer (f.Ri 0 : Set G) ≤
      normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    radicalFixedCenter (f.Ri 0) L = ⊥ := by
  by_contra hne
  apply hescape
  apply hfixed.trans
  apply D.normal_subgroup_normalizer_le S.source.toHypothesis1221 _ hne
  · apply sup_le
    · exact (le_centralizer_iff.mpr inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
    · exact (sylow_normalizes_Ri f 0).trans hfixed
  · exact (inf_le_left.trans (omegaOneAmbient_le _)).trans
      ((map_subtype_le (center (f.Ri 0))).trans ((localRadical_le_sylow _).trans le_sup_right))

/-- The complete 11.1.5 assembly from three distinct pending source results:
MS recognition, the corrected cohomology center calculation, and preservation
of the fixed summand by the radical normalizer. No target is a record field. -/
theorem chosen_radicalAlternative_of_source_steps
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L))
    (hcenter : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  by_cases he : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)
  · exact Or.inl he
  obtain ⟨hV, hb⟩ := hblocks he
  have hz := hcenter he hb
  have hzero := radicalFixedCenter_eq_bot_of_preserved D S f he (hfixed he hb hz)
  have hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
    by_contra hne
    exact radicalFixedCenter_ne_bot D f hne hzero
  refine Or.inr ⟨hV, hb, hC, ?_⟩
  simpa only [radicalOmegaCenter, hzero, sup_bot_eq] using hz.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
