module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Orbit
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# The algebraic center reduction for corrected source 11.1.5

For an actual short block, the centralizer of V in LT is its two-core Q,
and [Q,L]=V. Thus the point-radical omega center lies in Q. If it lies in
VC_T(L), coprime decomposition under the odd Cartan puts its moved part in
V₁ and its fixed part in C_G(L), giving Ω₁Z(R₁)=V₁ C_{Ω₁Z(R₁)}(L).

The equality branch Q=VC_T(L) is proved separately. In the strict branch,
the remaining input is C_Q(R₁)≤VC_T(L). The actual RadicalAssembly consumer
retains this calculation and the point geometry explicitly. Their construction
remains with this point-cohomology owner; block recognition and preservation
of the fixed summand belong to the parent normalizer-source assembly.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 11.1.5,
printed pp.765–766, with the C.1.13 denominator correction.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
theorem denominator_factor (D : ChosenModule T L V) {z : G}
    (hz : z ∈ cohomologyDenominator T L V) :
    ∃ v ∈ V, ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), v * c = z := by
  have hn : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le D.le_component)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hp : z ∈ (V : Set G) *
      (((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hz
  exact hp

omit [Finite G] in
theorem denominator_commutator_le (D : ChosenModule T L V) :
    ⁅cohomologyDenominator T L V, L⁆ ≤ V := by
  apply commutator_le.mpr
  intro z hz l hl
  obtain ⟨v,hv,c,hc,rfl⟩ := denominator_factor D hz
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 l hl).symm]
  simpa using commutator_le.mp
    (le_normalizer_iff_commutator_le_left.mp D.normalizes) v hv l hl

omit [Finite G] in
private theorem denominator_fixed_le (D : ChosenModule T L V) {X : Subgroup G}
    (hXL : X ≤ L) (hfixed : V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) :
    cohomologyDenominator T L V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G) := by
  rintro z ⟨hz,hzX⟩
  obtain ⟨v,hv,c,hc,rfl⟩ := denominator_factor D hz
  have hcX : c ∈ centralizer (X : Set G) := centralizer_le hXL hc.2
  have hvX : v ∈ centralizer (X : Set G) := by
    have hh := (centralizer (X : Set G)).mul_mem hzX
      ((centralizer (X : Set G)).inv_mem hcX)
    simpa only [mul_inv_cancel_right] using hh
  exact (centralizer (L : Set G)).mul_mem (hfixed ⟨hv,hvX⟩) hc.2

/-- C_LT(V)=O₂(LT) for an actual short block, on the original ambient maps. -/
theorem centralizer_seed_eq_core (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) (hb : ChapterC.IsShort L) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : N ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hquot : IsPGroup 2 (H ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype hgen
  let A := H ⊓ centralizer (V : Set G)
  have hAp : IsPGroup 2 A := by
    intro a
    let aH : H := ⟨a, a.property.1⟩
    obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' N aH)
    have haL : (a : G) ^ 2 ^ n ∈ L := by
      change aH ^ 2 ^ n ∈ N
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (aH ^ 2 ^ n) = 1
      rwa [map_pow]
    have haU : (⟨(a : G) ^ 2 ^ n, haL⟩ : L) ∈
        centralizer (ChapterC.blockU L : Set L) := by
      intro u hu
      apply Subtype.ext
      exact (centralizer (V : Set G)).pow_mem a.property.2 (2 ^ n) u
        ((PointBlocks.seed_eq_blockU D hb).symm ▸ mem_map_of_mem L.subtype hu)
    have haCore := hb.centralizer_blockU.le haU
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := L)) ⟨_, haCore⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    change (a : G) ^ 2 ^ (n + m) = 1
    rw [pow_add, pow_mul]
    exact congrArg (fun x : pCore 2 L => ((x : L) : G)) hm
  apply le_antisymm
  · apply le_pCoreIn_of_normalizes hAp inf_le_left
    exact (le_inf H.le_normalizer
      ((sup_le D.normalizes S.sylow_normalizes).trans
        (normalizer_le_normalizer_centralizer V))).trans inf_normalizer_le_normalizer_inf
  · exact le_inf (pCoreIn_le _ _) D.core_centralizes

/-- The original core commutator is the chosen seed. This supplies the
central elementary displacement layer in the corrected C.1.13 application. -/
theorem core_commutator_eq_seed (D : ChosenModule T L V)
    (hb : ChapterC.IsShort L) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ = V := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (le_sup_left.trans (L ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hQL : Q ≤ normalizer (L : Set G) :=
    (pCoreIn_le _ _).trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hcL : ⁅Q,L⁆ ≤ L := le_normalizer_iff_commutator_le_right.mp hQL
  have hcQ : ⁅Q,L⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hLQ
  have hcore : ⁅Q,L⁆ ≤ L.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le hcQ) hcL
      (normalizer_commutator_ge_right Q L)
  have hi := commutator_isPPerfect_idempotent L Q hb.twoPerfect
    (isPGroup_pCoreIn 2 _) hLQ
  apply le_antisymm
  · rw [PointBlocks.seed_eq_blockU D hb, ChapterC.blockU, map_commutator,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hi.symm.le.trans (commutator_mono hcore le_rfl)
  · exact D.eq_commutator.le.trans (commutator_mono D.le_core le_rfl)

/-- Since R₁ contains V, its center is already in the original two-core. -/
theorem radicalOmegaCenter_le_core (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) (hb : ChapterC.IsShort L)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    radicalOmegaCenter (f.Ri 0) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← centralizer_seed_eq_core D S hb]
  intro z hz
  have hz' : z ∈ omegaCenterIn (f.Ri 0) :=
    (omegaCenterIn_eq_omegaOneAmbient (f.Ri 0)).symm ▸ hz
  obtain ⟨hzR,hzC,_⟩ := (mem_omegaCenterIn_iff _ _).mp hz'
  exact ⟨mem_sup_right (localRadical_le_sylow _ hzR),
    centralizer_le (f.seed_le_Ri S 0) hzC⟩

theorem center_eq_point_sup_fixed_of_le_denominator
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hXL : X ≤ L) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hodd : Odd (Nat.card X))
    (hfixed : V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G))
    (hpoint : V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0)
    (hz : radicalOmegaCenter (f.Ri 0) ≤ cohomologyDenominator T L V) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L := by
  let Z := radicalOmegaCenter (f.Ri 0)
  have hZeq : Z = omegaCenterIn (f.Ri 0) := (omegaCenterIn_eq_omegaOneAmbient _).symm
  let : IsElementaryAbelian 2 Z := hZeq ▸ inferInstance
  let := D.elementary
  have hZR : Z ≤ f.Ri 0 := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp (hZeq ▸ hz)).1
  have hZC : Z ≤ centralizer (f.Ri 0 : Set G) := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp (hZeq ▸ hz)).2.1
  have hXZ : X ≤ normalizer (Z : Set G) := by
    rw [hZeq]
    exact hXR.trans (normalizer_le_normalizer_omegaCenterIn _)
  have hcop : Nat.Coprime (Nat.card X) (Nat.card Z) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 Z).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime Z X hXZ
    (inferInstance : Group.IsSolvable Z) hcop
  have hmZ : ⁅Z,X⁆ ≤ Z := le_normalizer_iff_commutator_le_left.mp hXZ
  have hmV : ⁅Z,X⁆ ≤ V := (commutator_mono hz hXL).trans (denominator_commutator_le D)
  have hmP : ⁅Z,X⁆ ≤ f.Vi 0 := hpoint ▸ le_inf hmV (hmZ.trans hZC)
  have hfL : Z ⊓ centralizer (X : Set G) ≤ radicalFixedCenter (f.Ri 0) L :=
    le_inf inf_le_left ((inf_le_inf_right _ hz).trans (denominator_fixed_le D hXL hfixed))
  apply le_antisymm
  · exact hsplit.le.trans (sup_le_sup hmP hfL)
  · apply sup_le _ inf_le_left
    rw [← hpoint]
    rintro v ⟨hv,hvC⟩
    rw [show radicalOmegaCenter (f.Ri 0) = omegaCenterIn (f.Ri 0) from hZeq]
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨f.seed_le_Ri S 0 hv, hvC, elemPow_eq_one_of_isElementaryAbelian v hv⟩

/-- The corrected equality branch retains the entire possible central factor. -/
theorem center_eq_of_core_eq_denominator
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (hb : ChapterC.IsShort L)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hXL : X ≤ L) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hodd : Odd (Nat.card X))
    (hfixed : V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G))
    (hpoint : V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0)
    (hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 = cohomologyDenominator T L V) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L :=
  center_eq_point_sup_fixed_of_le_denominator D S f X hXL hXR hodd hfixed hpoint
    ((radicalOmegaCenter_le_core D S hb f).trans hQ.le)

/-- The remaining strict-quotient obligation is a fixed-space bound on Q,
not a presumed decomposition of the omega center. -/
theorem center_eq_of_core_fixed_le_denominator
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (hb : ChapterC.IsShort L)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hXL : X ≤ L) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hodd : Odd (Nat.card X))
    (hfixed : V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G))
    (hpoint : V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0)
    (hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (f.Ri 0 : Set G) ≤
      cohomologyDenominator T L V) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L := by
  apply center_eq_point_sup_fixed_of_le_denominator D S f X hXL hXR hodd hfixed hpoint
  apply (le_inf (radicalOmegaCenter_le_core D S hb f) ?_).trans hQ
  intro z hz
  have hz' : z ∈ omegaCenterIn (f.Ri 0) :=
    (omegaCenterIn_eq_omegaOneAmbient (f.Ri 0)).symm ▸ hz
  exact ((mem_omegaCenterIn_iff _ _).mp hz').2.1

/-- Equality is handled before invoking the nonzero quotient calculation. -/
theorem center_eq_of_strict_quotient_calculation
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hXL : X ≤ L) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hodd : Odd (Nat.card X))
    (hfixed : V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G))
    (hpoint : V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0)
    (hstrict : Nontrivial (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
        ((cohomologyDenominator T L V).subgroupOf ((L ⊔ (T : Subgroup G)).pCoreIn 2))) →
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (f.Ri 0 : Set G) ≤
        cohomologyDenominator T L V) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L := by
  have hs : ChapterC.IsShort L := hb.elim (fun h => h.2.1) (fun h => h.1)
  rcases cohomology_quotient_split D S with he | hn
  · exact center_eq_of_core_eq_denominator D S hs f X hXL hXR hodd hfixed hpoint he
  · exact center_eq_of_core_fixed_le_denominator D S hs f X hXL hXR hodd hfixed hpoint
      (hstrict hn)

/-- Direct application to the parent assembly, with only the remaining point
geometry and strict cohomology calculation exposed. -/
theorem radicalAlternative_of_point_calculations
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L))
    (hgeometry : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      ∃ X : Subgroup G, X ≤ L ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
        Odd (Nat.card X) ∧
        (V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) ∧
        V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0)
    (hstrict : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      Nontrivial (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
        ((cohomologyDenominator T L V).subgroupOf ((L ⊔ (T : Subgroup G)).pCoreIn 2))) →
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (f.Ri 0 : Set G) ≤
        cohomologyDenominator T L V)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_source_steps D S f hblocks _ hfixed
  intro he hb
  obtain ⟨X,hXL,hXR,ho,hf,hp⟩ := hgeometry he hb
  exact center_eq_of_strict_quotient_calculation D S hb f X hXL hXR ho hf hp (hstrict he hb)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
