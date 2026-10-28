module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.RecognitionKnownSimple
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.Representation.BinaryPermutation.FiveCentralExtension

/-!
# Recognition from the original A₅ point closure

The sum of the twenty three-cycle operators shows C_V(L)=1 on the
original marked module. Its source TI property then implies that a point
centralizer contained in N_G(L) normalizes V. Nonabelian full closure
therefore forces that centralizer into the actual H_z family. The proved
13.5.10 equivalence and the complete A₅ recognition now apply without an
escape, F.9, normality or embedding premise.

The seed version uses the literal G₁=N_G(V₁), equal to C_G(V₁) because
|V₁|=2. Construction of the marked Context remains earlier preparation.
Source: Aschbacher–Smith, 13.5.10–12, printed p.918.
-/

public section
open Subgroup Theory.GroupTheory
open scoped BigOperators IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
private theorem fixed_all_zero (w : Space)
    (hw : ∀ a : alternatingGroup (Fin 5), coreRepresentation (Fin 5) a.val w = w) :
    w = 0 := by
  have he := FiveCentralExtension.core_sum w
  rw [Finset.sum_congr rfl (fun a ha => hw ⟨a,FiveCentralExtension.cubes_even a ha⟩),
    Finset.sum_const,FiveCentralExtension.cubes_card] at he
  have hz : 20 • w = 0 := by
    rw [←Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (20 : ZMod 2) • w = 0
    rw [show (20 : ZMod 2) = 0 from rfl,zero_smul]
  exact he.symm.trans hz

include d in
 private theorem fixed_free : V ⊓ centralizer (L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨w,rfl⟩ := d.flag.module.range_eq.ge hx.1
  have hw : ∀ a : alternatingGroup (Fin 5),
      coreRepresentation (Fin 5) a.val w.toAdd = w.toAdd := by
    intro a
    obtain ⟨l,hl⟩ := d.flag.module.onto a
    apply Multiplicative.ofAdd.injective
    apply d.flag.module.injective
    have he := d.flag.module.equivariant l w.toAdd
    rw [hl] at he
    rw [←he]
    change l.val * d.flag.module.map w * l.val⁻¹ = d.flag.module.map w
    rw [mem_centralizer_iff.mp hx.2 l.val l.property,mul_inv_cancel_right]
  have hw1 : w = 1 := congrArg Multiplicative.ofAdd (fixed_all_zero w.toAdd hw)
  rw [hw1,map_one]
  exact one_mem _

include d in
 private theorem point_escape_of_nonabelian_full
    (hU : ¬ IsMulCommutative (conjugateSpanBy V (centralizer (V₁ : Set G)))) :
    ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G) := by
  intro hC
  have hP : V₁ ≠ ⊥ := by
    intro he
    have hh := d.flag.one_card
    simp [he] at hh
  have hPV := d.flag.one_le_two.trans d.flag.two_le_V
  have hTI := d.chosen.ti_of_centralizer_eq_bot
    (Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient)
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) (fixed_free d)
  have hCV : centralizer (V₁ : Set G) ≤ normalizer (V : Set G) :=
    (le_inf hC (Subgroup.centralizer_le_normalizer _)).trans
      (inf_normalizer_le_of_trivial_intersections hTI hP hPV)
  have hUV := conjugateSpanBy_le (show V ≤ V from le_rfl) hCV
  let := d.elementary
  exact hU (le_centralizer_iff_isMulCommutative.mp
    (hUV.trans ((le_centralizer V).trans (centralizer_le hUV))))

include d in
private theorem point_family_of_nonabelian_full
    (hU : ¬ IsMulCommutative (conjugateSpanBy V (centralizer (V₁ : Set G)))) :
    centralizer (V₁ : Set G) ∈ Section08.Source.Hz
      (Section06.TerminalContradiction.Ratio.residualCentralizer L V₁)
      (T : Subgroup G) (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
  have hTZ : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  have hlineT : V₁ ≤ (T : Subgroup G) :=
    d.flag.one_le_two.trans (d.flag.two_le_V.trans d.chosen.le_sylow)
  have hc : V₁ ≤ (centralizer (V₁ : Set G)).pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hlineT) (hlineT.trans hTZ) (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨?_,sup_le ((map_subtype_le _).trans inf_le_right) hTZ⟩,le_rfl,
    point_escape_of_nonabelian_full d hU⟩
  intro he
  have hb := bot_unique (hc.trans_eq he)
  have hcard := d.flag.one_card
  rw [hb,card_bot] at hcard
  contradiction

include d in
/-- Nonabelian full point closure gives the two genuine degree-five models. -/
theorem source_point_full_modelConclusion
    (hU : ¬ IsMulCommutative (conjugateSpanBy V (centralizer (V₁ : Set G)))) :
    ModelConclusion G 5 := by
  let := d.elementary
  have hH := point_family_of_nonabelian_full d hU
  exact source_modelConclusion_knownSimple d hH
    (fun hs => hU ((source13_5_10_knownSimple d hH).1.1.mp hs))

include d in
/-- Clause (1) of 13.5.12 for the original marked A₅ Context. -/
theorem source_point_seed_modelConclusion
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ (normalizer (V₁ : Set G)))) :
    ModelConclusion G 5 := by
  apply source_point_full_modelConclusion d
  intro hV
  let := hV
  have he : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
      (Subgroup.centralizer_le_normalizer _)
  rw [he] at hU
  exact hU (conjugateSpanBy_isMulCommutative_of_le d.third_le le_rfl)
end CFSG.Quasithin.Chapter13.Section05.A5Source
