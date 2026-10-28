module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.Amalgam
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalGeometry
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# The original eight-dimensional section excludes the zero-core branch

The literal U_I/V₁ section of dimension at least eight has numerator of
order at least 512. Its coordinate map and kernel prove that numerator
is a two-group; its given I-normalization then places it in O₂(I).
The original local-star theorem makes the image of T in I/O₂(I) have
order divisible by four. Counting the kernel and image of the actual
map from T gives |T| ≥ 2048.

Combined with the source mixed-amalgam bound, this excludes zero core
for the actual original A₅ component and plane core closure. The dimension
premise is explicit and must come from the source module classification.
No abstract tensor or supplied F.1.1 configuration replaces that input.
Source: Aschbacher–Smith 14.7.42,46, printed pp.1061–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
open Chapter12.Section08 Chapter12.Section09.NaturalSource CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {I : Subgroup G}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The exact original section and star quotient give the Sylow lower bound,
using only structural input at the original G,T. -/
theorem sylow_card_ge_2048_of_local_section_rank_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (ρ : Representation (ZMod 2) I W)
    (s : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (hdim : 8 ≤ Module.finrank (ZMod 2) W) : 2048 ≤ Nat.card T := by
  let : Finite W := Finite.of_surjective (fun v : F.UH I => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hc : Nat.card (F.UH I) = 2 ^ (Module.finrank (ZMod 2) W + 1) := by
    rw [s.card_section,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      F.card 1 (by decide)]
    simp only [pow_succ,pow_zero,one_mul]
  have hp : IsPGroup 2 (F.UH I) := IsPGroup.of_card hc
  have hlarge : 512 ≤ Nat.card (F.UH I) := by
    rw [hc]
    calc
      512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ (Module.finrank (ZMod 2) W + 1) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  have hTI := F.sylow_le_of_mem_Hz hI
  let S := T.subtype hTI
  let q := QuotientGroup.mk' (pCore 2 I)
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  let A := (F.UH I).subgroupOf I
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer s.section_le).mpr s.normalized
  have hAc : A ≤ pCore 2 I := le_sSup ⟨inferInstance,hp.comap_subtype⟩
  have hAS : A ≤ (S : Subgroup I) := hAc.trans (pCore_isPGroup.le_sylow_of_normal S)
  let f := q.comp (S : Subgroup I).subtype
  let j : A → f.ker := fun a =>
    ⟨⟨a.val,hAS a.property⟩,(QuotientGroup.eq_one_iff a.val).mpr (hAc a.property)⟩
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : f.ker => x.val.val) he)
  have hker : 512 ≤ Nat.card f.ker := by
    apply hlarge.trans
    rw [←Nat.card_congr (subgroupOfEquivOfLe s.section_le).toEquiv]
    exact Nat.card_le_card_of_injective j hj
  have hfr : f.range = (Q : Subgroup (I ⧸ pCore 2 I)) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hrange : 4 ≤ Nat.card f.range := by
    rw [hfr]
    exact Nat.le_of_dvd Nat.card_pos
      (WholeResidualAssembly.four_dvd_local_star_sylow_card_at h hab structural I hI Q)
  have hcount : Nat.card f.ker * Nat.card f.range = Nat.card S := by
    rw [←index_ker]
    exact f.ker.card_mul_index
  have hST : Nat.card S = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTI).toEquiv
  calc
    2048 = 512 * 4 := rfl
    _ ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul hker hrange
    _ = Nat.card S := hcount
    _ = Nat.card T := hST

/-- The exact original rank-eight section rules out zero core in the generated
mixed pair. The remaining module-classification premise is only its dimension. -/
theorem original_mixed_core_ne_bot_of_section_rank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal)
    (ρ : Representation (ZMod 2) F.H W)
    (s : BinaryConjugationSection F.H (F.UH F.H) (F.Vi 1) ρ)
    (hdim : 8 ≤ Module.finrank (ZMod 2) W) :
    pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
  intro hcore
  have hu := original_mixed_zero_core_sylow_card_le d h hab structural previous faithful
    earlier C hC e hout hpoint hcore
  have hl := sylow_card_ge_2048_of_local_section_rank_at h hab (structural.at T)
    (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) ρ s hdim
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
