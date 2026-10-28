module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveFaithfulSylow
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults

/-!
# The native Mathieu local row excludes an A₅ section in J₄

The literal binary kernel of max1 gives its actual M₂₄ quotient. A solvable
kernel preserves the original local C-component and its A₅ two-core quotient.
The image with nontrivial two-core is excluded by the M₂₄ local geometry;
with trivial two-core it is an actual A₅, whose faithful full-Sylow action
contradicts the order of M₂₄. Both original subgroups and Sylow actors are
retained by the ambient restriction theorem.

Source: Aschbacher--Smith A.3.12(17) and the A₅ point inspection in 10.2.9,
printed pp.47--48 and750--751; GLS3 Table5.3i for the native max1 quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
open SolvableQuotients Janko4 Janko4.Cardinality Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
local notation "K" => localKernel matrixA_mul_self matrixB_pow_four

private theorem m24_not_section (S : Sylow 2 Sporadic.Mathieu.M24)
    (B : Subgroup Sporadic.Mathieu.M24) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Sporadic.Mathieu.M24) ≤ normalizer (B : Set Sporadic.Mathieu.M24))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  by_cases hc : pCore 2 B = ⊥
  · let e : B ≃* alternatingGroup (Fin 5) :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans eB)
    apply AlternatingFive.not_sixteen_dvd_of_evenCharacteristic S
      (MainConverse.m24_evenCharacteristic S) hl hn e
    rw [Sporadic.Mathieu.m24_order]
    decide
  · exact MathieuTwentyFour.not_section (MulEquiv.refl _) S B hl hn hc eB

/-- No local C-component normalized by a full Sylow of the native max1
carrier has two-core quotient A₅. No module recognition is required. -/
theorem max1_not_section (S : Sylow 2 M) (B : Subgroup M)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup M) ≤ normalizer (B : Set M))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let q := (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' K)
  have hq : Function.Surjective q :=
    (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).surjective.comp
      (QuotientGroup.mk'_surjective K)
  have hk : q.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).injective,
      QuotientGroup.ker_mk']
  let : Group.IsSolvable q.ker := by
    rw [hk]
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    let : Group.IsNilpotent K := (IsElementaryAbelian.isPGroup 2 K).isNilpotent
    infer_instance
  exact m24_not_section (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono (f := q) hn).trans (B.le_normalizer_map q))
    (section_map q B hl eB).some

/-- The actual pair consisting of the source local subgroup and its full
normalizing Sylow cannot both lie in literal max1. -/
theorem not_pair_le_max1 (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hBM : B ≤ M) (hSM : (S : Subgroup Model) ≤ M) : False := by
  let d := subgroupOfEquivOfLe hBM
  apply max1_not_section (S.subtype hSM) (B.subgroupOf M)
    (local_restrict hl hBM) _
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)
  intro s hs
  apply mem_normalizer_iff.mpr
  intro b
  exact mem_normalizer_iff.mp (hn hs) (b : Model)

/-- The same exclusion through an actual ambient equivalence, including a
chosen conjugation of max1. -/
theorem not_pair_map_le_max1 {G : Type*} [Group G] [Finite G]
    (f : G ≃* Model) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hBM : B.map f.toMonoidHom ≤ M)
    (hSM : (S : Subgroup G).map f.toMonoidHom ≤ M) : False := by
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  exact not_pair_le_max1 (S.mapSurjective (f := f.toMonoidHom) f.surjective)
    (B.map f.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom)
    ((map_mono (f := f.toMonoidHom) hn).trans (B.le_normalizer_map f.toMonoidHom))
    (section_map f.toMonoidHom B hl eB).some hBM hSM

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
