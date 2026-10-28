module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceSingleEndgame
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.SourceSylow
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FixerNormalizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceAveraging
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SylowJoin
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CentralCommutator
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoreIdentification
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.MutualCentralizers
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Source
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingTerminal
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Terminal
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Maximum
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPhiNormalizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingNormalizerAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingSingleBlock
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Source
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCommutator
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamilyAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingOrbit
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.SingleBlockFrattini

/-!
# Source conjugate-module calculations

The alternating-five branch of C.5.6(1)–(4) is assembled here on the actual
C.5.3–4 configuration. The proof accommodates two blocks interchanged by R:
the intrinsic transvection subgroup preserves each module, and its inner
Sylow exchange excludes the isolated-transposition image. The ensuing
factorizations give the common commutator plane and Frattini invariance.

The rank-one and A₃ branches prove the same four clauses. The alternating
four-family calculation and the literal four-module orbit are also included.
The full C.5.7 normalizer and family conclusions are proved in both branches.
The unrestricted C.5.6(5)–(7) families are also assembled, including
the terminal two-core and full centralizer assertions for both marked
alternating modules and the original natural central covers.
Source: Aschbacher–Smith, C.5.6, printed pp.155–159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- All of C.5.6(1)–(4) in the A₅ branch, on the literal right-conjugate module.
The sole noncommutation input is exactly the preceding choice in C.5.5. -/
theorem lemma_C_5_6_alternating_1_to_4 (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    let E := ⁅U, S⁆
    Q = U ⊔ D ∧ D ≤ centralizer (V : Set G) ∧
    S = V ⊔ Q ∧ S = Q ⊔ Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
    E = ⁅U, V⁆ ∧ E = U ⊓ centralizer (V : Set G) ∧ E = U ⊓ V ∧
    E.map (MulAut.conj x⁻¹).toMonoidHom = E ∧
    ((frattini D).map D.subtype).map (MulAut.conj x⁻¹).toMonoidHom =
      (frattini D).map D.subtype := by
  have he := h.commutator_structure x hx hnc
  exact ⟨h.product, h.centralizer_centralizes_conjugate x hx hnc,
    h.first_factorization x hx hnc, h.core_conjugate_span x hx hnc,
    he.1, he.2.1, he.2.2.1, he.2.2.2, h.frattini_invariant x hx hnc⟩

/-- The other block's module centralizes the chosen conjugate. This supplies
the cross-commutation edge used in the four-module orbit argument of (7). -/
theorem AlternatingPairSetup.other_module_centralizes_conjugate
    (h : AlternatingPairSetup R K L) (hLS : sourceModule L ≤ ChapterB.baumann R)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    sourceModule L ≤ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) :=
  (le_inf hLS ((map_subtype_le _).trans h.commute)).trans
    (h.centralizer_centralizes_conjugate x hx hnc)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
