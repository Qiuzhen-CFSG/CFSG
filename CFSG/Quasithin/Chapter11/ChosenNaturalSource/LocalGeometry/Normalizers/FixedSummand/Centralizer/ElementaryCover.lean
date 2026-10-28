module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.JankoPlacements
public import Theory.GroupTheory.MaximalTwoLocalElementary

/-!
# The ordinary full-module exclusion from uniform native J4 coverage

The literal projected radical P is nontrivial and two-radical. Choose a
maximal two-local above its full normalizer and express that local as the
normalizer of a nonzero elementary abelian subgroup. The uniform native
cover then places all of N(P) in one of the four actual local types.
The existing Mathieu, first-centralizer and symmetric-linear obstructions
exclude three rows. Since the projected covering residual normalizes P,
the existing literal PSL5(2)-quotient obstruction excludes the fourth.

The cover is an independent native theorem, explicitly retained here.
Its producer is qt-model-j4-elementary-normalizer-cover, which must supply
the actual embedded C and its quotient equivalence and prove this uniform
statement from intrinsic symmetry. The symmetry is owned by
qt-model-j4-large-center-radicals. This file proves neither native input.
The original source theorem remains with qt-d-1222-natural-point-fixed-summand
until both are discharged; the ordinary odd-normalizer application is
provided to qt-d-1222-natural-odd-kernel-normalizer in the same module.

All C.2.8 hypotheses, the full W, covering B, and inclusion-compatible
quotient remain unchanged. No shortness, W=V or order-64 premise is added.
Only ordinary prerequisites are imported, so both source consumers can use
this result without an import cycle.

Source: Aschbacher--Smith C.3.5, printed pp.150--151, and the local
inspections in 4.2.13 and 4.4.12, pp.611--612,622. The independent native
coverage contract uses Kleidman--Wilson, *The maximal subgroups of J4*,
Proc. LMS 56 (1988), 484--510, and its actual four embedded locals.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open WeakClosure.Generation

/-- Uniform full-normalizer coverage, independent of the chosen source group.
C is the native producer's embedded linear-five local; its literal core
quotient equivalence is supplied separately to each consumer. The other
three rows are fixed native subgroups, with actual conjugators. -/
def JankoElementaryNormalizerCover (C : Subgroup Janko4.Model) : Prop :=
  ∀ E : Subgroup Janko4.Model, E ≠ ⊥ → IsElementaryAbelian 2 E →
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
        Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      C.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Janko4.Model, normalizer (E : Set Janko4.Model) ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The J4 row is impossible once the independent uniform cover is supplied.
The cover is applied above the full normalizer of the actual projected radical. -/
theorem c28_covering_jankoFour_false_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) : False := by
  let P₀ := (ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))
  let P := P₀.map ek.toMonoidHom
  have hP : IsPRadical 2 P := (ordinary_projected_radical h K hK).map_equiv ek
  have hlocal : IsTwoLocal (normalizer (P : Set Janko4.Model)) :=
    ⟨P,hP.1,hP.isPGroup,rfl⟩
  obtain ⟨N,hPN,hN⟩ := hlocal.exists_le_maximal
  obtain ⟨E,hE,hEE,hEN⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hN
  have hPE : normalizer (P : Set Janko4.Model) ≤ normalizer (E : Set Janko4.Model) :=
    hPN.trans_eq hEN
  have hex := c28_covering_jankoFour_radical_normalizer_avoids_locals D S h hstrict hn
    hBL hc hVB e he K hK ek
  rcases hcover E hE hEE with ⟨g,hg⟩ | ⟨g,hg⟩ | ⟨g,hg⟩ | ⟨g,hg⟩
  · exact (hex g).1 (hPE.trans hg)
  · exact (hex g).2.1 (hPE.trans hg)
  · have hXN := (map_mono (f := ek.toMonoidHom)
        (ordinary_projected_cover_normalizes_radical h hn K hK)).trans
        (P₀.le_normalizer_map ek.toMonoidHom)
    exact c28_covering_jankoFour_avoids_linear_five D S h hBL hc hVB e K hK ek C eC g
      (hXN.trans (hPE.trans hg))
  · exact (hex g).2.2 (hPE.trans hg)

/-- The shared ordinary C.2.8 contradiction for the full covering residual.
The established Ru exclusion and J4 cover application discharge both models. -/
theorem c28_covering_ordinary_false_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨⟨ek⟩,_⟩ := c28_covering_ordinary_jankoFour D S h hBL hc hVB e K hK
  exact c28_covering_jankoFour_false_of_elementary_cover C eC hcover D S h hstrict hn
    hBL hc hVB e he K hK ek

/-- Literal ordinary odd-normalizer application with B=(L ∩ H)^∞ and
the constructor's whole W. The original quotient compatibility is retained. -/
theorem no_pushingUpFieldFourCase_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) (A : Subgroup G) :
    ¬ OddNormalizer.PushingUpFieldFourCase D S A := by
  rintro ⟨J,H,W,_,_,_,hstrict,_,hC,hc,hn,hVB,⟨e,he⟩,_,_,_,_,_,_,K,hK,_⟩
  exact c28_covering_ordinary_false_of_elementary_cover C eC hcover D S hC hstrict hn
    ((map_subtype_le _).trans inf_le_left) hc hVB e he K hK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
