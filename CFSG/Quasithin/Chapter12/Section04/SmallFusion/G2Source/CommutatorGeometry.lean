module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.ActorCommutatorEndgame
public import Theory.Representation.BinaryConjugationCoordinates.ReciprocalNonStrong

/-!
# The original G₂ commutator obstruction

The full binary G₂ Weyl module has no strong offenders: every offender has
rank and fixed codimension three. If the original module and its conjugate
normalize each other, the two centralizer-index inequalities are equalities.
Their nontrivial action image is therefore an offender. The existing actor
commutator identity and fixed-involution fusion now give the contradiction.

This discharges the separate offender and balanced-index inputs of the
actor endgame. The source normalizer inclusion remains explicit.
Source: Aschbacher--Smith 12.4.9, printed p.816, using B.4.6(3),(13).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "σ" => traceZeroAction F
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem weyl_not_strong : ¬ IsStrongFFModule σ := by
  rintro ⟨A,hA⟩
  have hoff : IsOffender σ A := ⟨hA.1,hA.2.le⟩
  have hr := OrthogonalCover.BinaryOffenders.offender_rank A hoff
  have hc := OrthogonalCover.BinaryOffenders.offender_fixedCodim A hoff
  have hh := hA.2
  omega

/-- Original 12.4.9 for the binary G₂ Weyl row: a conjugate normalizing V
and not centralizing it cannot itself be normalized by V. The actual source
module and full normalizer actor discharge all model-geometry premises. -/
theorem lemma_12_4_9_of_g2_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (g : G)
    (hA : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hcommne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  obtain ⟨_,_,_,_,hMV,_,_⟩ := exists_fixed_involution_setup h D structural e hne
  obtain ⟨b,φ,hφ⟩ := exists_normalizer_full_g2_actor h D structural e hne
  have hAM : V.conjBy g ≤ normalizer (L : Set G) := hA.trans hMV.symm.le
  have he (a : normalizer (L : Set G)) (v : V) :
      (b (V.normalizerMonoidHom ⟨a.val,hMV.le a.property⟩ v)).toAdd =
        σ (φ a) (b v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    change (b.symm (b (V.normalizerMonoidHom ⟨a.val,hMV.le a.property⟩ v)) : G) = _
    rw [b.symm_apply_apply,hφ]
    change _ = (a : G) * (b.symm (b v) : G) * (a : G)⁻¹
    rw [b.symm_apply_apply]
    rfl
  intro hVA
  have hrecip : V ≤ (normalizer (L : Set G)).conjBy g := by
    change V ≤ (normalizer (L : Set G)).map (MulAut.conj g).toMonoidHom
    rw [hMV,map_equiv_normalizer_eq]
    exact hVA
  obtain ⟨hindex,hoff⟩ :=
    BinaryConjugationCoordinates.reciprocal_conjugate_offender_of_nonStrong
      (normalizer (L : Set G)) V hMV.le σ traceZeroAction_injective_binary
      φ b he weyl_not_strong g hAM hrecip hcommne
  exact lemma_12_4_9_of_offender_g2_actor h D structural e hne hNT b φ hφ g
    hAM hoff hindex hcommne hVA

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
