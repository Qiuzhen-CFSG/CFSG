module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairReduced
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import Theory.GroupAction.IrreduciblePerfectContainment

/-!
# Core containment from the actual DGS Frattini action

If the core of an original F.1.1 parabolic has irreducible Frattini quotient,
an A5-marked original factor contains that entire core. The parabolic's
solvable residual is perfect and nontrivial, since it maps onto the A5
quotient of the factor. Characteristic two and irreducibility therefore
place the core in that residual, which already lies in the original factor.
This proves equality of the cores, and Borel normalization gives S ≤ Lᵢ.
No perfectness or splitting of the original factor is assumed.

The input action is on the intrinsic core of the full original parabolic,
including the odd Borel. DGS (10.10)(d), p.164, identifies the relevant
nonbinary core section with this Frattini quotient in its beta orientation.
The shared DGS branch and original-extension producers must establish that
input on the literal parabolic. This module does not assert it for every
endpoint or prove the other DGS branches.

Source: DGS85, Groups and Graphs, Part II, (10.10)(d), p.164;
Aschbacher--Smith, F.1.12, pp.262--264. Final source discharge belongs to
qt-d-tensor-a5-amalgam, using qt-dgs85-source-assembly and its profile and
original-extension inputs.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
namespace HypothesisF11

/-- The full parabolic core is the original core when its Frattini action
is irreducible. The original A5 marking supplies nontriviality of the residual. -/
theorem a5_parabolic_core_eq_of_frattini_irreducible (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hirr : IsNormalizerFrattiniIrreducible (pCore 2 (parabolic L S i))) :
    twoCore (parabolic L S i) = twoCore (L i) := by
  let P := parabolic L S i
  let f : L i →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (L i)))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hne : solvableResidual P ≠ ⊥ := by
    intro he
    have hl : (solvableResidual (L i)).map (L i).subtype = ⊥ := by
      rw [h.local_residual_eq_parabolic i, he, Subgroup.map_bot]
    have hr : solvableResidual (L i) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (L i).subtype_injective).mp hl
    have hm := map_solvableResidual_eq f hf
    rw [hr, Subgroup.map_bot, solvableResidual_eq_top] at hm
    exact bot_ne_top hm
  let : Nontrivial (solvableResidual P) := (nontrivial_iff_ne_bot _).mpr hne
  have hQR : pCore 2 P ≤ solvableResidual P :=
    IsNormalizerFrattiniIrreducible.le_perfect_normal_of_selfCentralizing
      (pCore 2 P) (solvableResidual P) pCore_isPGroup hirr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i))
  have hQL : twoCore P ≤ L i :=
    (map_mono hQR).trans (h.parabolic_residual_le_local i)
  rw [← h.local_inf_parabolic_core i, inf_eq_right.mpr hQL]

/-- The reduced DGS core is the original factor core, with the full Borel
retained in the irreducibility hypothesis. -/
theorem a5_localJoin_core_eq_of_frattini_irreducible (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hirr : IsNormalizerFrattiniIrreducible (pCore 2 (parabolic L S i))) :
    twoCore (L i ⊔ S) = twoCore (L i) := by
  rw [h.localJoin_twoCore_eq_parabolic hn i]
  exact h.a5_parabolic_core_eq_of_frattini_irreducible i e hirr

/-- The literal F.1.12 local containment from the DGS Frattini profile
at the same endpoint; the opposite endpoint is not substituted. -/
theorem a5_local_containment_of_frattini_irreducible (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hirr : IsNormalizerFrattiniIrreducible (pCore 2 (parabolic L S i))) :
    S ≤ L i :=
  (h.a5_local_containment_iff_core_eq i e (hn i)).mpr
    (h.a5_localJoin_core_eq_of_frattini_irreducible hn i e hirr)

end HypothesisF11
end CFSG.Quasithin.ChapterF.Source
