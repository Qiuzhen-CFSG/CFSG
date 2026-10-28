module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import Theory.Representation.HexacodeAction.CoverComparison
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Prescribed A₆ projection of the original local component

The standing natural action identifies the quotient of L by the full
preimage of the center with A₆. The component hypothesis makes L/O₂(L)
a perfect central cover with odd center, hence either ordinary A₆ or the
unique cubic cover. Schur cover comparison is performed over the given
projection, so the resulting equivalence retains the original action on V.
This is the group-marking part of Notation 13.2.1 and 13.2.2; the compatible
Sylow flag and residual factorization are separate source conclusions.

Source: Aschbacher–Smith, printed pp.876–878.
-/

@[expose] public section

open Subgroup Theory.GroupTheory GLS3.Chapter5.SchurPresentation
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The central quotient retains the prescribed natural A₆ projection. -/
noncomputable def local_central_quotient :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := (QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp q
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = centralCore L := by
    change ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp q).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : (L ⧸ centralCore L) ≃* ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact e.symm.trans d.local_quotient

theorem local_central_quotient_apply (l : L) :
    local_central_quotient d
      (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) (QuotientGroup.mk' (pCore 2 L) l)) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l) := by
  unfold local_central_quotient
  change d.local_quotient _ = d.local_quotient _
  congr 1
  apply (Equiv.symm_apply_eq _).mpr
  rfl

theorem local_quotient_quasisimple : IsQuasisimple (L ⧸ pCore 2 L) := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
    d.counterexample.local_component.1.1.perfect
  let e : (L.subgroupOf (L ⊔ (T : Subgroup G))) ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact { toIsPerfect := inferInstance, simple := (local_central_quotient d).isSimpleGroup }

theorem local_odd_center_alternatives :
    Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨ Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  let := local_quotient_quasisimple d
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) := by
    exact Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (local_central_quotient d) ho with hc | ⟨_,hc⟩
  · exact Or.inl hc
  · exact Or.inr hc

/-- The original component is ordinary A₆ or the concrete triple cover,
with the same projection to the six-letter action in either case. -/
theorem local_quotient_alternatives :
    (∃ e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6),
      ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l)) ∨
    (∃ e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      ∀ l : L, Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l)) := by
  let := local_quotient_quasisimple d
  rcases local_odd_center_alternatives d with hc | hc
  · let e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq ((eq_bot_iff_card _).mpr hc).symm).trans
          (local_central_quotient d))
    refine Or.inl ⟨e, ?_⟩
    intro l
    change (local_central_quotient d) (QuotientGroup.mk' (center (L ⧸ pCore 2 L))
      (QuotientGroup.mk' (pCore 2 L) l)) = _
    exact local_central_quotient_apply d l
  · let f : Covering (L ⧸ pCore 2 L) (alternatingGroup (Fin 6)) := {
      toMonoidHom := GLS3.Chapter5.alternatingQuotientHom (local_central_quotient d)
      surjective := (local_central_quotient d).surjective.comp
        (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))) }
    have hk : Nat.card f.toMonoidHom.ker = 3 := by
      have he : f.toMonoidHom.ker = center (L ⧸ pCore 2 L) := by
        ext x
        simp [f, GLS3.Chapter5.alternatingQuotientHom]
      rw [he]
      exact hc
    obtain ⟨e, he⟩ := Representation.Hexacode.CoverComparison.exists_even_equiv_over_coordinate f hk
    refine Or.inr ⟨e, ?_⟩
    intro l
    have h := congrArg (fun F : (L ⧸ pCore 2 L) →* alternatingGroup (Fin 6) =>
      F (QuotientGroup.mk' (pCore 2 L) l)) he
    change Atlas.Codes.hexEvenCoordinate (e (QuotientGroup.mk' (pCore 2 L) l)) =
      local_central_quotient d
        (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) (QuotientGroup.mk' (pCore 2 L) l)) at h
    exact h.trans (local_central_quotient_apply d l)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
