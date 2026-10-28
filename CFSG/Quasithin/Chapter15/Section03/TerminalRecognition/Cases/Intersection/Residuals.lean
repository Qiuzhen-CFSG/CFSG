module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Source
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Source

/-!
# Thompson containment and lifting the terminal residual

A nonzero two-subgroup generates a quasisimple generalized Fitting subgroup
by commutation. Applied to the image of J(T_E), this puts F*(H/O₂(H)) in
the actual Thompson image, before any residual identity is assumed.

Containment of the quotient residual then lifts through O₂(H): the marked
Sylow supplements the Thompson subgroup, its quotient is a two-group, and
idempotence of O² gives equality of the embedded residuals. Thus the
remaining model comparisons only need to establish the quotient residual
bound. The final adapter supplies that proved equality to the later
exceptional-action configuration without changing any marked subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; the component commutator argument is B.1.5(8).
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection

variable {H : Type*} [Group H] [Finite H]

/-- A quotient residual bound lifts to equality of the embedded residuals;
the two-core kernel is absorbed by the original Sylow subgroup. -/
theorem embedded_residual_eq_of_quotient_bound (T : Sylow 2 H) (X : Subgroup H) [X.Normal]
    (h : pResidual 2 (coreQuotient H) ≤ X.map coreProjection) :
    (pResidual 2 X).map X.subtype = pResidual 2 H := by
  let S : Sylow 2 (coreQuotient H) := T.mapSurjective (QuotientGroup.mk'_surjective _)
  have hm : (X ⊔ (T : Subgroup H)).map coreProjection = ⊤ := by
    rw [Subgroup.map_sup]
    apply top_unique
    exact (pResidual_sup_sylow_eq_top S).symm.le.trans (sup_le_sup_right h _)
  have hsup : X ⊔ (T : Subgroup H) = ⊤ := by
    have hc := congrArg (fun A : Subgroup (coreQuotient H) => A.comap coreProjection) hm
    rw [comap_map_eq, comap_top] at hc
    have hk : (coreProjection (H := H)).ker ≤ X ⊔ (T : Subgroup H) :=
      (QuotientGroup.ker_mk' _).le.trans
        ((pCore_isPGroup.le_sylow_of_normal T).trans le_sup_right)
    rwa [sup_eq_left.mpr hk] at hc
  have hr : pResidual 2 H ≤ X :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top X (T : Subgroup H) T.isPGroup' hsup⟩
  have hp : IsPPerfect 2 ((pResidual 2 H).subgroupOf X) :=
    (isPPerfect_pResidual (G := H) 2).of_surjective
      (subgroupOfEquivOfLe hr).symm.toMonoidHom (subgroupOfEquivOfLe hr).symm.surjective
  apply le_antisymm (map_pResidual_le 2 X.subtype)
  have hl := map_mono (f := X.subtype) (le_pResidual_of_isPPerfect _ hp)
  rwa [map_subgroupOf_eq_of_le hr] at hl

namespace SourceInput
variable {V : Subgroup H} (d : SourceInput V)

/-- Normality of the actual Thompson image in the quotient. -/
instance thompson_image_normal : ((thompsonGroup H).map coreProjection).Normal :=
  Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

include d

/-- The image of J(T_E) is the nontrivial two-subgroup needed by the
component commutator theorem; the normal Thompson image contains its commutators. -/
theorem fitting_le_thompson
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    generalizedFitting (coreQuotient H) ≤ (thompsonGroup H).map coreProjection := by
  have hJT : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup H) ≤ (d.T : Subgroup H) :=
    sSup_le fun _ hA => hA.1
  have hp := (d.T.isPGroup'.to_le hJT).map (coreProjection (H := H))
  rw [← ChapterB.QuasisimpleSections.commutator_fitting_eq
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
    hL d.sylow_thompson_image_ne_bot hp]
  exact (commutator_mono le_rfl
    (map_mono (Stellmacher.elementaryAbelianMaxJ_sylow_le_top d.T))).trans
      (commutator_le_right _ _)

/-- In quasisimple rows, only the quotient over F* needs to be a two-group. -/
theorem residual_eq_of_fitting_quotient
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hq : IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H))) :
    (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H :=
  embedded_residual_eq_of_quotient_bound d.T (thompsonGroup H)
    ((show pResidual 2 (coreQuotient H) ≤ generalizedFitting (coreQuotient H) from
      sInf_le ⟨inferInstance, hq⟩).trans (d.fitting_le_thompson hL))

/-- Full F* already forces the stronger identity of the Thompson image with
the whole quotient. No identification with the offender group was assumed. -/
theorem thompson_image_eq_top_of_fitting_top
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (htop : generalizedFitting (coreQuotient H) = ⊤) :
    (thompsonGroup H).map coreProjection = ⊤ :=
  top_unique (htop ▸ d.fitting_le_thompson hL)

/-- In the full-component rows, the residual equality needs no model computation. -/
theorem residual_eq_of_fitting_top
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (htop : generalizedFitting (coreQuotient H) = ⊤) :
    (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H := by
  apply embedded_residual_eq_of_quotient_bound d.T (thompsonGroup H)
  rw [d.thompson_image_eq_top_of_fitting_top hL htop]
  exact le_top

/-- In these rows both actors fill the quotient, as a consequence of the
component argument rather than an input to B.5.6. -/
theorem offender_eq_top_of_fitting_top [IsElementaryAbelian 2 (moduleClosure V)]
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (htop : generalizedFitting (coreQuotient H) = ⊤) : d.offenderGroup = ⊤ :=
  top_unique ((d.thompson_image_eq_top_of_fitting_top hL htop) ▸ d.thompson_image_le_offender)

/-- All original local subgroups and their equations pass unchanged to the
later action recognition, once the residual has actually been proved. -/
def toActionInput
    (hres : (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H) :
    ExceptionalAction.ActionRecognition.SourceInput V :=
  { d with thompson_residual := hres }

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
