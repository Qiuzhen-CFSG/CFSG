module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Source
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Extension

/-!
# The marked orthogonal action on the original seed span

The complete corrected B.5.1 implication first recognizes the literal
[W_K,K]/C_[W_K,K](K) under the entire plus actor. Odd-coset averaging
extends its coordinates to W_K with precisely the K-fixed kernel. The
Sylow-fixed original seed then selects a four-block marking; rotating the
actor and moved-section coordinates together preserves their equivariance.
We extend the rotated coordinates canonically to retain one marking on
both the moved section and the original seed span.

The resulting theorem identifies the actual seed stabilizer and C_K(z)
image, and the checked exceptional equivalence sends the latter to the
end-node parabolic. The explicit natural/orthogonal comparison gives the
six-dimensional orthogonal coordinates for that same actor. In particular
neither a splitting nor a dimension-only recognition is an input.

Only the genuine earlier configuration and full corrected universal B.5.1
remain explicit in the marking theorem. Their producers are
qt-13-06-rank-four-source-selection and qt-b05-quasisimple, and their final
discharge belongs to qt-13-06-orthogonal-marked-local-action. The kernel
export additionally consumes the simultaneous intrinsic marking
K/O₂(K) ≃ SL₄(2) from Selection.source_rankFour_selection. Comparing its
order with K⁺ and using the two-group supplement proves the literal plus
kernel is a two-group, discharging the residual/core transport premise.
No wreath quotient or Thompson equality is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23 and its following paragraph, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
open ComponentSelection Theory.SpecificGroups.SymmetricEight
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
    {Ξ : GroupClass.{u}} {K L V : Subgroup G} {T : Sylow 2 G} {z v : G}
    (c : Recognition.SourceAction.Configuration Ξ K L V T z v)

/-- Apply the kernel comparison to the genuine source configuration and
its intrinsic quotient marking. The latter is an earlier source-selection
output; an abstract isomorphism for K⁺ alone would not suffice. -/
theorem source_plusMk_kernel_isPGroup
    (eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2)) :
    IsPGroup 2 (plusMk K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed).ker :=
  plusMk_kernel_isPGroup K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    c.invariant c.lv_le (T.isPGroup'.to_le inf_le_left) (eK.trans c.linear_four.symm)

/-- The actual residual/core consumer, with its two-group kernel premise
discharged. The residual is O^{3′}(C_K(z)), with the original plus map. -/
theorem source_residual_join_core_image
    (eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2)) :
    plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
        ((Source.orthogonalResidual K z ⊔ Tv (T : Subgroup G) v).pCoreIn 2) =
      (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          (Source.orthogonalResidual K z) ⊔
        plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          (Tv (T : Subgroup G) v)).pCoreIn 2 :=
  residual_join_core_image K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    (source_plusMk_kernel_isPGroup c eK)

variable (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)
include classification

/-- Construct compatible moved and seed sections from the full source
hypotheses. Their one actor marks the original seed, its literal component
centralizer and the end-node parabolic. The seed projection is surjective,
fully equivariant, has exactly the K⁺-fixed kernel, and restricts to the
chosen coordinates on the actual U_K/C_{U_K}(K). -/
theorem source_marked_sections :
    letI := c.elementary
    ∃ (d : NaturalMovedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed)
      (s : NaturalSeedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed),
      s.actor = d.actor ∧
      (∀ w : d.upper.toSubmodule,
        s.projection w.val = d.coordinates (d.central.toSubmodule.mkQ w)) ∧
      (∀ w : Additive (WK K L (T : Subgroup G) z v), w ∈ d.upper.toSubmodule ↔
        (w.toMul : G) ∈ UX L z v (starImage z v K)) ∧
      (seedStabilizer K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed).map
        d.actor.toMonoidHom = A6ShadowTwoLocals.fourStabilizer ∧
      (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed (K ⊓ Gv z)).map
        d.actor.toMonoidHom = alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer ∧
      (((plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed (K ⊓ Gv z)).map
        d.actor.toMonoidHom).subgroupOf (alternatingGroup (Fin 8))).map
          FourBlockParabolic.equiv.toMonoidHom = BinaryLinear.parabolic FourBlockParabolic.plane := by
  let := c.elementary
  obtain ⟨d⟩ := Recognition.source_naturalMovedSection c classification
  obtain ⟨r, hseed, hcent, hpar⟩ := exists_compatible_marking_of_movedSection
    K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.selected c.invariant c.lv_le c.sylow d
  let d' := d.conjugate K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed r
  obtain ⟨s, hs, hext⟩ := exists_naturalSeedSection K L (T : Subgroup G) z v
    c.lv_invariant c.seed_fixed c.selected.1.1 c.invariant c.lv_le c.sylow d'
  refine ⟨d', s, hs, hext, ?_, hseed, hcent, hpar⟩
  intro w
  exact (d'.upper_mem w).trans
    ((Recognition.movedSection_upper_mem K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.invariant c.lv_le w).symm.trans
        (Recognition.movedSection_upper_source K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          c.selected c.invariant c.lv_le w))

/-- The marked representation and centralizer branch following 13.6.23.
The same chosen actor identifies K⁺ with A₈ (via d.component_image), gives
orthogonal coordinates on the literal U_K/C_{U_K}(K), and marks the
stabilizer of z in W_K before quotienting by fixed vectors. The final
parabolic uses the checked exceptional equivalence, not an unrelated
SL₄(2) marking. Universal B.5.1 and earlier source selection remain explicit. -/
theorem source_orthogonal_seed_marking :
    letI := c.elementary
    ∃ d : NaturalMovedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
      (∀ w : Additive (WK K L (T : Subgroup G) z v), w ∈ d.upper.toSubmodule ↔
        (w.toMul : G) ∈ UX L z v (starImage z v K)) ∧
      Module.finrank (ZMod 2) (d.upper.toSubmodule ⧸ d.central.toSubmodule) = 6 ∧
      (∀ g w, d.orthogonalCoordinates K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          (d.central.quotientRepresentation g w) =
        (Atlas.Order20160A8.DeletedEight.orthogonalHom (d.actor g)).val
          (d.orthogonalCoordinates K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed w)) ∧
      (seedStabilizer K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed).map
        d.actor.toMonoidHom = A6ShadowTwoLocals.fourStabilizer ∧
      (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed (K ⊓ Gv z)).map
        d.actor.toMonoidHom = alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer ∧
      (((plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed (K ⊓ Gv z)).map
        d.actor.toMonoidHom).subgroupOf (alternatingGroup (Fin 8))).map
          FourBlockParabolic.equiv.toMonoidHom = BinaryLinear.parabolic FourBlockParabolic.plane := by
  let := c.elementary
  obtain ⟨d, _, _, _, hu, hseed, hcent, hpar⟩ := source_marked_sections c classification
  exact ⟨d, hu, d.section_finrank K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
    d.orthogonal_equivariant K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
    hseed, hcent, hpar⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
