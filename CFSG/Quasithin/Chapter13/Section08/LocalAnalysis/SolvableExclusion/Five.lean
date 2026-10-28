module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.PrimeReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.FixedSpace
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.DisjointSummands
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FactorData
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Supports
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.RankTwo
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FiveCentralizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization

/-!
# The five-primary contradiction in 13.8.13

The imported modules provide the literal H/O₂(H)-action on U_H/V₁,
its exact restricted commutator images, the common-center bound that
excludes the rank-two factor action, and canonical lifts of quotient
summands. The theorem below derives triviality on the second summand
from the source local bounds, constructing both relative normalizers,
the moved-space noncontainment, and normalization of its inverse image.

`reducedFive_false` completes this branch from `ReducedFive`, minimal solvable
membership in the genuine Hz family, the standing source setup and the earlier
source conclusions. The source kernel constructs the faithful action; the
factor construction supplies the rank-one factors; and localization constructs
the symmetry, generation, second actor and every remaining local bound.
The resulting moved point contradicts fixation of that same second support.

The universal D.2.13(1–2) input is the checked alternative to applying D.2.17
directly to H*. Its producer is `qt-d-02`; the universal F.9 geometry producer
is `qt-f09-geometry`. The earlier 13.8.5 and 13.8.8 conclusions remain explicit.
The parent solvable-overgroup theorem must supply these source inputs and
construct `ReducedFive` using its three-primary reduction. This module proves
the conditional five-primary exclusion, not the other branches of 13.8.13.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968). The final contradiction compares the fixed
second summand below with its nontrivial B₂-action from the factor analysis.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

/-- The final local bounds force B₂ to fix the actual second summand.
The factor construction must separately prove that it moves that summand. -/
theorem StarAction.second_summand_fixed [IsMulCommutative UH]
    (a : StarAction H UH V₁) (Uγ Vγ A₁ B₂ : Subgroup G)
    (S₁ S₂ : Subgroup (UH ⧸ V₁.subgroupOf UH))
    (hVγ : Vγ ≤ H) (hB₂ : B₂ ≤ Vγ)
    (hA : A₁ ≤ UH) (hV : V₁ ≤ UH) (hAcard : Nat.card A₁ = 2)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2)
    (hmoved : 2 < Nat.card (tildeImage UH V₁ ⁅UH, Uγ⁆))
    (hdis : Disjoint V₁ A₁)
    (hfixed : ⁅liftTilde UH V₁ S₂, Uγ⁆ ≤ V₁)
    (h13737 : ⁅UH ⊓ centralizer (Uγ : Set G), Vγ⁆ ≤ A₁)
    (hinvariant : ∀ b : a.actors Vγ, ∀ x ∈ S₂, b • x ∈ S₂)
    (hline : tildeImage UH V₁ A₁ ≤ S₁) (hsum : Disjoint S₁ S₂) :
    ∀ b : a.actors B₂, ∀ x ∈ S₂, b • x = x := by
  have hnA : UH ≤ normalizer (A₁ : Set G) :=
    ((UH.le_centralizer).trans (centralizer_le hA)).trans (Subgroup.centralizer_le_normalizer _)
  have hnV : UH ≤ normalizer (V₁ : Set G) :=
    ((UH.le_centralizer).trans (centralizer_le hV)).trans (Subgroup.centralizer_le_normalizer _)
  have hnon := moved_not_le_line_sup_denominator Uγ A₁ hA hV hAcard hmoved
  have hn₂ := a.normalizes_liftTilde Vγ hVγ S₂ hinvariant
  have hline' : tildeImage UH V₁ A₁ ≤ tildeImage UH V₁ (liftTilde UH V₁ S₁) := by
    rwa [tildeImage_liftTilde]
  have hsum' : Disjoint (tildeImage UH V₁ (liftTilde UH V₁ S₁))
      (tildeImage UH V₁ (liftTilde UH V₁ S₂)) := by
    simpa only [tildeImage_liftTilde] using hsum
  have he := second_summand_commutator_image_eq_bot UH Uγ Vγ A₁ V₁
    (liftTilde UH V₁ S₁) (liftTilde UH V₁ S₂) B₂ hindex hnA hnV hnon hdis
    (liftTilde_le UH V₁ S₂) hfixed h13737 hB₂ hn₂ hline' hsum'
  intro b x hx
  by_contra hn
  apply a.commutator_image_ne_bot_of_moves (liftTilde UH V₁ S₂) B₂
    (liftTilde_le UH V₁ S₂) (hB₂.trans hVγ) ?_ he
  exact ⟨b, x, (tildeImage_liftTilde UH V₁ S₂).symm ▸ hx, hn⟩

open CriticalGeometry CriticalGeometry.Reorientation
open CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
open Representation.BinaryOffender
open Three.Supercritical.Offenders
open scoped IsMulCommutative

/-- The five-primary branch is impossible for the prescribed source action.
The proof constructs the factors and every localization premise. In particular,
neither a rank-one actor nor the nontrivial second-factor action is assumed. -/
theorem reducedFive_false_of_action
    {L V V₃ L₁ G₁ M Vα : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (src : SourceD213PrimeInput.{u})
    (reduced : ReducedFive H L₁ T M Vα)
    (c : CriticalPair L T H V)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hqt : _root_.IsQuasithin G)
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hs : Group.IsSolvable H)
    (s : SourceInputs c V₃ V₁ L₁ G₁ M)
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hQ : Source.starImage H (c.Ugamma V₃) ∈ ChapterD.Q (linearAction a))
    (h135 : (∃ h : H, (centerAction a).action h ≠ 1 ∧
      binaryLinear ((centerAction a).action h) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      FullModelConclusions L L₁ T (le_sup_left.trans hminimal.prop.1.2) (centerAction a))
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    False := by
  have hf := a.injective_of_kernel hk
  obtain ⟨f⟩ := rankOneFactors_of_critical_pair src reduced c a hqt hminimal hs
    s.seed_le s.line_seed s.line_card s.line_normalized hk (s.geometry c)
    s.selected_rank hQ hplacement
  obtain ⟨geo, second, hfixed, hinvariant, ⟨b, w, hw, hmoved⟩, hdisjoint, hcard⟩ :=
    Localization.exists_localization c a hf reduced f hminimal hs s h135 hplacement
  exact hmoved (a.second_summand_fixed (c.Ugamma V₃) c.Vgamma (c.Aone V₁) second.B₂
    (f.factors.support ⟨0, f.factors.count_pos⟩) (f.factors.support second.second)
    geo.Vgamma_le second.B₂_le geo.Aone_le geo.Vone_le geo.Aone_card geo.DH_index
    hcard geo.lines_disjoint hfixed geo.centralizer_commutator hinvariant
    second.line_le_first hdisjoint b w hw)

/-- Exclude `ReducedFive` using only the genuine standing setup and earlier
source statements. The kernel identity constructs the actual faithful action
on U_H/V₁. The action-independent 13.8.5 and 13.8.8(2) inputs are applied to
that constructed action, whose conjugation formula fixes both quotient maps.
The three-primary reduction and universal solvable-overgroup exclusion remain
with the parent 13.8.13 assembly. -/
theorem reducedFive_false
    {L V V₃ L₁ G₁ M Vα : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (src : SourceD213PrimeInput.{u})
    (reduced : ReducedFive H L₁ T M Vα)
    (c : CriticalPair L T H V)
    (hqt : _root_.IsQuasithin G)
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hs : Group.IsSolvable H)
    (s : SourceInputs c V₃ V₁ L₁ G₁ M)
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hQ : ∀ a : StarAction H (Source.UH H V₃) V₁, Function.Injective a.action →
      Source.starImage H (c.Ugamma V₃) ∈ ChapterD.Q (linearAction a))
    (h135 : ∀ a : StarAction H (Source.UH H V₃) V₁, Function.Injective a.action →
      (∃ h : H, (centerAction a).action h ≠ 1 ∧
        binaryLinear ((centerAction a).action h) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
        FullModelConclusions L L₁ T (le_sup_left.trans hminimal.prop.1.2) (centerAction a))
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    False := by
  obtain ⟨a, ha⟩ := exists_faithful_source_starAction H V₃ V₁
    (hminimal.prop.2.1.trans s.line_normalized) hk
  exact reducedFive_false_of_action src reduced c a hqt hminimal hs s hk
    (hQ a ha) (h135 a ha) hplacement

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
