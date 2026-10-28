module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span.OriginalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The original rank-four L₁ orbit span in 14.7.70

For the genuine source data and one prepared rank-three critical path,
prove ⟨Zα^(L₁)⟩ = V Zα. OriginalAction proves the upper containment and
that the literal orbit image contains V/V₁. To recover the original kernel,
use the checked natural point-residual identity V = [V,L₁]. The orbit span
is L₁-invariant, while L₁ centralizes V₁, so its containment of V modulo V₁
implies containment of all V. This retains the original subgroup lift.

The order-sixteen and rank-four results from Elementary now apply to the
actual span. Since E has order four, L₁ cannot normalize E. The final
source_span_geometry application constructs descent from the literal
earlier O₂(H)-centralization and includes both original T-fixed identities.

This completes the conditional span helper. T-normalization of E remains
an explicit intermediate result from qt-14-07-rank-three-moved-plane.
Preliminary is produced by qt-14-07-rechoice-preparation; 14.5.15(4)
by qt-14-05; ModuleSeparation by qt-14-07-solvable; compatible UpperMarking
and LocalActors by qt-14-03/qt-14-07. Parent
qt-14-07-rechoice-rank-three-action retains all premise discharge and
source-theorem assembly. Neither pairing identity, a Goldschmidt triple,
nor a later rank contradiction is used.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.64–65, printed pp.1069–1070, and proof of 14.7.70,
printed p.1074 (PDF p.1091), before the Goldschmidt construction.
-/

public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
open Subgroup Representation Chapter12.Section08 Preparation Preparation.MarkedSpans
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W) (s : d.ActionDescent)
  (c : CriticalPath (L := L) F) (h : Preliminary d c)
include s h

/-- Recover V, including the original V₁ kernel, inside the literal L₁ orbit span. -/
theorem seed_le_orbit (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    V ≤ conjugateSpanBy c.Zα (F.Li L 1) := by
  let S := conjugateSpanBy c.Zα (F.Li L 1)
  have hSU : S ≤ F.U := (orbit_le d s c h mark sep actors hT).trans
    (sup_le (Data.V_le_U F) (h.opposite_le.trans (h.commutator_le.trans inf_le_left)))
  have hPSU : S ⊔ F.Vi 1 ≤ F.U := sup_le hSU d.conjugationSection.kernel_le
  have hpoint : tilde d (F.Vi 1) = ⊥ := by
    apply bot_unique
    intro w hw
    obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    exact (d.conjugationSection.coordinates_eq_one_iff a).mpr ha
  have hVS : V ≤ S ⊔ F.Vi 1 := by
    apply (tilde_le_iff d (Data.V_le_U F) hPSU le_sup_right).mp
    rw [tilde_sup d hSU d.conjugationSection.kernel_le, hpoint, sup_bot_eq]
    exact seed_image_le_orbit d s c h mark sep actors hT
  have hSn : F.Li L 1 ≤ normalizer (S : Set G) := le_normalizer_conjugateSpanBy _ _
  have hUS : F.U ≤ normalizer (S : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    let : IsMulCommutative F.U := d.abelian
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨v, hSU hv⟩ : F.U) ⟨u, hu⟩)
  have hPc : F.Vi 1 ≤ centralizer (F.Li L 1 : Set G) := by
    apply le_centralizer_iff.mp
    rw [point_centralizer d]
    exact (F.Li_le L 1).trans inf_le_right
  have hPre : S ⊔ F.Vi 1 ≤ commutatorPreimage F.U (F.Li L 1) S := by
    apply sup_le
    · exact le_commutatorPreimage hSU (le_normalizer_iff_commutator_le_left.mp hSn)
    · apply le_commutatorPreimage d.conjugationSection.kernel_le
      rw [commutator_eq_bot_iff_le_centralizer.mpr hPc]
      exact bot_le
  calc
    V = ⁅V, F.Li L 1⁆ := d.seed_eq_commutator_point_residual
    _ ≤ ⁅commutatorPreimage F.U (F.Li L 1) S, F.Li L 1⁆ :=
      commutator_mono (hVS.trans hPre) le_rfl
    _ ≤ S := commutator_commutatorPreimage_le F.U (F.Li L 1) S hUS

/-- The actual orbit-span equality in 14.7.70, before the Goldschmidt construction. -/
theorem orbit_eq (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    conjugateSpanBy c.Zα (F.Li L 1) = V ⊔ c.Zα :=
  le_antisymm (orbit_le d s c h mark sep actors hT)
    (sup_le (seed_le_orbit d s c h mark sep actors hT) (le_conjugateSpanBy _ _))

/-- The span has rank four, and the actual L₁ fails to normalize E. -/
theorem rank_four_geometry (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    conjugateSpanBy c.Zα (F.Li L 1) = V ⊔ c.Zα ∧
      primeRank 2 (conjugateSpanBy c.Zα (F.Li L 1)) = 4 ∧
      ¬ F.Li L 1 ≤ normalizer (E c : Set G) := by
  have hs := orbit_eq d s c h mark sep actors hT
  exact ⟨hs, hs.symm ▸ h.seed_sup_opposite_rank, h.L₁_not_normalizes_of_span hs⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
open Subgroup Representation Chapter12.Section08 Preparation Preparation.MarkedSpans
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Source application: descent is constructed from earlier 14.5.15(4).
The moved-plane producer still supplies T-normalization to the parent assembly. -/
theorem source_span_geometry (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (h : Preliminary d c)
    (hcore : ∀ x : F.H, x ∈ pCore 2 F.H → d.action x = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    tilde d c.Zα ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d) = fixedT d ∧
      fixedT d = tilde d (F.Vi 2) ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d) ∧
      conjugateSpanBy c.Zα (F.Li L 1) = V ⊔ c.Zα ∧
      primeRank 2 (conjugateSpanBy c.Zα (F.Li L 1)) = 4 ∧
      ¬ F.Li L 1 ≤ normalizer (E c : Set G) := by
  let s := d.actionDescentOfCore hcore
  have hf := fixed_decompositions d s c h mark sep actors hT
  exact ⟨hf.1, hf.2, rank_four_geometry d s c h mark sep actors hT⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
