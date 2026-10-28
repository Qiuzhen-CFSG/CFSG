module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Covers
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Natural.Generation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition.Source
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SourceAssembly

/-!
# Rank-one source families in Chapter K

The common source domain uses the full known-simple catalogue and the literal
layer action. `SourceHypotheses.psl2_case` supplies the exhaustive natural or
Hermitian recognition together with the natural offender conclusions, exact
orthogonal ratios and the distinct A₅/S₅ endpoint actions. The re-exported
orthogonal calculations retain the original Sylow intersection, outer
transvection, centralizers, and separate threshold and minimizing families.

The Suzuki recognition and source calculation supply the actual natural
intertwiner, compatible central projection, prime-to-two residual, both ratios
and unique threshold subgroup Ω₁(T). The unitary assembly similarly supplies
the full natural SU₃ action, center, outer actions and unique actor Ω₁(T ∩ L),
conditional only on the earlier group-only cover. That cover remains an
explicit obligation of `qt-b01-ff-classical-even-cover-lifting`; no module
recognition or numerical premise remains in the unitary assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1,
K.3.3 and K.3.6, printed pp.453–454 and 456–457.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation.BinaryOffender
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- K.3.1.1 on the source domain, once an actual natural-module identification
has been established. The other module alternatives are not assumed away. -/
theorem SourceHypotheses.natural_case (h : SourceHypotheses ρ L)
    (M : NaturalModel (F := F) ρ L) (hF : 2 < Nat.card F) (T : Sylow 2 G) :
    quadraticRatio ρ = 1 ∧ cubicRatio ρ = 1 ∧
    IsQuadratic ρ ((T : Subgroup G) ⊓ L) ∧
    rank ((T : Subgroup G) ⊓ L) = Module.finrank (ZMod 2) F ∧
    fixedCodim ρ ((T : Subgroup G) ⊓ L) = Module.finrank (ZMod 2) F ∧
    subspaceCommutator ρ ⊤ ((T : Subgroup G) ⊓ L) = fixedSpace ρ ((T : Subgroup G) ⊓ L) ∧
    (∀ A : Subgroup G, A ≤ T →
      (IsOffender ρ A ↔ A = (T : Subgroup G) ⊓ L)) ∧
    generatedBy {A | IsBestOffender ρ A} (T : Subgroup G) = (T : Subgroup G) ⊓ L := by
  let : L.Normal := h.layer_normal
  have hrat := M.ratios_eq_one hF h.faithful
  have hcalc := M.sylowInf_calculation T
  exact ⟨hrat.1, hrat.2, hcalc.1, hcalc.2.1, hcalc.2.2,
    M.sylowInf_commutator_eq_fixedSpace T,
    fun _ hAT => M.offender_iff_eq_sylowInf hF h.faithful T hAT,
    M.generatedBy_bestOffenders_sylow hF h.faithful T⟩

end CFSG.Quasithin.ChapterK.RankOne
