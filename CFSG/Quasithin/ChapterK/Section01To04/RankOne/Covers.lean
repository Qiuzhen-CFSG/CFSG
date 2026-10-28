module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.Suzuki
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting

/-!
# Actual PSL₂ and Suzuki covering groups in Chapter K

Faithfulness and irreducibility on the layer kill its two-core. The already
proved covering theorem then identifies the whole layer with the actual PSL₂
model of the same field order, including the exceptional parameter four.
Cyclic odd-Sylow transfer also identifies the Suzuki layer through its exact
central projection. These are group identifications only; the natural and
orthogonal module cases remain distinct and require separate representation recognition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1,
printed p.453, using I.1.3. The unitary covers retain their existing producer.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open Theory.GroupTheory
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- All permitted even PSL₂ central quotients identify the source layer itself. -/
theorem SourceHypotheses.isPSL_of_even_quotient (h : SourceHypotheses ρ L)
    {q : ℕ} (hp : KnownSimple.LinearParameters 2 q) (he : Even q)
    (hq : ClassicalGroup.IsPSL (L ⧸ Subgroup.center L) 2 q) :
    ClassicalGroup.IsPSL L 2 q := by
  let : IsQuasisimple L := h.quasisimple
  exact ChapterB.ComponentRecognition.KnownFFTypes.Classical.isPSL_of_even_psl2
    h.layer_twoCore_eq_bot hp he hq

/-- The source Suzuki layer is identified through its actual central projection.
The field exponent is `2*m+1`, with the simple range `m ≥ 1`. -/
noncomputable def SourceHypotheses.suzukiEquiv (h : SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ Subgroup.center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m := by
  let : IsQuasisimple L := h.quasisimple
  exact ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.suzukiEquiv
    h.layer_twoCore_eq_bot hm e

/-- Compatibility with the exact source central-quotient map. -/
@[simp] theorem SourceHypotheses.suzukiEquiv_apply (h : SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ Subgroup.center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (x : L) :
    h.suzukiEquiv hm e x = e (QuotientGroup.mk x) := by
  let : IsQuasisimple L := h.quasisimple
  exact ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.suzukiEquiv_apply
    h.layer_twoCore_eq_bot hm e x

end CFSG.Quasithin.ChapterK.RankOne
