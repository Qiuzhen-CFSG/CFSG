module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2Source
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import Theory.SpecificGroups.G2Even.MarkedCover

/-!
# G₂ natural recognition from the original B.4.2 hypotheses

The actual central quotient determines the whole quasisimple layer because
its two-core is trivial. The completed cubic degree bound then identifies
the original binary module with the natural six-space. The conclusion is
an action equivalence, retaining the group map and linear intertwiner.

The offender ranks, generation and ratio needed for the full B.4.2 G₂ row
are separate geometric conclusions of B.4.6.

Source: Aschbacher–Smith B.4.2(4), B.4.6, and K.3.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Genuine representation recognition from the prescribed central quotient.
No degree bound, cover, natural marking or offender geometry is assumed. -/
theorem g2_natural_action (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : L ⧸ center L ≃* Atlas.G2.Model F.Carrier) :
    Nonempty (ActionEquiv (ρ.comp L.subtype) (binaryG2 F)) := by
  let := h.quasisimple
  let := h.layer_normal
  let := h.irreducible
  obtain ⟨j, _⟩ := Atlas.G2.FiniteCover.exists_marked_equiv (by omega) F.card_eq
    h.layer_twoCore_eq_bot e
  obtain ⟨e', f, hf⟩ := ChapterK.Exceptional.SourceAssembly.g2_natural ρ L
    (by omega) F.card_eq j h.faithful h.smallCubic
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hF
  let : Group.IsPerfect (Atlas.G2.Model F.Carrier) := Atlas.G2.isPerfect hq
  let d : commutator (Atlas.G2.Model F.Carrier) ≃* Atlas.G2.Model F.Carrier :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  refine ⟨{
    groupEquiv := e'.trans d
    linearEquiv := LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective
    intertwines := ?_ }⟩
  intro g v
  exact hf g v

/-- Literal application to an original B.4.2 best offender. -/
theorem g2_natural_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : L ⧸ center L ≃* Atlas.G2.Model F.Carrier) :
    Nonempty (ActionEquiv (ρ.comp L.subtype) (binaryG2 F)) :=
  g2_natural_action (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA) F hF e

/-- The binary central quotient supplies the original derived-group natural
action, without an assumed covering map or degree bound. -/
theorem g2_binary_natural_action (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty (ActionEquiv (ρ.comp L.subtype)
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) := by
  let := h.quasisimple
  let := h.layer_normal
  let := h.irreducible
  obtain ⟨j, _⟩ := Atlas.G2.FiniteCover.exists_binaryDerived_marked_equiv
    h.layer_twoCore_eq_bot e
  obtain ⟨e',f,hf⟩ := ChapterK.Exceptional.SourceAssembly.g2_binary_natural ρ L j
    h.faithful h.smallCubic
  exact ⟨{
    groupEquiv := e'
    linearEquiv := LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective
    intertwines := fun g v => hf g v }⟩

/-- Apply binary recognition to the literal B.4.2 best-offender hypotheses. -/
theorem g2_binary_natural_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty (ActionEquiv (ρ.comp L.subtype)
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) :=
  g2_binary_natural_action (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA) e

end CFSG.Quasithin.ChapterB.SourceClassification
