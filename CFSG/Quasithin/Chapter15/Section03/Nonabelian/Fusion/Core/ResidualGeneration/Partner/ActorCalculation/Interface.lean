module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.Transport

/-!
# Simultaneous actor and parabolic coordinates for 15.3.59

The remaining geometry must align the actual image of X and the actual relative
normalizer of V₀ with a point radical and its parabolic. The coordinate change
is an automorphism of the concrete SL₃(2), so it transports its inner actors
compatibly. This interface assumes neither a residual image nor a commutator
identity. Its existence remains a separate geometric proof obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5), 15.3.58(1,3), and 15.3.59, printed pp.1147–1150.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G]
variable {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The faithful action of the actual actor quotient on the actual vector quotient. -/
noncomputable def faithfulActorAction
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    ActorQuotient Z →* MulAut (VectorQuotient Z ZS) :=
  (quotientAction Z ZS).range.subtype.comp
    (actorQuotientEquivRange Z ZS hkernel).toMonoidHom

/-- The descended action retains the literal conjugation map. -/
theorem faithfulActorAction_projection
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h : centralizerH Z) :
    faithfulActorAction hkernel (actorProjection Z h) = quotientAction Z ZS h := rfl

/-- Faithfulness is a consequence of the supplied kernel equality. -/
theorem faithfulActorAction_injective
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    Function.Injective (faithfulActorAction hkernel) :=
  Subtype.val_injective.comp (actorQuotientEquivRange Z ZS hkernel).injective

/-- The image of the literal relative normalizer is the full stabilizer of its
quotient image. This uses surjectivity of H → H/O₂(H), not a lifting assumption. -/
theorem mem_actorImage_markedNormalizer_iff
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V₀ : Subgroup G) (hZV : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS)
    (a : ActorQuotient Z) :
    a ∈ actorImage Z (markedNormalizer Z V₀) ↔
      ∀ w : VectorQuotient Z ZS,
        faithfulActorAction hkernel a w ∈ vectorImage Z ZS V₀ ↔
          w ∈ vectorImage Z ZS V₀ := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z)) a
  constructor
  · rintro ⟨k, hk, he⟩
    have he' : faithfulActorAction hkernel (actorProjection Z k) =
        faithfulActorAction hkernel (actorProjection Z h) := congrArg _ he
    rw [faithfulActorAction_projection, faithfulActorAction_projection] at he'
    rw [show faithfulActorAction hkernel (QuotientGroup.mk' _ h) =
      quotientAction Z ZS h from rfl, ← he']
    exact (mem_markedNormalizer_iff Z ZS V₀ hZV hVU k).mp hk
  · intro hh
    exact ⟨h, (mem_markedNormalizer_iff Z ZS V₀ hZV hVU h).mpr hh, rfl⟩

/-- A change of the concrete SL₃(2) labels acts on its actual automorphism group. -/
def actorRelabel (d : RecognizedAction T Z ZS V t) (α : MulAut Matrix.PSL3Two.SL) :
    ActorQuotient Z ≃* MulAut Matrix.PSL3Two.SL :=
  d.actorEquiv.trans (MulAut.congr α)

/-- Simultaneous placement of the marked four-group and the full line stabilizer.
This is an intermediate conclusion to prove, not an earlier-source hypothesis. -/
def ParabolicAlignment (d : RecognizedAction T Z ZS V t) (V₀ : Subgroup G) (y : G) :
    Prop :=
  ∃ α : MulAut Matrix.PSL3Two.SL,
    (actorImage Z (partnerX Z ZS y)).map (actorRelabel d α).toMonoidHom =
      Matrix.PSL3Two.MarkedAutomorphisms.pointV.map MulAut.conj ∧
    (actorImage Z (markedNormalizer Z V₀)).map (actorRelabel d α).toMonoidHom =
      Matrix.PSL3Two.pointParabolicSL.map MulAut.conj

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
