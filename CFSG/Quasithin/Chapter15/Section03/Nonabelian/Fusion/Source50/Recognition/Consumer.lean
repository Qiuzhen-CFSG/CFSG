module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Action

/-!
# The action record used by the original fusion consumer

The previously recognized K* supplies every inner action formula, and the
concrete normalizer calculation supplies both outer swaps. Thus an actual
outer t with the source membership data gives the literal 15.3.59 action
record, without assuming an actor or module identification separately.
Source: Aschbacher–Smith 15.3.58(1,3), printed p.1149.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}
  {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}

namespace NaturalPair
variable (p : NaturalPair d a)

theorem coordinates_inner (h : centralizerH Z) (g : Matrix.PSL3Two.SL)
    (hg : p.actorEquivSL (QuotientGroup.mk' _ h) = MulAut.conj g)
    (w : VectorQuotient Z ZS) :
    (p.coordinates (quotientAction Z ZS h w)).toAdd =
      (BinaryLinearThree.W g (p.coordinates w).toAdd.1,
       BinaryLinearThree.W.dual g (p.coordinates w).toAdd.2) := by
  obtain ⟨k, rfl⟩ :=
    (p.first_model.actor.trans Matrix.PSL3Two.equiv.symm).surjective g
  have hk : QuotientGroup.mk' (pCore 2 (centralizerH Z)) h = k :=
    p.actorEquivSL.injective (hg.trans (p.actorEquivSL_on_K k).symm)
  exact p.coordinates_equivariant h k hk w

/-- Exact adapter to the action field of `Partner.EarlierGeometry` and hence
`Fusion.Assembly.EarlierData`, for the source's chosen outer element. -/
noncomputable def recognizedAction {T : Subgroup G} (t : G)
    (ht : t ∈ T) (hH : t ∈ centralizerH Z)
    (hout : t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)))
    (houter : QuotientGroup.mk' (pCore 2 (centralizerH Z)) ⟨t, hH⟩ ∉ p.K) :
    Fusion.Core.ResidualGeneration.RecognizedAction T Z ZS V t where
  actorEquiv := p.actorEquivSL
  coordinates := p.coordinates
  equivariant := p.coordinates_inner
  t_mem := ht
  t_mem_H := hH
  t_outside := hout
  swaps_natural x := by
    exact (p.outer_swaps (QuotientGroup.mk' _ ⟨t, hH⟩) houter).1 x
  swaps_dual x := by
    exact (p.outer_swaps (QuotientGroup.mk' _ ⟨t, hH⟩) houter).2 x

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
