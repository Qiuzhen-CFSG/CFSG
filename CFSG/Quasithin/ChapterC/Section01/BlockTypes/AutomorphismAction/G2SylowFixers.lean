module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.CentralSylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.Representation.G2BinaryFixedBounds
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction

/-!
# Central Sylow fixers of a G₂ block

The actual G₂(2)′ natural representation is faithful, and every Sylow
subgroup fixes at most a line. Averaging in the block's actual module
therefore bounds the entire automorphism subgroup fixing a Sylow modulo
the center by two. The central kernel of U(L) is retained throughout.
The hidden actor body is used only for its literal two-core quotient map.
Source: Aschbacher--Smith 15.1.22(**), printed p.1099; B.4.6.
The model calculations retain the licensed ATLAS attribution of their imports.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
open Atlas.G2.Natural Representation.BinaryOffender
variable {L : Type*} [Group L] [Finite L]

private theorem g2_action_injective : Function.Injective g2TwoNaturalAction := by
  intro g h hh
  apply Subtype.ext
  apply action_injective (ZMod 2)
  apply LinearMap.ext
  intro v
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hh (Multiplicative.ofAdd v))

/-- Every automorphism subgroup fixing a G₂ block Sylow modulo its center has order at most two. -/
theorem IsG2TwoBlock.central_sylow_fixers_card_le_two
    (hb : IsG2TwoBlock L) (P : Sylow 2 L) (B : Subgroup (MulAut L))
    (hB : ∀ a ∈ B, ∀ x ∈ P, a x * x⁻¹ ∈ center L) : Nat.card B ≤ 2 := by
  obtain ⟨m⟩ := hb.natural_model
  let : Finite (Multiplicative (Space (ZMod 2))) := Finite.of_equiv (BlockModule L) m.moduleIso.toEquiv
  let : Finite (Space (ZMod 2)) := inferInstanceAs (Finite (Multiplicative (Space (ZMod 2))))
  have hk : IsPGroup 2 m.actor.ker := by
    have he : m.actor.ker = pCore 2 L := by
      rw [BlockModuleModel.actor,MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,
        QuotientGroup.ker_mk']
    rw [he]
    exact pCore_isPGroup
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : Group.IsPerfect L := hb.short.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    m.actor m.actor_surjective hk
  let Q := P.mapSurjective (f := m.actor) m.actor_surjective
  let F := {w : Multiplicative (Space (ZMod 2)) // ∀ x ∈ P, g2TwoNaturalAction (m.actor x) w = w}
  let f : F → fixedSpace (Representation.g2DerivedNatural (ZMod 2)) (Q : Subgroup _) :=
    fun w => ⟨w.val.toAdd,by
      rintro ⟨g,x,hx,rfl⟩
      exact congrArg Multiplicative.toAdd (w.property x hx)⟩
  have hfi : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact congrArg (fun z => z.val) hh
  exact (hb.short.central_sylow_fixers_card_le m g2_action_injective P B hB).trans
    ((Nat.card_le_card_of_injective f hfi).trans
      (BinarySylowFixedSpace.card_derived_sylow_fixed_le_two Q))
end CFSG.Quasithin.ChapterC
