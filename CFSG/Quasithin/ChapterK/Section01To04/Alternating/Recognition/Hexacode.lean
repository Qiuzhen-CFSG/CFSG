module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeEven
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeExtension
public import Theory.Representation.Quotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The hexacode branch after the binary degree calculation

Transport the literal component action to the concrete even cover, recover
its intertwining coordinates in degree six, and use normality of F*(G) to
construct the permitted marked ambient extension. Only the degree statement
from GM02 remains explicit; neither a module catalogue nor an extension of
the representation is assumed.

Source: Aschbacher–Smith, K.1.3, printed p.453 (PDF p.464).
-/

public section

namespace CFSG.Quasithin.ChapterK.Alternating
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass} {L : Subgroup G}

/-- The literal K.1 input acquires both even coordinates and its permitted
marked ambient extension once its binary dimension is six. -/
theorem hexacodeAction_of_dimension (h : Input ρ K L)
    (q : L ≃* HexEvenAutomorphisms) (hd : Module.finrank (ZMod 2) V = 6) :
    Nonempty (HexacodeAction ρ L) := by
  let τ := (ρ.comp L.subtype).comp q.symm.toMonoidHom
  have hf : Function.Injective τ :=
    (h.faithful.comp L.subtype_injective).comp q.symm.injective
  have hi : IsIrreducible τ :=
    (irreducible_comp_surjective_iff q.symm.toMonoidHom q.symm.surjective _).mpr h.irreducible
  obtain ⟨e⟩ := EvenRecognition.exists_actionEquiv τ hf hi hd
  let a : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction := {
    groupEquiv := q.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := by
      intro l v
      have he := e.intertwines (q l) v
      simpa only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        q.symm_apply_apply, MulEquiv.trans_apply] using he }
  let : L.Normal := by rw [h.fitting]; infer_instance
  exact ⟨⟨a, hexacode_extension ρ L h.faithful a⟩⟩
end CFSG.Quasithin.ChapterK.Alternating
