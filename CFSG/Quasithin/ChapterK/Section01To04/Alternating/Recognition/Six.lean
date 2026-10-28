module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Extension
public import Theory.Representation.Quotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Assembling the A₆ recognition branch

Transport the restricted representation to the given A₆ actor, use intrinsic
four-dimensional recognition, and transport its automorphism twist back to
the original component. Normality of F*(G) and the model normalizer then
give the complete marked ambient extension.

The degree, four-space recognition, and normalizer premises below are
unfinished source obligations. These conditional theorems do not assert
`SixRecognition` without them; `sixRecognition` is reserved for their final
discharge.

Source: Aschbacher–Smith, K.1–K.1.1, printed p.452 (PDF p.463), citing
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource RecognitionInputs
universe u v

/-- Apply intrinsic four-space recognition and the proved extension construction
to the original K.1 component and action, retaining its exact marking. -/
theorem six_naturalAction_of_dimension
    (h4 : Six.FourSpace.{v}) (hn : Six.Normalizer)
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}
    (h : Input ρ K L) (q : L ≃* alternatingGroup (Fin 6))
    (hd : Module.finrank (ZMod 2) V = 4) : Nonempty (NaturalAction ρ L 6) := by
  let τ := (ρ.comp L.subtype).comp q.symm.toMonoidHom
  have hf : Function.Injective τ :=
    (h.faithful.comp L.subtype_injective).comp q.symm.injective
  have hi : IsIrreducible τ :=
    (irreducible_comp_surjective_iff q.symm.toMonoidHom q.symm.surjective _).mpr h.irreducible
  obtain ⟨e⟩ := h4 τ hf hi hd
  let a : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6) := {
    groupEquiv := q.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := by
      intro l v
      have he := e.intertwines (q l) v
      simpa only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        q.symm_apply_apply, MulEquiv.trans_apply] using he }
  let : L.Normal := by rw [h.fitting]; infer_instance
  exact ⟨⟨a, six_extension_of_normalizer ρ L hn h.faithful a⟩⟩

/-- Final branch assembly with the three remaining mathematical obligations
explicit. The degree premise applies to the ambient cubic ratio, without
assuming it transfers to the component. -/
theorem sixRecognition_of_inputs (hd : Six.Degree.{u,v})
    (h4 : Six.FourSpace.{v}) (hn : Six.Normalizer) : SixRecognition.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h q
  exact six_naturalAction_of_dimension h4 hn ρ h q (hd ρ K L h q)

end CFSG.Quasithin.ChapterK.Alternating
