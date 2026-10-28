module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalSylowBound
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Normal elementary actors on an irreducible Hall–Janko subgroup

Faithfulness and binary irreducibility make conjugation injective on the
original elementary actor. Its image is normal in the image of the supplied
Sylow subgroup. The actual conjugation range contains the inner Hall–Janko
carrier, so the intrinsic normal-Sylow bound gives actor order at most eight.

Source: Aschbacher–Smith G.11.1(4), G.11.7, with the Hall–Janko small-degree
exclusion preceding its retained G.9 rows.
-/

public section
open Subgroup
namespace Representation.JankoTwo

theorem normal_elementary_actor_card_le_eight
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (L : Subgroup D) [L.Normal] [Representation.IsIrreducible (ρ.comp L.subtype)]
    (e : L ≃* Sporadic.LeechRelated.J2.Carrier)
    (P : Sylow 2 D) (A : Subgroup D) (hAP : A ≤ P)
    (hn : (A.subgroupOf (P : Subgroup D)).Normal) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 8 := by
  let f : D →* Sporadic.LeechRelated.J2.ExceptionalParabolics.Extension :=
    Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.symm.toMonoidHom.comp
      ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L)))
  have hfi : Function.Injective (f.comp A.subtype) := by
    apply Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.symm.injective.comp
    apply (MulAut.congr e).injective.comp
    have hAL : A ≤ normalizer (L : Set D) := by
      rw [normalizer_eq_top_iff.mpr (inferInstance : L.Normal)]
      exact le_top
    exact Representation.BinaryIrreducibleCentralizer.elementary_conjugation_injective ρ L hf A hAL
  have hinner : Sporadic.LeechRelated.J2.ExceptionalParabolics.intoExtension.range ≤ f.range := by
    rintro _ ⟨x,rfl⟩
    refine ⟨e.symm x, ?_⟩
    apply Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.injective
    change Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut
      (Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut_intoExtension]
    change MulAut.congr e (MulAut.conjNormal (e.symm x : D)) = MulAut.conj x
    rw [MulAut.conjNormal_val,MulAut.congr_conj,e.apply_symm_apply]
  have hb := Sporadic.LeechRelated.J2.overgroup_sylow_normal_elementary_card_le_eight
    f.range hinner
  apply Theory.GroupTheory.NormalSylowElementary.bound_surjective
    f.rangeRestrict f.rangeRestrict_surjective 8 hb P A hAP hn
  intro x y he
  exact hfi (congrArg Subtype.val he)

end Representation.JankoTwo
