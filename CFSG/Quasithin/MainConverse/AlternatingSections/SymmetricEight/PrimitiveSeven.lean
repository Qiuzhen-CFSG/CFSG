module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.LinearModels
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.AlternatingOvergroups
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.OrderAlternative
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.Order168Recognition
public import Theory.GroupAction.PrimitiveQuotient

/-!
# Simple quotients of primitive groups of degree seven

The noninjective quotient case reduces to degree six. The nontrivial
kernel is transitive by primitivity, so the point stabilizer still maps
onto the quotient. Its faithful action on the other six points places
the quotient among the already classified simple sections of S₆.

The remaining case is a faithful simple subgroup of S₇. Solvability and
containment of A₇ are discharged by the existing cyclic and alternating
branches. The order alternative proves that every remaining subgroup has
order 168. Recognition constructs its multiplicative equivalence with
PSL₃(2) from checked permutation and matrix identities, and the linear-model
section theorem covers its simple quotient. The final theorem discharges
both premises of the retained conditional assembly, giving exhaustive
coverage of simple quotients of primitive subgroups of S₇.

Source: the condition K calculation for the alternating examples in
Aschbacher–Smith, Theorem 0.1.2(3), printed p.4, and Main Hypothesis (K),
printed p.482. This concerns quotients of the primitive group itself;
the S₈ assembly applies its permutation cases to each section numerator.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple MulAction
open scoped MatrixGroups

/-- Nonfaithful simple quotients in primitive degree seven are sections of S₆. -/
public theorem primitiveSeven_simple_quotient_constructed_of_not_injective
    (U : Subgroup (Equiv.Perm (Fin 7))) (hp : IsPreprimitive U (Fin 7))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) (hni : ¬ Function.Injective f) :
    IsConstructedCarrier S := by
  classical
  let : IsPreprimitive U (Fin 7) := hp
  let H := stabilizer U (0 : Fin 7)
  let X := SubMulAction.ofStabilizer U (0 : Fin 7)
  let : FaithfulSMul H X := Atlas.GroupTheory.stabilizer_complement_faithful (0 : Fin 7)
  let : Fintype X := Fintype.ofFinite X
  have hcard : Fintype.card X ≤ Fintype.card (Fin 6) := by
    dsimp [X]
    simpa only [← Nat.card_eq_fintype_card, SubMulAction.nat_card_ofStabilizer_eq,
      Nat.card_fin] using (show 7 - 1 ≤ 6 by decide)
  obtain ⟨j⟩ : Nonempty (X ↪ Fin 6) := Function.Embedding.nonempty_of_card_le hcard
  let i : H →* Equiv.Perm (Fin 6) :=
    (Equiv.Perm.viaEmbeddingHom j).comp (MulAction.toPermHom H X)
  have hi : Function.Injective i :=
    (Equiv.Perm.viaEmbeddingHom_injective j).comp MulAction.toPerm_injective
  have hH := SymmetricEight.isKGroup_constructed_of_injective
    (symmetricSmall_isKGroup_constructed 6 (by decide)) i hi
  have hsur : Function.Surjective (f.domRestrict H) :=
    f.surjective_domRestrict_stabilizer_of_not_injective hf hni (0 : Fin 7)
  exact SymmetricEight.constructed_section_of_isKGroup hH (⊤ : Subgroup H)
    ((f.domRestrict H).comp (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom)
    (hsur.comp (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).surjective)

/-- Conditional final assembly: only the faithful nonsolvable simple case
outside the alternating-containing branch requires permutation recognition. -/
public theorem primitiveSeven_simple_quotient_constructed_of_order_and_recognition
    (horder : ∀ U : Subgroup (Equiv.Perm (Fin 7)),
      IsPreprimitive U (Fin 7) → IsSimpleGroup U → ¬ Group.IsSolvable U →
      ¬ alternatingGroup (Fin 7) ≤ U → Nat.card U = 168)
    (hrecognition : ∀ U : Subgroup (Equiv.Perm (Fin 7)),
      IsPreprimitive U (Fin 7) → IsSimpleGroup U → Nat.card U = 168 →
      Nonempty (U ≃* PSL(3, ZMod 2)))
    (U : Subgroup (Equiv.Perm (Fin 7))) (hp : IsPreprimitive U (Fin 7))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  by_cases hi : Function.Injective f
  · let : IsSimpleGroup U := (MulEquiv.ofBijective f ⟨hi, hf⟩).isSimpleGroup
    by_cases hsolv : Group.IsSolvable U
    · let := hsolv
      let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
      exact .cyclic (primeCyclic_of_solvable_simple S)
    by_cases ha : alternatingGroup (Fin 7) ≤ U
    · exact alternatingOvergroup_simple_quotient_constructed 7 (by decide) U ha f hf
    obtain ⟨e⟩ := hrecognition U hp inferInstance (horder U hp inferInstance hsolv ha)
    exact psl3Two_simple_section_constructed e (⊤ : Subgroup U)
      (f.comp (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).toMonoidHom)
      (hf.comp (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).surjective)
  · exact primitiveSeven_simple_quotient_constructed_of_not_injective U hp f hf hi

/-- Every simple quotient of a primitive subgroup of S₇ belongs to the
constructed carrier catalogue, with the target in any universe. -/
public theorem primitiveSeven_simple_quotient_constructed
    (U : Subgroup (Equiv.Perm (Fin 7))) (hp : IsPreprimitive U (Fin 7))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S :=
  primitiveSeven_simple_quotient_constructed_of_order_and_recognition
    primitiveSeven_simple_card_eq_168 primitiveSeven_order168_equiv_psl3Two U hp f hf

end CFSG.Quasithin.MainConverse
