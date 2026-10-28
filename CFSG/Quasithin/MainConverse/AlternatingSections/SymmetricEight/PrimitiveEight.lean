module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveEight.Affine
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveEight.Structure

/-!
# Assembly of the primitive degree-eight quotient calculation

The solvable and affine cases are proved. Groups containing A₈ are covered by
the existing alternating-overgroup theorem. The assembly below explicitly takes
the two remaining structural steps: a factor five forces A₈, and a nonsolvable
primitive group with no factor five and no nontrivial abelian normal subgroup
has an actual PSL₂(7) normal layer with solvable quotient.

Neither structural step is asserted here. Consequently this module does not
yet export the unconditional `primitiveEight_simple_quotient_constructed`.
The owner of that result must discharge both premises. This is the primitive
part of the section calculation for condition K in Aschbacher–Smith,
Theorem 0.1.2(3), printed pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple MulAction

/-- Conditional assembly; the two structural assertions remain to be proved. -/
public theorem primitiveEight_simple_quotient_constructed_of_structural_cases
    (U : Subgroup (Equiv.Perm (Fin 8))) [IsPreprimitive U (Fin 8)]
    (hfive : 5 ∣ Nat.card U → alternatingGroup (Fin 8) ≤ U)
    (hseven : ¬ Group.IsSolvable U → ¬ 5 ∣ Nat.card U →
      ¬ PrimitiveEight.HasAbelianNormal U → PrimitiveEight.HasPSL2SevenLayer U)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  classical
  by_cases hsolv : Group.IsSolvable U
  · let := hsolv
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
    exact .cyclic (primeCyclic_of_solvable_simple S)
  by_cases hab : PrimitiveEight.HasAbelianNormal U
  · obtain ⟨N, hN, ha, hn⟩ := hab
    let := hN
    let := ha
    exact SymmetricEight.constructed_section_of_isKGroup
      (primitiveEight_isKGroup_of_abelian_normal U N hn) ⊤
      (f.comp (Subgroup.topEquiv (G := U)).toMonoidHom)
      (hf.comp Subgroup.topEquiv.surjective)
  by_cases h5 : 5 ∣ Nat.card U
  · exact alternatingOvergroup_simple_quotient_constructed 8 (by decide) U (hfive h5) f hf
  exact PrimitiveEight.simple_quotient_constructed_of_psl2Seven_layer
    (hseven hsolv h5 hab) f hf

end CFSG.Quasithin.MainConverse
