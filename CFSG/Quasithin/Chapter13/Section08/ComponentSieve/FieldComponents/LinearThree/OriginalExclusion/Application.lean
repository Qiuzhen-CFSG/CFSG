module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.CriticalReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OrdinarySource.Complete
/-!
# Applying the binary critical reduction to the field sieve

The original critical reduction forces a transvection if H/O₂(H) is L₃(2).
The preceding 13.8.5(2) alternatives then contradict the order 168 of that
quotient. Applying this exclusion to the already constructed ordinary and
covered containment consumers yields H/O₂(H) ≃ Aut(L₃(2)) whenever the
component quotient is L₃(2), using the literal source quotient throughout.

The 13.8.5 transvection alternatives remain explicit. Their discharge and
all other field-sieve branches belong to qt-d-138-fields-source; the original
section assembly qt-d-1381-source supplies SourceContext. These conditional
applications do not claim the unconditional source theorems 13.8.19–21.
Source: Aschbacher–Smith, 13.8.5(2), 13.8.19 and 13.8.21(3), pp.947,953,956–957.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open LinearThree LinearThree.OriginalExclusion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Whole-quotient binary exclusion after the preceding 13.8.5(2) group
alternatives. All H.6.5, critical selection and module-obstruction inputs
are discharged from the original SourceContext. The field-sieve owner
retains the source proof of the transvection alternatives. -/
theorem source_binary_exclusion_of_transvection_models
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁)
    (htrans : (∃ g : Source.Hstar H, fixedCodim act.representation (zpowers g) = 1) →
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 7)) ∨
      Nonempty (Source.Hstar H ≃* PSL(4, ZMod 2))) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  have hc : Nat.card (Source.Hstar H) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  rcases htrans (source_binary_has_transvection c act e) with hf | hf | hf
  · obtain ⟨f⟩ := hf
    have hh := Nat.card_congr f.toEquiv
    norm_num [hc,Nat.card_eq_fintype_card,Fintype.card_perm] at hh
  · obtain ⟨f⟩ := hf
    have hh := Nat.card_congr f.toEquiv
    norm_num [hc,Nat.card_eq_fintype_card,Fintype.card_perm] at hh
  · obtain ⟨f⟩ := hf
    have hh := Nat.card_congr (f.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toEquiv
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num at hh

/-- The actual binary automorphism consumer now requires only the preceding
transvection alternatives, rather than the whole-quotient exclusion. This
applies in both ordinary and covered local cases; K* remains allowed to be
L₃(2). The original section owner supplies SourceContext, while this field
owner retains discharge of the transvection premise and all remaining rows. -/
theorem source_binary_automorphism_of_transvection_models
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)
    (htrans : (∃ g : Source.Hstar H, fixedCodim act.representation (zpowers g) = 1) →
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 7)) ∨
      Nonempty (Source.Hstar H ≃* PSL(4, ZMod 2))) :
    Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL) :=
  source_binary_automorphism c eK
    (source_binary_exclusion_of_transvection_models c act htrans)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
