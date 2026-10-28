module
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.SimpleNormalActor

/-!
# A section consuming all displacement

Equality between section and ambient fixed codimension forces the actor to
fix the denominator and the quotient above the section. This follows from
the subrepresentation and quotient codimension inequalities, without any
semisimplicity assumption. When the actor is faithful on a simple normal
factor, that factor fixes the denominator and the upper quotient as well.

Source application: Aschbacher--Smith 13.1.9, printed p.871, the consequences
of equality in (*).
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- If a section consumes the full displacement, its denominator and the
quotient above it are fixed by the original actor. -/
theorem fixed_outside_section_of_fixedCodim_eq
    (ρ : Representation (ZMod 2) Q V) (U W : Subrepresentation ρ) (hUW : U ≤ W)
    (A : Subgroup Q) (he : fixedCodim (sectionRepresentation ρ U W) A = fixedCodim ρ A) :
    U.toSubmodule ≤ fixedSpace ρ A ∧
      ∀ a ∈ A, ∀ v, W.quotientRepresentation a v = v := by
  have hq := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation
    (sectionLower ρ U W) A
  have hw := fixedCodim_subrepresentation_le ρ W A
  change fixedCodim (sectionRepresentation ρ U W) A + _ ≤ _ at hq
  have hz : fixedCodim (sectionLower ρ U W).toRepresentation A = 0 := by omega
  have heW : fixedCodim W.toRepresentation A = fixedCodim ρ A := by omega
  refine ⟨(sectionLower_trivial_iff ρ hUW A).mp
    ((fixedCodim_eq_zero_iff _ A).mp hz),?_⟩
  exact quotient_trivial_of_sup_fixedSpace ρ W A
    ((fixedCodim_subrepresentation_eq_iff ρ W A).mp heW)
omit [FiniteDimensional (ZMod 2) V] in
/-- Triviality of a faithful nontrivial actor forces triviality of the simple
normal factor in the same representation. -/
theorem simple_normal_le_ker_of_actor_le_ker
    (ρ : Representation (ZMod 2) Q V) (K A : Subgroup Q)
    [K.Normal] [IsSimpleGroup K] (hf : A ⊓ centralizer (K : Set Q) = ⊥)
    (hA : A ≠ ⊥) (ht : A ≤ ρ.ker) : K ≤ ρ.ker := by
  by_contra hn
  have hi : Function.Injective (ρ.comp K.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (ρ.comp K.subtype).normal_ker.eq_bot_or_eq_top with he | he
    · exact he
    · exact (hn (fun k hk =>
        (show (⟨k,hk⟩ : K) ∈ (ρ.comp K.subtype).ker from he.symm ▸ mem_top _))).elim
  have hc := ρ.ker_le_centralizer_of_injective_normal_restriction K hi
  exact hA (le_bot_iff.mp ((le_inf le_rfl (ht.trans hc)).trans_eq hf))

/-- A faithful actor on a simple normal factor exhausts the displacement of
that factor whenever its section exhausts the actor displacement. -/
theorem factor_fixed_outside_section_of_fixedCodim_eq
    (ρ : Representation (ZMod 2) Q V) (U W : Subrepresentation ρ) (hUW : U ≤ W)
    (K A : Subgroup Q) [K.Normal] [IsSimpleGroup K]
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (hA : A ≠ ⊥)
    (he : fixedCodim (sectionRepresentation ρ U W) A = fixedCodim ρ A) :
    U.toSubmodule ≤ fixedSpace ρ K ∧
      ∀ k ∈ K, ∀ v, W.quotientRepresentation k v = v := by
  obtain ⟨hU,hW⟩ := fixed_outside_section_of_fixedCodim_eq ρ U W hUW A he
  have hAU : A ≤ U.toRepresentation.ker := by
    intro a ha
    exact LinearMap.ext (fun v => Subtype.ext (hU v.property ⟨a,ha⟩))
  have hKU := simple_normal_le_ker_of_actor_le_ker U.toRepresentation K A hf hA hAU
  have hAW : A ≤ W.quotientRepresentation.ker := fun a ha => LinearMap.ext (hW a ha)
  have hKW := simple_normal_le_ker_of_actor_le_ker W.quotientRepresentation K A hf hA hAW
  refine ⟨?_,fun k hk v => LinearMap.congr_fun (hKW hk) v⟩
  intro v hv k
  exact congrArg Subtype.val (LinearMap.congr_fun (hKU k.property) ⟨v,hv⟩)
end Representation.BinaryOffender
