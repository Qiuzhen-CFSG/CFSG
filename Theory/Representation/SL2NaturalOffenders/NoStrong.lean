module

public import Theory.Representation.SL2NaturalOffenders.Internal
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# No strong offenders on natural SL₂ sections

An offender inside a specified natural SL₂ layer has the order of its
Sylow two-subgroups. A nonidentity matrix fixes at most one field line, so
the offender inequality cannot be strict. An equivariant quotient of an
invariant subspace can only decrease fixed codimension, giving the same
obstruction on an ambient module with a faithful natural section.

Source: Aschbacher–Smith B.4.2(1), printed p.86, and B.1.5(8), printed
pp.69–70, as used in the line-normalizer argument 15.3.67, printed p.1154.
-/

@[expose] public section

namespace Representation.SL2NaturalOffenders.NoStrong
open Representation Representation.BinaryOffender
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

abbrev Actor (F : Type*) [CommRing F] := Matrix.SpecialLinearGroup (Fin 2) F
abbrev natural : Representation (ZMod 2) (Actor F) (Fin 2 → F) :=
  (specialLinearNatural 2).restrictScalars

/-- The bound for offenders contained in the actual natural SL₂ layer. -/
theorem not_strong_of_le {H : Type*} [Group H] [Finite H]
    (L : Subgroup H) (e : L ≃* Actor F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {A : Subgroup H} (hAL : A ≤ L) : ¬ IsStrongOffender ρ A := by
  intro hA
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨P, hP⟩ := Representation.SL2NaturalOffenders.exists_sylow_of_le
    L e ρ hnat ⟨hA.1, hA.2.le⟩ hAL
  have hcardA : Nat.card A = Nat.card F := by
    rw [← hP, ← Nat.card_congr
      ((P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).toEquiv]
    exact Representation.SL2NaturalOffenders.sylow_card L e P
  have hfix := Representation.SL2NaturalOffenders.fixedSpace_card_le_of_le
    L e ρ hnat hA.1.1 hAL
  have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2)
    ((fixedCodim_lt_rank_iff ρ A).mp hA.2)
  have hcV : Nat.card (Fin 2 → F) = 2 ^ Module.finrank (ZMod 2) (Fin 2 → F) := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → F))
  have hcW : Nat.card (fixedSpace ρ A) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ A))
  rw [weight, pow_add, ← hA.1.card_eq_two_pow_rank, ← hcW, ← hcV] at hlt
  have hle := Nat.mul_le_mul_left (Nat.card A) hfix
  rw [hcardA] at hlt hle
  have hlt' : Nat.card F * Nat.card F <
      Nat.card F * Nat.card (fixedSpace ρ A) := by
    simpa [Nat.card_fun, pow_two] using hlt
  exact (not_lt_of_ge hle) hlt'


/-- The natural binary SL₂ action has no strong offenders, including over F₂. -/
theorem natural_not_strong : ¬ IsStrongFFModule (natural (F := F)) := by
  rintro ⟨A,hA⟩
  exact not_strong_of_le ⊤ Subgroup.topEquiv natural (fun _ _ => rfl) le_top hA

/-- Keep the original actor injection and the actual surjective quotient map. -/
theorem not_strong_of_natural_quotient
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : D →* Actor F) (hf : Function.Injective f)
    (q : V →ₗ[ZMod 2] (Fin 2 → F)) (hq : Function.Surjective q)
    (he : ∀ g v, q (ρ g v) = natural (f g) (q v)) :
    ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA⟩
  have hcod := fixedCodim_le_of_equivariant_surjection ρ (natural.comp f) q hq he A
  have hAM := (IsOffender.map_equivariant (natural.comp f) natural f hf
    (LinearEquiv.refl (ZMod 2) (Fin 2 → F)) (fun _ _ => rfl)
    ⟨hA.1, (hcod.trans_lt hA.2).le⟩).1
  apply natural_not_strong (F := F) ⟨A.map f, hAM, ?_⟩
  rw [rank_map_injective f hf]
  change Module.finrank (ZMod 2) ((Fin 2 → F) ⧸ fixedSpace natural (A.map f)) < _
  rw [← fixedSpace_comp_map natural f A]
  exact hcod.trans_lt hA.2

/-- A natural section suffices; neither extension splitting nor centrality is required. -/
theorem not_strong_of_natural_section
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : D →* Actor F) (hf : Function.Injective f)
    (U : Subrepresentation ρ) (q : U.toSubmodule →ₗ[ZMod 2] (Fin 2 → F))
    (hq : Function.Surjective q)
    (he : ∀ g u, q (U.toRepresentation g u) = natural (f g) (q u)) :
    ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA⟩
  exact not_strong_of_natural_quotient U.toRepresentation f hf q hq he
    ⟨A, hA.1, (fixedCodim_subrepresentation_le ρ U A).trans_lt hA.2⟩

end Representation.SL2NaturalOffenders.NoStrong
