module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Complete

/-!
# The marked small-plane action rows

The small-moved sieve bounds the defining fields and excludes the G₂ and
triple-cover rows without discarding the action equivalences in B.4.2.
The A₇ and exterior SL₅ rows retain exactly their source group markings
and dimensions. The second theorem applies this sieve to the literal
central quotient of a B.5 moved section.

Source: Aschbacher–Smith, B.4.2, B.5.1 and13.7.15–13.7.18,
printed pp.85–86,99–103,943–945.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
open SourceInduction.ProjectiveLine
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The surviving source rows with their literal action markings. The two
dimension rows retain the weaker data supplied by B.4.2 itself. -/
inductive PlaneActionCase (L : Subgroup G) : Prop
  | linearTwo (F : BinaryField) (degree : F.degree ≤ 2)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2))
  | linearThree (F : BinaryField) (degree : F.degree ≤ 2)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
  | symplectic (F : BinaryField) (degree : F.degree = 2)
      (e : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F))
  | symplecticTwo
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7)
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
  | alternatingSix (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6))
  | alternatingSeven (e : L ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) V = 4)
  | binaryLinear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n))
  | orthogonalSix (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 8))
  | symmetricEight
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (BinaryPermutation.naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8)))
  | exteriorFive (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) V = 10)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- The faithful irreducible small-plane sieve retains every surviving
action equivalence on the original representation. -/
theorem irreducible_marked_of_plane {A L : Subgroup G}
    (hf : Function.Injective ρ) (hA : IsBestOffender ρ A)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase
      ρ L (offenderSubgroup ρ)) : PlaneActionCase ρ L := by
  have hAH := hA.le_offenderSubgroup ρ
  cases hc with
  | linearTwo F gen e _ _ =>
    exact .linearTwo F (model_field_degree_le_two F ρ hf hA.1.1
      (gen ▸ hAH) hd (specialLinearNatural 2) e) e
  | linearThree F gen e _ =>
    exact .linearThree F (model_field_degree_le_two F ρ hf hA.1.1
      (gen ▸ hAH) hd (specialLinearNatural 3) e) e
  | symplectic F large gen e _ =>
    have hh := model_field_degree_le_two F ρ hf hA.1.1
      (gen ▸ hAH) hd (symplecticNatural 2) e
    exact .symplectic F (by omega) e
  | symplecticTwo e _ => exact .symplecticTwo e
  | g2 F _ gen e _ _ =>
    exact (not_g2_model_of_plane ρ (hA.isOffender ρ) (gen ▸ hAH) hd F e).elim
  | g2Two e _ _ =>
    exact (not_g2_model_of_plane ρ (hA.isOffender ρ) hAH hd BinaryField.two e.action).elim
  | symmetric n hn e _ _ => exact .symmetric n hn e
  | alternatingSix _ e _ _ => exact .alternatingSix e
  | alternatingSeven _ _ e hd _ _ => exact .alternatingSeven e hd
  | tripleSix gen action _ =>
    exact (TripleSix.not_plane hf (hA.isOffender ρ) (gen ▸ hAH) hd action).elim
  | binaryLinear n hn _ e _ => exact .binaryLinear n hn e
  | orthogonalSix _ _ e _ _ => exact .orthogonalSix e
  | symmetricEight _ e _ => exact .symmetricEight e
  | exteriorFive _ _ e hd _ _ => exact .exteriorFive e hd

/-- The full source alternative, retaining the actual central quotient
action in the irreducible branch and the moved-space action otherwise. -/
@[expose] def SectionPlaneCase {L : Subgroup G} (s : MovedSection ρ L) : Prop :=
  (IsIrrPlus ρ L s.space.toSubmodule ∧
    Function.Injective s.action ∧ IsIrreducible (s.action.comp L.subtype) ∧
    PlaneActionCase s.action L) ∨
  ∃ n, (n = 4 ∨ n = 5) ∧
    IsLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two n

/-- Inspect the literal B.5 section before forgetting any model marking. -/
theorem source_marked_of_plane {A L : Subgroup G}
    (hA : IsOffender ρ A) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    SectionPlaneCase ρ s := by
  rcases source_irreducible_or_binary_of_plane ρ hA hd s hc with hi | hb
  · let Q := s.action
    have hoff := hA.on_subquotient ρ s.space s.central
    obtain ⟨C,hCA,hC⟩ := hoff.exists_bestOffender Q
    have hdim := (moved_finrank_quotient_le s.space.toRepresentation s.central A).trans
      ((moved_finrank_subrepresentation_le ρ s.space A).trans hd)
    have hle : moved Q C ≤ moved Q A := by
      apply Submodule.span_mono
      rintro v ⟨c,hc,w,hw,hv⟩
      exact ⟨c,hCA hc,w,hw,hv⟩
    exact Or.inl ⟨hi.1,hi.2.1,hi.2.2.1,irreducible_marked_of_plane Q hi.2.1 hC
      ((Submodule.finrank_mono hle).trans hdim) hi.2.2.2⟩
  · exact Or.inr hb
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
