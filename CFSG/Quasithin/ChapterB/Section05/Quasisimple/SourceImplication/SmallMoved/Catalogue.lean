module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.FieldDegree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Rows
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport

/-!
# The small-moved actor catalogue for 13.7.15

The faithful irreducible source list, together with a genuine offender moving
at most a plane, leaves binary linear groups, alternating groups, SL3(4),
Sp4(4), and the explicit triple-cover A6 row. Field transport identifies the
actual field-four groups; the small derived Sp4(2) endpoint is A6. Both G2
rows are excluded by their concrete short-root displacement. The remaining
triple-cover branch retains its faithful original quotient and offender data.

Source: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved

/-- The four group families in 13.7.15(1), on concrete standard carriers. -/
def ActorList (D : Type*) [Group D] : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ Nonempty (D ≃* PSL(n,ZMod 2))) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (D ≃* alternatingGroup (Fin n))) ∨
  Nonempty (D ≃* SL(3,BinaryField.four.Carrier)) ∨
  Nonempty (D ≃* Matrix.symplecticGroup (Fin 2) BinaryField.four.Carrier)

/-- The catalogue transports the actual component through an actor isomorphism. -/
theorem ActorList.of_mulEquiv {D E : Type*} [Group D] [Group E]
    (h : ActorList D) (e : E ≃* D) : ActorList E := by
  rcases h with ⟨n,hn,hu,⟨f⟩⟩ | ⟨n,hn,hu,⟨f⟩⟩ | hf | hf
  · exact Or.inl ⟨n,hn,hu,⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n,hn,hu,⟨e.trans f⟩⟩)
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inr (Or.inl ⟨e.trans f⟩))
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inr (Or.inr ⟨e.trans f⟩))

private noncomputable def fieldFourEquiv (F : BinaryField) (hF : F.degree = 2) :
    F.Carrier ≃+* BinaryField.four.Carrier := by
  let := Fintype.ofFinite F.Carrier
  let := Fintype.ofFinite BinaryField.four.Carrier
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, F.card_eq,
    BinaryField.four.card_eq, hF]
  rfl

private noncomputable def derivedSpEquivSix :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private theorem binary_model_mem {D : Type*} [Group D] {n : ℕ}
    (hn : 2 ≤ n) (hu : n ≤ 5) (e : D ≃* SL(n,ZMod 2)) : ActorList D :=
  Or.inl ⟨n,hn,hu,⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

private theorem alternating_model_mem {D : Type*} [Group D] {n : ℕ}
    (hn : 5 ≤ n) (hu : n ≤ 8) (e : D ≃* alternatingGroup (Fin n)) : ActorList D :=
  Or.inr (Or.inl ⟨n,hn,hu,⟨e⟩⟩)

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- Every original irreducible row is checked; only the covered-A6 geometry
is left as an explicit source row, with its actual coordinates. -/
theorem irreducible_actor_or_triple_of_plane {A L : Subgroup G}
    (hf : Function.Injective ρ) (hA : IsBestOffender ρ A)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ)) :
    ActorList L ∨ (offenderSubgroup ρ = L ∧
      Nonempty (SourceInduction.ProjectiveLine.TripleSixAction ρ L)) := by
  have hAH := hA.le_offenderSubgroup ρ
  cases hc with
  | linearTwo F gen e _ _ =>
    have hAL : A ≤ L := gen ▸ hAH
    have hdF := model_field_degree_le_two F ρ hf hA.1.1 hAL hd (specialLinearNatural 2) e
    have hp := F.degree_pos
    by_cases hF : F.degree = 1
    · exact Or.inl (binary_model_mem (by decide) (by decide)
        (e.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 2).groupEquiv))
    · have hF : F.degree = 2 := by omega
      obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (F.card_eq.trans (by rw [hF]; decide))
      exact Or.inl (alternating_model_mem (by decide) (by decide)
        (e.groupEquiv.trans ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier)).trans e5)))
  | linearThree F gen e _ =>
    have hAL : A ≤ L := gen ▸ hAH
    have hdF := model_field_degree_le_two F ρ hf hA.1.1 hAL hd (specialLinearNatural 3) e
    have hp := F.degree_pos
    by_cases hF : F.degree = 1
    · exact Or.inl (binary_model_mem (by decide) (by decide)
        (e.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv))
    · have hF : F.degree = 2 := by omega
      exact Or.inl (Or.inr (Or.inr (Or.inl
        ⟨e.groupEquiv.trans (Atlas.fieldEquivSL 3 (fieldFourEquiv F hF))⟩)))
  | symplectic F large gen e _ =>
    have hdF := model_field_degree_le_two F ρ hf hA.1.1 (gen ▸ hAH) hd (symplecticNatural 2) e
    have hF : F.degree = 2 := by omega
    exact Or.inl (Or.inr (Or.inr (Or.inr
      ⟨e.groupEquiv.trans (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp
        (fieldFourEquiv F hF))⟩)))
  | symplecticTwo e _ =>
    exact Or.inl (alternating_model_mem (by decide) (by decide)
      (e.subgroupEquiv.trans derivedSpEquivSix))
  | g2 F _ gen e _ _ =>
    exact (not_g2_model_of_plane ρ (hA.isOffender ρ) (gen ▸ hAH) hd F e).elim
  | g2Two e _ _ =>
    exact (not_g2_model_of_plane ρ (hA.isOffender ρ) hAH hd BinaryField.two e.action).elim
  | symmetric n hn e _ _ =>
    exact Or.inl (alternating_model_mem
      (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide) e.subgroupEquiv)
  | alternatingSix _ e _ _ =>
    exact Or.inl (alternating_model_mem (by decide) (by decide) e.groupEquiv)
  | alternatingSeven _ _ e _ _ _ =>
    exact Or.inl (alternating_model_mem (by decide) (by decide) e)
  | tripleSix gen action _ => exact Or.inr ⟨gen,⟨action⟩⟩
  | binaryLinear n hn _ e _ =>
    exact Or.inl (binary_model_mem
      (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide) e.groupEquiv)
  | orthogonalSix _ _ e _ _ =>
    exact Or.inl (alternating_model_mem (by decide) (by decide) e.groupEquiv)
  | symmetricEight _ e _ =>
    exact Or.inl (alternating_model_mem (by decide) (by decide) e.subgroupEquiv)
  | exteriorFive _ _ e _ _ _ =>
    exact Or.inl (binary_model_mem (by decide) (by decide) e)

/-- The complete B.5.1 reduction retains the precise remaining covered-A6
contract on its actual central quotient, including a genuine best offender. -/
theorem source_actor_or_triple_of_plane {A L : Subgroup G}
    (hA : IsOffender ρ A) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    ActorList L ∨ (Function.Injective s.central.quotientRepresentation ∧
      offenderSubgroup s.central.quotientRepresentation = L ∧
      Nonempty (SourceInduction.ProjectiveLine.TripleSixAction s.central.quotientRepresentation L) ∧
      ∃ C ≤ A, IsBestOffender s.central.quotientRepresentation C ∧
        Module.finrank (ZMod 2) (moved s.central.quotientRepresentation C) ≤ 2) := by
  rcases source_irreducible_or_binary_of_plane ρ hA hd s hc with hi | ⟨n,hn,⟨e⟩⟩
  · let Q := s.central.quotientRepresentation
    have hoff := hA.on_subquotient ρ s.space s.central
    obtain ⟨C,hCA,hC⟩ := hoff.exists_bestOffender Q
    have hdim := (moved_finrank_quotient_le s.space.toRepresentation s.central A).trans
      ((moved_finrank_subrepresentation_le ρ s.space A).trans hd)
    have hle : moved Q C ≤ moved Q A := by
      apply Submodule.span_mono
      rintro v ⟨c,hc,w,hw,hv⟩
      exact ⟨c,hCA hc,w,hw,hv⟩
    have hdC := (Submodule.finrank_mono hle).trans hdim
    rcases irreducible_actor_or_triple_of_plane Q hi.2.1 hC hdC hi.2.2.2 with hgood | htri
    · exact Or.inl hgood
    · exact Or.inr ⟨hi.2.1,htri.1,htri.2,C,hCA,hC,hdC⟩
  · exact Or.inl (binary_model_mem
      (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide) e.groupEquiv)
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
