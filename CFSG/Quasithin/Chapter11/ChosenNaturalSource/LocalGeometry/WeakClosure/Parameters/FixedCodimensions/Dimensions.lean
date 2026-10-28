module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Contracts
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.FirstCohomologyCyclic
open Subgroup Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
/-!
# Dimensions of the original natural-module flag preimages

The literal coordinate projection has kernel C_V(L). Its surjectivity identifies
the relative index of a field-subspace preimage with the corresponding vector
quotient cardinality. Restriction of scalars then computes the binary corank.
This retains the whole central attachment, including nonsplit Sp₄(4) modules.
The final inequality supplies the dimension clause of the parameter calculation.

Source: Aschbacher--Smith, 11.2.2(1--3), printed pp.767--768.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.NaturalDimensions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (c : Coordinates D S.field)
/-- The relative index is the index of the actual field-subspace quotient. -/
theorem pullback_index (U : Submodule S.field.Carrier c.Space) :
    (c.preimage U).relIndex V =
      (U.restrictScalars (ZMod 2)).toAddSubgroup.toSubgroup.index := by
  have h : (c.preimage U).subgroupOf V =
      (U.restrictScalars (ZMod 2)).toAddSubgroup.toSubgroup.comap c.projection := by
    ext v
    change (v : G) ∈ c.preimage U ↔ (c.projection v).toAdd ∈ U
    exact c.mem_preimage U v
  change ((c.preimage U).subgroupOf V).index = _
  rw [h]
  exact Subgroup.index_comap_of_surjective _ c.projection_surjective

/-- Binary corank is field degree times field codimension. -/
theorem pullback_corank (U : Submodule S.field.Carrier c.Space) :
    subgroupCorank V (c.preimage U) =
      S.field.degree * Module.finrank S.field.Carrier (c.Space ⧸ U) := by
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  rw [subgroupCorank, pullback_index D S c U, AddSubgroup.index_toSubgroup,
    AddSubgroup.index_eq_card]
  change Nat.log 2 (Nat.card (c.Space ⧸ U.restrictScalars (ZMod 2))) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2),
    (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) U).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) S.field.Carrier,
    coefficient_finrank_of_card 2 _ S.field.card_eq]

/-- The dimension follows from the literal chosen action marking. -/
theorem field_dimension : Module.finrank S.field.Carrier c.Space =
    match c with | .sl3 _ => 3 | .sp4 _ => 4 | .g2 _ => 6 := by
  cases c with
  | sl3 m => exact Module.finrank_pi _
  | sp4 m =>
    change Module.finrank S.field.Carrier ((Fin 2 ⊕ Fin 2) → S.field.Carrier) = 4
    simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
  | g2 m => exact Atlas.G2.Natural.finrank_space S.field.Carrier

/-- The source flag preimages have the expected binary coranks. -/
theorem flag_corank (f : InvariantFlag c) (i : Fin 3) :
    subgroupCorank V (f.Vi i) = S.field.degree *
      (Module.finrank S.field.Carrier c.Space - (i.val + 1)) := by
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  rw [InvariantFlag.Vi, pullback_corank D S c]
  congr 1
  have h := (f.space i).finrank_quotient_add_finrank
  rw [f.dimension] at h
  omega

/-- Even after dividing by the full central part, the dimension exceeds 2m. -/
theorem dimension_central : 2 * naturalParameter D S c <
    subgroupCorank V (V ⊓ centralizer (L : Set G)) := by
  rw [← c.preimage_bot, pullback_corank D S c]
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule S.field.Carrier c.Space) rfl).finrank_eq]
  rw [field_dimension D S c]
  have hn := S.nonbinary
  cases c <;> simp only [naturalParameter] <;> omega

/-- The dimension inequality used in the fixed-codimension contract. -/
theorem dimension : 2 * naturalParameter D S c < subgroupCorank V ⊥ :=
  (dimension_central D S c).trans_le (Section06.subgroupCorank_antitone bot_le)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.NaturalDimensions
