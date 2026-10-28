module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.SourceFields
public import Theory.Representation.OrthogonalFourPlusMatrix.Action

/-!
# The independently marked orthogonal action on P

An additive marking of the actual Y/P action by the two SL₂ factors gives
an E-linear conjugation representation on P. Its four-dimensional matrix
coordinates also determine the dimension after any transport to a field of
the same order. No compatibility with the separately marked natural V is
assumed here; Source constructs that compatibility on the literal intersection.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the orthogonal
module paragraph preceding 11.3.8, printed pp.774–775.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] (E : BinaryField) (P Y : Subgroup G) [IsMulCommutative P]

/-- An independent orthogonal marking of the actual Y/P action on P.
Its coordinates are additive; no compatibility with the natural field on V is assumed. -/
structure OrthogonalMarking where
  core_le : P ≤ Y
  actors : Y →* PairSL (F := E.Carrier)
  surjective : Function.Surjective actors
  kernel : actors.ker = P.subgroupOf Y
  coordinates : Additive P ≃+ Mat (F := E.Carrier)
  intertwines : ∀ (y : Y) (v : Mat (F := E.Carrier)),
    ((coordinates.symm (matrixAction (actors y) v)).toMul : G) =
      MulAut.conj (y : G) ((coordinates.symm v).toMul : G)

namespace OrthogonalMarking
variable {E P Y} (d : OrthogonalMarking E P Y)

/-- The field on P is transported solely from its independent orthogonal marking. -/
@[instance_reducible] def moduleStructure : Module E.Carrier (Additive P) :=
  d.coordinates.module E.Carrier

/-- The full Y-action is linear for this independently constructed field. -/
def action :
    let := d.moduleStructure
    Representation E.Carrier Y (Additive P) := by
  let := d.moduleStructure
  exact (d.coordinates.linearEquiv E.Carrier).symm.conjRingEquiv.toMonoidHom.comp
    (representation.comp d.actors)

theorem action_conj (y : Y) (p : Additive P) :
    ((d.action y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G) := by
  have h := d.intertwines y (d.coordinates p)
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- The literal P has dimension four over its independent orthogonal field. -/
theorem finrank :
    let := d.moduleStructure
    Module.finrank E.Carrier (Additive P) = 4 := by
  let := d.moduleStructure
  dsimp only
  rw [(d.coordinates.linearEquiv E.Carrier).finrank_eq]
  change Module.finrank E.Carrier (Fin 2 → Fin 2 → E.Carrier) = 4
  simp [Module.finrank_pi_fintype]

include d in
/-- The marking in particular proves normalization of the original subgroup P. -/
theorem normalizes : Y ≤ normalizer (P : Set G) := by
  intro y hy
  apply mem_normalizer_iff.mpr
  intro p
  constructor
  · intro hp
    have h := d.action_conj ⟨y,hy⟩ (Additive.ofMul ⟨p,hp⟩)
    have hm := (d.action ⟨y,hy⟩ (Additive.ofMul ⟨p,hp⟩)).toMul.property
    change ((d.action ⟨y,hy⟩ (Additive.ofMul ⟨p,hp⟩)).toMul : G) ∈ P at hm
    rw [h] at hm
    exact hm
  · intro hp
    have h := d.action_conj (⟨y,hy⟩ : Y)⁻¹ (Additive.ofMul ⟨y * p * y⁻¹,hp⟩)
    have hm := h ▸ (d.action (⟨y,hy⟩ : Y)⁻¹ (Additive.ofMul ⟨y * p * y⁻¹,hp⟩)).toMul.property
    simpa [MulAut.conj_apply,mul_assoc] using hm

omit [IsMulCommutative P] in
include d in
/-- The independent marking fixes the order of the literal P. -/
theorem card : Nat.card P = (Nat.card E.Carrier) ^ 4 := by
  have h := Nat.card_congr d.coordinates.toEquiv
  change Nat.card P = Nat.card (Fin 2 → Fin 2 → E.Carrier) at h
  simpa only [Nat.card_fun,Nat.card_fin,← pow_mul] using h

include d in
/-- Every transported field of the same order still makes P four-dimensional. -/
theorem finrank_of_same_field [Finite G] (F : BinaryField)
    [Module F.Carrier (Additive P)] (hc : Nat.card E.Carrier = Nat.card F.Carrier) :
    Module.finrank F.Carrier (Additive P) = 4 := by
  have h := Module.natCard_eq_pow_finrank (K := F.Carrier) (V := Additive P)
  change Nat.card P = (Nat.card F.Carrier) ^ Module.finrank F.Carrier (Additive P) at h
  rw [d.card,hc] at h
  exact Nat.pow_right_injective (show 1 < Nat.card F.Carrier from by
    rw [F.card_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt F.degree_pos) (by decide)) h.symm

end OrthogonalMarking
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
