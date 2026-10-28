module
public import CFSG.Quasithin.ChapterG.Section11.WholeComponentCandidates
public import CFSG.Quasithin.ChapterG.Section11.WholeLinearThree
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import Theory.Representation.SmallSymplecticNormalThree
public import Theory.Representation.Mathieu.M22James.MinimumDegree
public import Theory.Mathieu.M22.TripleCover.Recognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover

/-!
# Excluding the actual central covers in a large whole-component action

The invariant alternating form makes the fixed component action self-dual.
The binary linear and unitary covers violate their actual degree windows.
Odd signed-three and triple-A6 covers have degree six; a normal cubic center
then forces solvability. The triple-M22 minimum degree exceeds twice the
actor rank. All centers and central quotients remain literal.

The proofs adapt the general part of Chapter14's larger-actor analysis.
The HS whole-component consumer uses the complete cover exclusion.
Source: Aschbacher--Smith G.5.1, G.7.3, G.9.3 and 14.3.24,
printed pp.342--343,348,354--357,1000.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.LargeWhole
open Section09
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X L H : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
open Section09.DefiningCharacteristic Chapter1.Section02.LocalModels
variable (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L L
      (finrank (ZMod 2) (Additive X)))
include h

/-- The supplied invariant pairing gives self-duality of the fixed component action. -/
theorem selfDual :
    Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (Representation.dual (ρ.comp L.subtype))) := by
  refine ⟨Representation.Equiv.mk (B.toDual h.nondegenerate) ?_⟩
  intro a
  ext u w
  change B (ρ a u) w = B u (ρ (a⁻¹ : L) w)
  have he := h.preserves a u (ρ (a⁻¹ : L) w)
  simpa only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv,
    mul_inv_cancel, map_one, Module.End.one_apply] using he

include h9
/-- A normal cubic center cannot occur in a whole component of degree at most six. -/
theorem not_single_cubic_center_small
    (hc : Nat.card (center L) = 3) (hd : finrank (ZMod 2) V ≤ 6) : False := by
  let : IsIrreducible (ρ.comp L.subtype) := h9.irreducible
  exact h9.component.isCComponent.not_isSolvable
    (SmallSymplecticNormalThree.isSolvable_of_normal_cubic
      (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective)
      B h.alternating h.nondegenerate
      (fun a u w => h.preserves a u w) hd (center L) hc)

/-- The genuine triple-A₆ cover has degree six; its cubic center contradicts
the invariant nondegenerate alternating form. -/
theorem not_single_triple_alternating_six (model : IsAlternatingCover L 6) : False := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h9.irreducible
  have hc : Nat.card (center L) = 3 :=
    (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
  have hd := AlternatingSixCover.small_degree_eq_six model.2.2.some hc
    (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    h9.single_component_degree_bound
  exact not_single_cubic_center_small h h9 hc hd.le

omit h in
/-- The triple-M₂₂ minimum degree twelve exceeds twice the actual actor
rank, which is at most five by faithful conjugation on the central quotient. -/
theorem not_single_triple_mathieu
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X)) (model : IsM22Cover L) : False := by
  let : IsQuasisimple L := h9.component.2
  have hr := TwistedExclusions.actor_rank_le_of_central_quotient h9 model.2.2.some
    Sporadic.Mathieu.m22_automorphism_twoRank_le_five
  have hc : Nat.card (center L) = 3 :=
    (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
  obtain ⟨e⟩ := Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hc model.2.2
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hl := Sporadic.Mathieu.M22TripleCover.faithful_irreducible_finrank_ge_twelve σ
    (h9.faithful.comp (L.subtype_injective.comp e.symm.injective))
  have hu := hlarge
  omega

/-- Odd signed-three carriers have degree six, so a central cubic excludes
the whole cover in the original symplectic action. -/
private theorem not_single_odd_three_cover (hc : Nat.card (center L) = 3)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) : False := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h9.irreducible
  obtain ⟨_,hd⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho model h9.single_component_degree_bound
  exact not_single_cubic_center_small h h9 hc hd.le

/-- Both signs and all source parameters of the classical central covers
are excluded on the actual whole component. -/
theorem not_single_classical_cover (hc : Nat.card (center L) = 3)
    (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q)
    (model : IsSLSign L unitary 3 q) : False := by
  cases unitary
  · change IsSL L 3 q at model
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
      let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
      exact WholeLinearThree.not_single_component_linear_three h9
        (selfDual h) e.symm.toMonoidHom e.symm.surjective
        (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le)
        n hn hcard
    · exact not_single_odd_three_cover h h9 hc hp ho (.inr (.inl model))
  · change IsSU L 3 q at model
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · obtain ⟨k,_,_,J,hcard,hconj,e⟩ := model
      exact TwistedExclusions.not_unitary_three_positive_exponent h9 J hn hcard hconj (.inl e)
    · exact not_single_odd_three_cover h h9 hc hp ho (.inr (.inr (.inr model)))

/-- All central-cover rows of the whole-component carrier sieve are impossible
for the original larger actor. -/
theorem not_single_cover
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X)) (hc : Nat.card (center L) = 3)
    (model : WholeComponentCandidates.Cover L) : False := by
  rcases model with ⟨u,q,hq,hm⟩ | ha | hm
  · exact not_single_classical_cover h h9 hc u q hq hm
  · exact not_single_triple_alternating_six h h9 ha
  · exact not_single_triple_mathieu h9 hlarge hm

end CFSG.Quasithin.ChapterG.Section11.LargeWhole
