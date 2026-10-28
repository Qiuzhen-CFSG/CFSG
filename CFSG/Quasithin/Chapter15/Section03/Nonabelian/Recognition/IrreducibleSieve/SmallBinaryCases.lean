module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import Theory.Representation.BinaryLinearRecognition
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight
public import Theory.SpecificGroups.Alternating.InvolutionCubicCentralizer
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.InvolutionNormalForm
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Transport
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.Quotient

/-!
# The small binary alternatives in the irreducible sieve

`Alternative` records exactly G.9.3(3), (4), (5), (11), (12), and (13),
independently of the source data of Chapter 15. Ambient-group and normal
component-join identifications are distinct. The genuine triple cover is
specified intrinsically by quasisimplicity, its central quotient A₆, and
its center of order three. No module identification is added to a case
where the printed statement gives only a group and degree.

Degree excludes (3), (11), and the degree-five part of (13). The centerless
minimal normal component join excludes (5). For (4) and (12), permutation
centralizers supply a cubic element commuting with the marked involution,
giving a cubic stabilizer of its literal displacement plane, contrary to
the source's prime-to-three stabilizer restriction. Only the
ten-dimensional part of (13) remains after `reduce_to_binary_five_ten`.
`exclude` closes that branch using the exhaustive identification with the exterior
square or cube. Involution conjugacy gives square displacement rank three or
four; the actual complementary-basis equivalence transports this exclusion to
the cube along the inverse-transpose automorphism. The original conditional
assembly remains available as `exclude_of_ten_dimensional_inputs`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.9.3,
printed pp.353–357, and the proof of 15.3.58, printed p.1149.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SmallBinaryCases

open Subgroup Representation
open CFSG.Quasithin.ChapterG.Section09
open Representation.BinaryLinearRecognition
open scoped MatrixGroups

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- The six source alternatives, with book `G,H` represented by `H,K`.
Quasiequivalence includes both the actual group and intertwining linear
isomorphisms. In particular, (13) does not assume exterior recognition. -/
inductive Alternative (ρ : Representation (ZMod 2) H W) (K : Subgroup H)
    (m : ℕ) : Prop
  | alternatingSevenFour
      (group : Nonempty (H ≃* alternatingGroup (Fin 7)))
      (degree : Module.finrank (ZMod 2) W = 4) (rank : m = 2) : Alternative ρ K m
  | alternatingSevenSix
      (group : Nonempty (K ≃* alternatingGroup (Fin 7)))
      (degree : Module.finrank (ZMod 2) W = 6) (rank : 2 ≤ m) : Alternative ρ K m
  | alternatingSixCover
      (quasisimple : Theory.GroupTheory.IsQuasisimple K)
      (quotient : Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 6)))
      (center_order : Nat.card (center K) = 3)
      (degree : Module.finrank (ZMod 2) W = 6) (rank : 2 ≤ m) : Alternative ρ K m
  | binaryFourNatural
      (module : Quasiequivalent ρ (naturalAction 4 (by decide)))
      (degree : Module.finrank (ZMod 2) W = 4) (rank : 1 ≤ m) : Alternative ρ K m
  | orthogonalEight
      (module : Quasiequivalent (ρ.comp K.subtype) orthogonalEightAction)
      (degree : Module.finrank (ZMod 2) W = 6) (rank : 2 ≤ m) : Alternative ρ K m
  | binaryFive
      (group : Nonempty (H ≃* PSL(5, ZMod 2)))
      (parameters : (Module.finrank (ZMod 2) W = 5 ∧ 2 ≤ m) ∨
        (Module.finrank (ZMod 2) W = 10 ∧ 4 ≤ m)) : Alternative ρ K m

variable [Finite H] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The actual normal A₇ and A₈ models each force a forbidden cubic element.
This argument applies to every ambient action and needs no module-recognition
premise beyond the subgroup's actual group identification. -/
theorem not_alternating_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : K ≃* alternatingGroup (Fin n)) : False := by
  let : K.Normal := hK.normal
  obtain ⟨b, hb, hcomm⟩ := alternatingGroup.exists_order_three_commuting_of_normalizes
    K hn e v (by rw [normalizer_eq_top]; exact mem_top v)
    (by rw [← h.involution]; exact pow_orderOf_eq_one v)
  apply h.no_cubic_plane_preserver b hb
  intro w hw
  exact Representation.RankTwo.map_mem_movedSpace_of_commute ρ hcomm.symm hw

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
/-- A genuine triple cover cannot be the centerless component join. -/
theorem not_triple_cover (hK : ComponentData ρ K)
    (hz : Nat.card (center K) = 3) : False := by
  rw [hK.center_eq_bot, card_bot] at hz
  norm_num at hz

/-- All but the ten-dimensional part of source case (13) are excluded.
The surviving identification is of the entire ambient actor. The original
actor rank is four (`s = 3`), not a replacement maximum two-rank. -/
theorem reduce_to_binary_five_ten (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (ha : Alternative ρ K (s + 1)) :
    Nonempty (H ≃* PSL(5, ZMod 2)) ∧ Module.finrank (ZMod 2) W = 10 ∧ s = 3 := by
  cases ha with
  | alternatingSevenFour _ hd _ => exact (h.degree_not_le_four hd.le).elim
  | alternatingSevenSix he _ _ =>
      obtain ⟨e⟩ := he
      exact (not_alternating_component h hK (Or.inl rfl) e).elim
  | alternatingSixCover _ _ hz _ _ => exact (not_triple_cover hK hz).elim
  | binaryFourNatural _ hd _ => exact (h.degree_not_le_four hd.le).elim
  | orthogonalEight he _ _ =>
      obtain ⟨e, _, _⟩ := he
      exact (not_alternating_component h hK (Or.inr rfl) e).elim
  | binaryFive he hd =>
      rcases hd with ⟨hd, _⟩ | ⟨hd, _⟩
      · have := h.six_le_degree
        omega
      · exact ⟨he, hd, by have := h.dimension; omega⟩

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
private theorem ambient_irreducible (hK : ComponentData ρ K) : IsIrreducible ρ := by
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (ρ.comp K.subtype)
  refine { eq_bot_or_eq_top := fun S => ?_ }
  let R : Subrepresentation (ρ.comp K.subtype) :=
    ⟨S.toSubmodule, fun k w hw => S.apply_mem_toSubmodule k hw⟩
  rcases hK.irreducible.eq_bot_or_eq_top R with hb | ht
  · have he := congrArg (fun U : Subrepresentation (ρ.comp K.subtype) => U.toSubmodule) hb
    exact Or.inl (Subrepresentation.toSubmodule_injective he)
  · have he := congrArg (fun U : Subrepresentation (ρ.comp K.subtype) => U.toSubmodule) ht
    exact Or.inr (Subrepresentation.toSubmodule_injective he)

/-- Displacement is transported through both maps of an actual exterior-model
identification. A bound only for selected involution representatives does not
supply the universally quantified model premise here. -/
theorem not_exterior_model (h : SourceData ρ X T v s) (r : ℕ)
    (hr : ∀ g : Representation.SL5TenDimensional.Group, orderOf g = 2 →
      Module.finrank (ZMod 2)
        (LinearMap.range (Representation.SL5TenDimensional.exteriorAction r g -
          LinearMap.id)) ≠ 2)
    (he : Quasiequivalent ρ (Representation.SL5TenDimensional.exteriorAction r)) : False := by
  obtain ⟨e, f, hf⟩ := he
  apply hr (e v) ((e.orderOf_eq v).trans h.involution)
  have hd := Representation.RankTwo.finrank_movedSpace_transport ρ
    (Representation.SL5TenDimensional.exteriorAction r) e f hf v
  exact hd.symm.trans h.displacement_rank

open Representation.SL5TenDimensional in
/-- Assembly from three explicit SL₅ inputs: exhaustive recognition
and displacement exclusion for every involution on each of the two exterior
modules. The statement does not strengthen source alternative (13). -/
theorem exclude_of_ten_dimensional_inputs (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (ha : Alternative ρ K (s + 1))
    (hten : ∀ σ : Representation (ZMod 2) Representation.SL5TenDimensional.Group W,
      IsIrreducible σ → Module.finrank (ZMod 2) W = 10 →
      Nonempty (σ.Equiv (exteriorAction 2)) ∨ Nonempty (σ.Equiv (exteriorAction 3)))
    (hsquare : ∀ g : Representation.SL5TenDimensional.Group, orderOf g = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (exteriorAction 2 g - LinearMap.id)) ≠ 2)
    (hcube : ∀ g : Representation.SL5TenDimensional.Group, orderOf g = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (exteriorAction 3 g - LinearMap.id)) ≠ 2) :
    False := by
  obtain ⟨⟨e⟩, hd, _⟩ := reduce_to_binary_five_ten h hK ha
  let E := e.trans projectiveEquiv.symm
  let σ := ρ.comp E.symm.toMonoidHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective ρ).mpr
      (ambient_irreducible hK)
  rcases hten σ hi hd with hf | hf
  · obtain ⟨f⟩ := hf
    apply not_exterior_model h 2 hsquare
    refine ⟨E, f.toLinearEquiv, ?_⟩
    intro g w
    have hf := congrArg (fun a : W →ₗ[ZMod 2] ExteriorModule 2 => a w)
      (f.isIntertwining' (E g))
    change f.toLinearEquiv (ρ (E.symm (E g)) w) = exteriorAction 2 (E g) (f.toLinearEquiv w) at hf
    simpa only [E.symm_apply_apply] using hf
  · obtain ⟨f⟩ := hf
    apply not_exterior_model h 3 hcube
    refine ⟨E, f.toLinearEquiv, ?_⟩
    intro g w
    have hf := congrArg (fun a : W →ₗ[ZMod 2] ExteriorModule 3 => a w)
      (f.isIntertwining' (E g))
    change f.toLinearEquiv (ρ (E.symm (E g)) w) = exteriorAction 3 (E g) (f.toLinearEquiv w) at hf
    simpa only [E.symm_apply_apply] using hf

open Representation.SL5TenDimensional Representation.SL5ExteriorSquare in
private theorem square_displacement_rank_ne_two (g : Representation.SL5TenDimensional.Group)
    (hg : orderOf g = 2) :
    Module.finrank (ZMod 2) (LinearMap.range (exteriorAction 2 g - LinearMap.id)) ≠ 2 := by
  have hne : g ≠ 1 := by
    intro he
    simp [he] at hg
  have hs : g * g = 1 := by
    simpa only [hg, pow_two] using pow_orderOf_eq_one g
  rcases involution_conjugacy_exhaustion g hne hs with h | h
  · exact fun htwo => (by decide : (3 : ℕ) ≠ 2) ((ranks_of_isConj_j₁ h).2.symm.trans htwo)
  · exact fun htwo => (by decide : (4 : ℕ) ≠ 2) ((ranks_of_isConj_j₂ h).2.symm.trans htwo)

open Representation.SL5TenDimensional Representation.SL5ExteriorSquare in
private theorem cube_displacement_rank_ne_two (g : Representation.SL5TenDimensional.Group)
    (hg : orderOf g = 2) :
    Module.finrank (ZMod 2) (LinearMap.range (exteriorAction 3 g - LinearMap.id)) ≠ 2 := by
  rw [EquivariantGeometry.displacement_rank (exteriorAction 3) (exteriorAction 2)
    Duality.graph Duality.hodge Duality.hodge_action g]
  exact square_displacement_rank_ne_two (Duality.graph g)
    ((Duality.graph.orderOf_eq g).trans hg)

open Representation.SL5TenDimensional in
/-- G.9.3(3), (4), (5), (11), (12), and (13) are impossible in the
irreducible branch of 15.3.58. The actual source actor rank is `s + 1`, and
exhaustive recognition and displacement exclusion for both ten-dimensional
exterior models are discharged without additional model premises. -/
theorem exclude (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (ha : Alternative ρ K (s + 1)) : False := by
  apply exclude_of_ten_dimensional_inputs h hK ha
  · intro σ hi hd
    let := hi
    exact Classification.identification_of_finrank_ten σ hd
  · exact square_displacement_rank_ne_two
  · exact cube_displacement_rank_ne_two

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SmallBinaryCases
