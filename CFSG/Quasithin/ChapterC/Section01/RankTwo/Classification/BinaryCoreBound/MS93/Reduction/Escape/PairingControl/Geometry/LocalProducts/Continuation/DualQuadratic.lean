module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Triple
public import Theory.Representation.DualCommutator
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Quadratic action on the opposite local section

At a moving pair, the common edge displacement makes Q_start quadratic on
U_back. The natural and opposite coordinates use the same quotient marking.
The dot product identifies the inverse-transpose coordinates with the functional
dual, so quadratic duality makes Q_start quadratic on Vcirc_back/U_back.
The exact kernel of the coordinate map then gives the group estimate
`[[Vcirc_back,Q_start],Q_start] ≤ U_back`.

The coordinate bridges use the actual conjugation formulas and the image of
the group commutator in the linear commutator space. Neither normality of a
backward product nor a bound on a residual span enters this deduction.

Source: Meierfrankenfeld--Stellmacher (1993), the displayed triple-commutator
bound immediately after (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation

variable {G : Type*} [Group G] {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

/-- A surjective conjugation-coordinate map transports quadratic group action. -/
private theorem coordinate_quadratic (H A : Subgroup G) [H.Normal]
    (ρ : Representation k G E) (c : H →* Multiplicative E)
    (hs : Function.Surjective c)
    (hc : ∀ g x, (c (MulAut.conjNormal g x)).toAdd = ρ g (c x).toAdd)
    (hq : ⁅⁅H, A⁆, A⁆ = ⊥) :
    Coinvariants.ker (ρ.comp A.subtype) ≤ invariants (ρ.comp A.subtype) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, v⟩, rfl⟩ b
  obtain ⟨x, hx⟩ := hs (Multiplicative.ofAdd v)
  let y : H := MulAut.conjNormal a.val x * x⁻¹
  have hy : (y : G) ∈ ⁅H, A⁆ := by
    change ⁅a.val, x.val⁆ ∈ ⁅H, A⁆
    rw [commutator_comm]
    exact commutator_mem_commutator a.property x.property
  have hby : MulAut.conjNormal b.val y = y := by
    apply Subtype.ext
    have ht : ⁅b.val, y.val⁆ = 1 := by
      apply mem_bot.mp
      rw [← hq, commutator_comm]
      exact commutator_mem_commutator b.property hy
    exact (mul_inv_eq_one.mp ht)
  have hcY : (c y).toAdd = ρ a.val v - v := by
    change (c (MulAut.conjNormal a.val x * x⁻¹)).toAdd = _
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      ← sub_eq_add_neg, hc, hx, toAdd_ofAdd]
  have hh := hc b.val y
  rw [hby, hcY] at hh
  exact hh.symm

/-- Fixed linear displacements put the group triple commutator in the exact kernel. -/
private theorem triple_le_of_coordinate_quadratic (H N A : Subgroup G) [H.Normal]
    (ρ : Representation k G E) (c : H →* Multiplicative E)
    (hk : c.ker = N.subgroupOf H)
    (hc : ∀ g x, (c (MulAut.conjNormal g x)).toAdd = ρ g (c x).toAdd)
    (hq : Coinvariants.ker (ρ.comp A.subtype) ≤ invariants (ρ.comp A.subtype)) :
    ⁅⁅H, A⁆, A⁆ ≤ N := by
  let W := Coinvariants.ker (ρ.comp A.subtype)
  let K : Subgroup (Multiplicative E) := W.toAddSubgroup.toSubgroup
  have hcomm : ⁅H, A⁆ ≤ (K.comap c).map H.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha x hx
    let u : H := ⟨x, hx⟩
    let y : H := MulAut.conjNormal a u * u⁻¹
    refine ⟨y, ?_, rfl⟩
    change (c y).toAdd ∈ W
    change (c (MulAut.conjNormal a u * u⁻¹)).toAdd ∈ W
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      ← sub_eq_add_neg, hc]
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a, ha⟩ _
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha y hy
  obtain ⟨u, hu, rfl⟩ := hcomm hy
  have hfix := hq (show (c u).toAdd ∈ W from hu) ⟨a, ha⟩
  have he : c (MulAut.conjNormal a u * u⁻¹) = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      ← sub_eq_add_neg, hc, toAdd_one]
    exact sub_eq_zero.mpr hfix
  have hm : MulAut.conjNormal a u * u⁻¹ ∈ c.ker := he
  rw [hk] at hm
  exact hm

private noncomputable def markedRepresentation (π : G →* SL) (σ : SL ≃* SL) :
    Representation (ZMod 2) G (Fin 3 → ZMod 2) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (Matrix.SpecialLinearGroup.toLin'.comp (σ.toMonoidHom.comp π))

/-- The dot product intertwines inverse-transpose coordinates with the functional dual. -/
private theorem dual_coordinates_action (π : G →* SL) (σ : SL ≃* SL)
    (g : G) (v : Fin 3 → ZMod 2) :
    dotProductEquiv (ZMod 2) (Fin 3) (((σ (π g))⁻¹).val.transpose.mulVec v) =
      (markedRepresentation π σ).dual g (dotProductEquiv (ZMod 2) (Fin 3) v) := by
  apply LinearMap.ext
  intro w
  change dotProduct (((σ (π g))⁻¹).val.transpose.mulVec v) w =
    dotProduct v ((σ (π g⁻¹)).val.mulVec w)
  rw [map_inv, map_inv, dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

/-- Opposite factors for one marking inherit quadratic action from the natural factor. -/
private theorem dual_factor_quadratic {π : G →* SL} {H N Z : Subgroup G}
    (n : RankOnePairing.NaturalFactor π ⊤ Z ⊥)
    (d : RankOnePairing.DualFactor π ⊤ H N Z n) (A : Subgroup G)
    (hq : ⁅⁅Z, A⁆, A⁆ = ⊥) : ⁅⁅H, A⁆, A⁆ ≤ N := by
  let : Z.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp n.normalized)
  let : H.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp d.normalized)
  let ρ := markedRepresentation π n.marking
  have hn : Coinvariants.ker (ρ.comp A.subtype) ≤ invariants (ρ.comp A.subtype) :=
    coordinate_quadratic Z A ρ n.coordinates n.surjective
      (fun g x => n.action g (mem_top g) x (MulAut.conjNormal g x) rfl) hq
  have hd : Coinvariants.ker (ρ.dual.comp A.subtype) ≤ invariants (ρ.dual.comp A.subtype) :=
    (Representation.quadratic_dual_iff (ρ.comp A.subtype)).mpr hn
  let e := (dotProductEquiv (ZMod 2) (Fin 3)).toAddEquiv.toMultiplicative
  let c := e.toMonoidHom.comp d.coordinates
  apply triple_le_of_coordinate_quadratic H N A ρ.dual c _ _ hd
  · change (e.toMonoidHom.comp d.coordinates).ker = _
    exact (MonoidHom.ker_comp_of_injective d.coordinates e.toMonoidHom e.injective).trans
      d.kernel
  · intro g x
    change dotProductEquiv (ZMod 2) (Fin 3) (d.coordinates (MulAut.conjNormal g x)).toAdd = _
    rw [d.action g (mem_top g) x (MulAut.conjNormal g x) rfl]
    exact dual_coordinates_action π n.marking g (d.coordinates x).toAdd

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- At any moving pair across the given edge, the opposite quotient is quadratic. -/
theorem moving_triple_le_natural (hb : 2 < geometry.b R)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a) :
    ⁅⁅Vcirc R d, Q R a⁆, Q R a⁆ ≤ U R d := by
  have hdc := moving_color ha hd
  obtain ⟨o⟩ := facts.opposite d hdc
  have hU : U R d ≤ stabilizer R d := (U_le_Z d).trans (Z_le_stabilizer R d)
  have hV : Vcirc R d ≤ stabilizer R d :=
    (Vcirc_le_V d).trans (V_le_stabilizer_of_distance hdc (by simpa using hb.le))
  have hQ : Q R a ≤ stabilizer R d := Q_le_stabilizer_of_dist_two R a d ha hd.1
  have hquad : ⁅⁅(U R d).subgroupOf (stabilizer R d),
      (Q R a).subgroupOf (stabilizer R d)⁆,
      (Q R a).subgroupOf (stabilizer R d)⁆ = ⊥ := by
    apply map_injective (stabilizer R d).subtype_injective
    rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hU,
      map_subgroupOf_eq_of_le hQ, Subgroup.map_bot]
    exact moving_natural_quadratic facts p (by omega) initial bad ha hat hdt hd
  have hh := map_mono (f := (stabilizer R d).subtype)
    (dual_factor_quadratic o.naturalU o.dual _ hquad)
  simpa only [map_commutator, map_subgroupOf_eq_of_le hV,
    map_subgroupOf_eq_of_le hU, map_subgroupOf_eq_of_le hQ] using hh

/-- The exact backward-choice estimate used after MS93 (4.3.2)(6). -/
theorem backward_triple_le_natural (hb : 2 < geometry.b R)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a) (choice : BackwardChoice q) :
    ⁅⁅Vcirc R choice.back, Q R q.a⁆, Q R q.a⁆ ≤ U R choice.back :=
  moving_triple_le_natural hb facts q initial bad q.color_a
    choice.adjacent_start choice.adjacent_back choice.moving

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
