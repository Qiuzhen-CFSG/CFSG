module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Separation
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual.Displacement
/-!
# The 22-vector orbit and its actual stabilizers

The quotient identifies pairs through coordinate 0 with pairs through 9.
Equivariance and separation identify vector stabilizers with the native point
stabilizer and the setwise-pair group's moving-point stabilizer, respectively.
Orbit--stabilizer gives orders 20160 and 40320. These numerical results do not
assert an identification with a projective linear group.

Source: Aschbacher--Smith, H.15.1, printed p.398; inner-stabilizer use in
8.1.1, printed p.712.
-/

@[expose] public section
open Sporadic.Mathieu
open scoped BigOperators Pointwise
namespace MathieuCode
noncomputable section

private theorem full_single (g : M24) (i : Fin 24) :
    fullRepresentation g (Pi.single i 1) = Pi.single (g • i) 1 := by
  ext j
  change (Pi.single i 1 : Full) (g.val.symm j) = (Pi.single (g.val i) 1 : Full) j
  simp only [Pi.single_apply]
  congr 1
  exact propext g.val.symm_apply_eq

theorem m22CocodePair_equivariant (g : m22PairStabilizer) (i j : Fin 24) :
    m22OuterCocodeRepresentation g (m22CocodePair i j) =
      m22CocodePair (g.val • i) (g.val • j) := by
  rw [m22CocodePair, m22OuterCocodeRepresentation_mk, cocodeRepresentation_mk]
  apply congrArg (fun v : Core => m22PairLine.mkQ (codeInCore.mkQ v))
  apply Subtype.ext
  change fullRepresentation g.val (Pi.single i 1 + Pi.single j 1) = _
  rw [map_add, full_single, full_single]
  rfl

theorem m22CocodePair_nine (i : Fin 24) : m22CocodePair 9 i = m22CocodePair 0 i := by
  have h : m22CocodePair 9 i - m22CocodePair 0 i = m22CocodePair 0 9 := by
    unfold m22CocodePair
    rw [← map_sub, ← map_sub]
    apply congrArg (fun v : Core => m22PairLine.mkQ (codeInCore.mkQ v))
    apply Subtype.ext
    change (Pi.single 9 1 + Pi.single i 1 : Full) -
      (Pi.single 0 1 + Pi.single i 1) = Pi.single 0 1 + Pi.single 9 1
    rw [add_sub_add_right_eq_sub]
    ext k
    change (Pi.single 9 1 : Full) k - (Pi.single 0 1 : Full) k =
      (Pi.single 0 1 : Full) k + (Pi.single 9 1 : Full) k
    rw [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  exact sub_eq_zero.mp (h.trans m22CocodePair_distinguished)

theorem m22WeightTwoVector_equivariant (g : M22) (i : Fin 22) :
    m22CocodeRepresentation g (m22WeightTwoVector i) = m22WeightTwoVector (g • i) := by
  change m22OuterCocodeRepresentation (m22ToPairStabilizer g)
    (m22CocodePair 0 (m22Coordinates i)) = _
  rw [m22CocodePair_equivariant]
  change m22CocodePair ((m22Embedding g).val 0)
    ((m22Embedding g).val (m22Coordinates i)) = _
  rw [m22Embedding_fixed_zero, m22Embedding_apply]
  rfl

theorem m22Coordinates_not_pair (i : Fin 22) : m22Coordinates i ∉ m22Pair := by
  revert i
  decide +kernel

theorem m22PairStabilizer_moves_coordinates (g : m22PairStabilizer) (i : Fin 22) :
    ∃ j : Fin 22, m22Coordinates j = g.val • m22Coordinates i := by
  have hout : g.val • m22Coordinates i ∉ m22Pair := fun h =>
    m22Coordinates_not_pair i ((MulAction.mem_stabilizer_finset.mp g.property _).mp h)
  obtain h | h | h := pairResidual_coordinates_cover (g.val • m22Coordinates i)
  · exact False.elim (hout (by simp [m22Pair, h]))
  · exact False.elim (hout (by simp [m22Pair, h]))
  · exact h

/-- On the quotient, exchanging the two marked coordinates has no effect on
which moving coordinate labels a weight-two vector. -/
theorem m22WeightTwoVector_outer (g : m22PairStabilizer) (i j : Fin 22)
    (hij : g.val • m22Coordinates i = m22Coordinates j) :
    m22OuterCocodeRepresentation g (m22WeightTwoVector i) = m22WeightTwoVector j := by
  change m22OuterCocodeRepresentation g (m22CocodePair 0 (m22Coordinates i)) = _
  rw [m22CocodePair_equivariant, hij]
  have h0 : g.val • (0 : Fin 24) ∈ m22Pair :=
    (MulAction.mem_stabilizer_finset.mp g.property _).mpr (by simp [m22Pair])
  have hh : g.val • (0 : Fin 24) = 0 ∨ g.val • (0 : Fin 24) = 9 := by
    simpa [m22Pair] using h0
  rcases hh with h | h
  · rw [h]; rfl
  · rw [h, m22CocodePair_nine]; rfl

theorem m22WeightTwoVector_fixed_iff (g : M22) (i : Fin 22) :
    m22CocodeRepresentation g (m22WeightTwoVector i) = m22WeightTwoVector i ↔ g • i = i := by
  rw [m22WeightTwoVector_equivariant, m22WeightTwoVector_injective.eq_iff]

theorem m22WeightTwoVector_outer_fixed_iff (g : m22PairStabilizer) (i : Fin 22) :
    m22OuterCocodeRepresentation g (m22WeightTwoVector i) = m22WeightTwoVector i ↔
      g.val • m22Coordinates i = m22Coordinates i := by
  obtain ⟨j, hj⟩ := m22PairStabilizer_moves_coordinates g i
  rw [m22WeightTwoVector_outer g i j hj.symm, m22WeightTwoVector_injective.eq_iff,
    ← hj, m22Coordinates.injective.eq_iff]

theorem m22WeightTwoFamily_nonzero {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    v ≠ 0 := by
  obtain ⟨i, rfl⟩ := hv
  exact m22WeightTwoVector_ne_zero i

theorem m22WeightTwoFamily_transitive (i j : Fin 22) :
    ∃ g : M22, m22CocodeRepresentation g (m22WeightTwoVector i) = m22WeightTwoVector j := by
  let := m22_isPretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 i j
  exact ⟨g, (m22WeightTwoVector_equivariant g i).trans (congrArg m22WeightTwoVector hg)⟩

theorem m22WeightTwoFamily_orbit (i : Fin 22) :
    m22WeightTwoFamily = {v | ∃ g : M22, m22CocodeRepresentation g (m22WeightTwoVector i) = v} := by
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    exact m22WeightTwoFamily_transitive i j
  · rintro ⟨g, rfl⟩
    exact ⟨g • i, (m22WeightTwoVector_equivariant g i).symm⟩

theorem m22WeightTwoFamily_outer_orbit (i : Fin 22) :
    m22WeightTwoFamily = {v | ∃ g : m22PairStabilizer,
      m22OuterCocodeRepresentation g (m22WeightTwoVector i) = v} := by
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := m22WeightTwoFamily_transitive i j
    exact ⟨m22ToPairStabilizer g, hg⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨j, hj⟩ := m22PairStabilizer_moves_coordinates g i
    exact ⟨j, (m22WeightTwoVector_outer g i j hj.symm).symm⟩

theorem m22WeightTwoFamily_card : Nat.card m22WeightTwoFamily = 22 := by
  change Nat.card (Set.range m22WeightTwoVector) = 22
  rw [← Nat.card_congr (Equiv.ofInjective m22WeightTwoVector m22WeightTwoVector_injective)]
  simp

/-- The stabilizer in a specified action on the literal ten-dimensional cocode. -/
def m22CocodeStabilizer {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G M22Cocode) (v : M22Cocode) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' {g} hg := ρ.inv_apply_eq_iff.mpr hg.symm

/-- The outer point stabilizer retains its inclusion in the degree-24 pair group. -/
def m22OuterPointStabilizer (i : Fin 22) : Subgroup m22PairStabilizer :=
  (MulAction.stabilizer M24 (m22Coordinates i)).comap m22PairStabilizer.subtype

theorem m22WeightTwoVector_stabilizer (i : Fin 22) :
    m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i) =
      MulAction.stabilizer M22 i := by
  ext g
  exact m22WeightTwoVector_fixed_iff g i

theorem m22WeightTwoVector_outer_stabilizer (i : Fin 22) :
    m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i) =
      m22OuterPointStabilizer i := by
  ext g
  exact m22WeightTwoVector_outer_fixed_iff g i

private theorem orbit_card_mul_stabilizer {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G M22Cocode) (v : M22Cocode) :
    Nat.card {w | ∃ g : G, ρ g v = w} * Nat.card (m22CocodeStabilizer ρ v) = Nat.card G := by
  let : MulAction G M22Cocode := {
    smul g w := ρ g w
    one_smul w := by change ρ 1 w = w; simp
    mul_smul g h w := by change ρ (g * h) w = ρ g (ρ h w); simp }
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G v)
  rw [Nat.card_prod] at h
  exact h

theorem m22WeightTwoVector_stabilizer_card (i : Fin 22) :
    Nat.card (m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i)) = 20160 := by
  have h := orbit_card_mul_stabilizer m22CocodeRepresentation (m22WeightTwoVector i)
  rw [← m22WeightTwoFamily_orbit, m22WeightTwoFamily_card, m22_order] at h
  omega

theorem m22WeightTwoVector_outer_stabilizer_card (i : Fin 22) :
    Nat.card (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i)) = 40320 := by
  have h := orbit_card_mul_stabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i)
  rw [← m22WeightTwoFamily_outer_orbit, m22WeightTwoFamily_card, m22PairStabilizer_card] at h
  omega

/-- The marked inclusion of the native point stabilizer into the outer one. -/
def m22PointToOuterPoint (i : Fin 22) :
    MulAction.stabilizer M22 i →* m22OuterPointStabilizer i where
  toFun g := ⟨m22ToPairStabilizer g.val, by
    change (m22Embedding g.val).val (m22Coordinates i) = m22Coordinates i
    rw [m22Embedding_apply, show g.val • i = i from g.property]⟩
  map_one' := by apply Subtype.ext; exact m22ToPairStabilizer.map_one
  map_mul' g h := by apply Subtype.ext; exact m22ToPairStabilizer.map_mul g.val h.val

@[simp] theorem m22PointToOuterPoint_coe (i : Fin 22) (g : MulAction.stabilizer M22 i) :
    (m22PointToOuterPoint i g).val = m22ToPairStabilizer g.val := rfl

end
end MathieuCode
