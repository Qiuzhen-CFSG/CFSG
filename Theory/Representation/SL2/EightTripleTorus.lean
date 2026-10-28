module
public import Theory.Representation.SL2.BinarySmallInvolution.TripleFixedSpaces
public import BenderSuzuki.Converse.PSL2
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.Representation.SL2.EightTriple

/-!
# The order-seven fixed space of the actual binary triple module

The upper-root orbit basis is permuted by the diagonal torus through square
multiplication on its field parameter. Its tensor seed has weight minus seven,
so it is fixed over the field of eight elements. The two orbits are zero and
the nonzero field elements. Sylow conjugacy retains any specified subgroup
of order seven, and scalar-extension invariants descend the fixed dimension
to the original binary action. The final theorem uses intrinsic degree-eight
irreducibility to construct the tensor comparison.
-/

noncomputable section
open Module Matrix.SpecialLinearGroup BenderSuzuki.Converse
open scoped MatrixGroups TensorProduct
namespace Representation.SL2.BinarySmall.TripleFixedSpaces
noncomputable section
/-- Intertwining equivalences identify fixed subspaces. -/
private def torusInvariantsEquiv {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W} (φ : ρ.Equiv σ) :
    ρ.invariants ≃ₗ[F] σ.invariants where
  toFun v := ⟨φ v, by
    intro g
    have h := IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v
    rw [v.property g] at h
    exact h.symm⟩
  invFun v := ⟨φ.symm v, by
    intro g
    have h := IntertwiningMap.isIntertwining σ ρ φ.symm.toIntertwiningMap g v
    rw [v.property g] at h
    exact h.symm⟩
  left_inv v := Subtype.ext (φ.toLinearEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (φ.toLinearEquiv.apply_symm_apply v)
  map_add' x y := Subtype.ext (map_add φ (x : V) (y : V))
  map_smul' a v := Subtype.ext (map_smul φ a (v : V))


variable {K : Type*} [Field K] [Finite K] [CharP K 2]

@[instance_reducible] private def squareAction : MulAction Kˣ (Multiplicative K) where
  smul a t := Multiplicative.ofAdd ((a : K)^2 * t.toAdd)
  one_smul t := by change Multiplicative.ofAdd ((1 : K)^2 * t.toAdd) = t; simp
  mul_smul a b t := by
    change Multiplicative.ofAdd (((a*b : Kˣ) : K)^2 * t.toAdd) = Multiplicative.ofAdd ((a : K)^2 * ((b : K)^2 * t.toAdd))
    simp [mul_pow,mul_assoc]
local instance : MulAction Kˣ (Multiplicative K) := squareAction

private theorem torus_fixed_seed (hK : Nat.card K = 8) (a : Kˣ) :
    triple (torHom K a) (tensorBasis ((1,1),1)) = tensorBasis ((1,1),1) := by
  have hp : ((a⁻¹ : Kˣ) : K)^7 = 1 := by
    have hu : a⁻¹ ^ 7 = 1 := by
      simpa [Nat.card_units,hK] using pow_card_eq_one' (x := a⁻¹)
    exact congrArg Units.val hu
  simp only [tensorBasis, Basis.tensorProduct_apply, triple_apply_tmul]
  have hf (j : ℕ) : frobeniusNatural j (torHom K a) ((Pi.basisFun K (Fin 2)) 1) =
      (((a⁻¹ : Kˣ) : K) ^ (2^j)) • ((Pi.basisFun K (Fin 2)) 1) := by
    ext i
    fin_cases i <;> simp [frobeniusNatural_apply, torHom, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, iterateFrobenius_def]
  rw [hf,hf,hf]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
  norm_num only [pow_zero, pow_one, Nat.reducePow]
  have hh : ((a⁻¹ : Kˣ) : K)^4 * (((a⁻¹ : Kˣ) : K)^2 * ((a⁻¹ : Kˣ) : K)) = 1 := by
    calc _ = ((a⁻¹ : Kˣ) : K)^7 := by ring
         _ = 1 := hp
  rw [hh,one_smul]

omit [Finite K] [CharP K 2] in
private theorem torus_upper (a : Kˣ) (t : Multiplicative K) :
    torHom K a * upperUnipotentHom K t = upperUnipotentHom K (a • t) * torHom K a := by
  have hs : (a • t).toAdd = (a : K)^2 * t.toAdd := rfl
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torHom, upperUnipotentHom, transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, hs, pow_two, mul_assoc, mul_comm, mul_left_comm]

private theorem torus_orbit_basis [Fintype K] (hK : Nat.card K = 8)
    (a : Kˣ) (t : Multiplicative K) :
    triple (torHom K a) (upperOrbitBasis hK t) = upperOrbitBasis hK (a • t) := by
  rw [upperOrbitBasis_apply, ← Module.End.mul_apply, ← map_mul, torus_upper,
    map_mul, Module.End.mul_apply,torus_fixed_seed hK,upperOrbitBasis_apply]

private theorem square_orbit (x y : Multiplicative K) :
    MulAction.orbitRel Kˣ (Multiplicative K) x y ↔ (x.toAdd = 0 ↔ y.toAdd = 0) := by
  rw [MulAction.orbitRel_apply]
  constructor
  · rintro ⟨a,rfl⟩
    change (a : K)^2 * y.toAdd = 0 ↔ y.toAdd = 0
    simp [a.ne_zero]
  · intro h
    by_cases hy : y.toAdd = 0
    · have hx := h.mpr hy
      refine ⟨1,?_⟩
      change (1 : Kˣ) • y = x
      rw [one_smul]
      exact Multiplicative.toAdd.injective (hy.trans hx.symm)
    · have hx : x.toAdd ≠ 0 := mt h.mp hy
      obtain ⟨a,ha⟩ := surjective_frobenius K 2 (x.toAdd / y.toAdd)
      have ha' : a^2 = x.toAdd / y.toAdd := ha
      have ha0 : a ≠ 0 := by
        intro hz
        have hn := div_ne_zero hx hy
        apply hn
        simpa [hz] using ha'.symm
      refine ⟨Units.mk0 a ha0,?_⟩
      change Multiplicative.ofAdd (a^2 * y.toAdd) = x
      rw [ha',div_mul_cancel₀ _ hy]
      rfl

private theorem square_orbit_card :
    Nat.card (MulAction.orbitRel.Quotient Kˣ (Multiplicative K)) = 2 := by
  classical
  let f : Multiplicative K → Bool := fun x => decide (x.toAdd = 0)
  have hf : Function.Surjective f := by
    intro b
    cases b
    · exact ⟨Multiplicative.ofAdd 1,by simp [f]⟩
    · exact ⟨Multiplicative.ofAdd 0,by simp [f]⟩
  let e : MulAction.orbitRel.Quotient Kˣ (Multiplicative K) ≃ Bool :=
    (Quotient.congrRight (fun x y => by
      change MulAction.orbitRel Kˣ (Multiplicative K) x y ↔ f x = f y
      simp only [f,decide_eq_decide]
      exact square_orbit x y)).trans (Setoid.quotientKerEquivOfSurjective f hf)
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool]

private theorem fixed_finrank_of_square_basis
    {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K Kˣ W) (b : Basis (Multiplicative K) K W)
    (hb : ∀ a t, ρ a (b t) = b (a • t)) : finrank K ρ.invariants = 2 := by
  exact (permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card ρ b hb).trans
    (square_orbit_card (K := K))

omit [CharP K 2] in
private theorem seven_conjugate_torus (hK : Nat.card K = 8)
    (C : Subgroup SL(2,K)) (hc : Nat.card C = 7) :
    ∃ g : SL(2,K), ((MulAut.conj g).toMonoidHom.comp (torHom K)).range = C := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let T := (torHom K).range
  have ht : Nat.card T = 7 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (torHom_injective (F := K))).toEquiv,
      Nat.card_units,hK]
  have hi (X : Subgroup SL(2,K)) (hx : Nat.card X = 7) : ¬ 7 ∣ X.index := by
    have hh := X.index_mul_card
    rw [hx,Atlas.card_sl_two,hK] at hh
    have hindex : X.index = 72 := by omega
    rw [hindex]
    decide
  let P : Sylow 7 SL(2,K) := (IsPGroup.of_card (p := 7) (n := 1) (by simpa using ht)).toSylow (hi T ht)
  let Q : Sylow 7 SL(2,K) := (IsPGroup.of_card (p := 7) (n := 1) (by simpa using hc)).toSylow (hi C hc)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,K) P Q
  refine ⟨g,?_⟩
  rw [MonoidHom.range_comp]
  exact congrArg Sylow.toSubgroup hg

private theorem fixed_finrank_of_conjugate_square_basis
    {G W : Type*} [Group G] [AddCommGroup W] [Module K W]
    (ρ : Representation K G W) (f0 : Kˣ →* G)
    (basis : Basis (Multiplicative K) K W)
    (hbase : ∀ a t, ρ (f0 a) (basis t) = basis (a • t))
    (C : Subgroup G) (g : G)
    (hg : ((MulAut.conj g).toMonoidHom.comp f0).range = C) :
    finrank K (Representation.invariants (ρ.comp C.subtype)) = 2 := by
  let f := (MulAut.conj g).toMonoidHom.comp f0
  let e : W ≃ₗ[K] W :=
    { toLinearMap := ρ g
      invFun := ρ g⁻¹
      left_inv := ρ.inv_self_apply g
      right_inv := ρ.self_inv_apply g }
  let b := basis.map e
  have hb (a : Kˣ) (t : Multiplicative K) : ρ (f a) (b t) = b (a • t) := by
    change ρ (g * f0 a * g⁻¹) (ρ g (basis t)) =
      ρ g (basis (a • t))
    simp only [map_mul,Module.End.mul_apply,ρ.inv_self_apply]
    exact congrArg (ρ g) (hbase a t)
  have he : Representation.invariants (k := K) (V := W) (ρ.comp C.subtype) =
      Representation.invariants (k := K) (V := W) (ρ.comp f) := by
    ext v
    constructor
    · intro hv a
      have ha : f a ∈ C := by rw [←hg]; exact ⟨a,rfl⟩
      exact hv ⟨f a,ha⟩
    · intro hv a
      have ha : (a : G) ∈ f.range := by rw [hg]; exact a.property
      obtain ⟨u,hu⟩ := ha
      change ρ (a : G) v = v
      rw [←hu]
      exact hv u
  change finrank K (Representation.invariants (k := K) (V := W) (ρ.comp C.subtype)) = 2
  rw [he]
  exact fixed_finrank_of_square_basis (ρ.comp f) b hb


/-- Every actual subgroup of order seven has a two-dimensional fixed space
on the triple tensor. -/
public theorem triple_seven_fixed_finrank (hK : Nat.card K = 8)
    (C : Subgroup SL(2,K)) (hc : Nat.card C = 7) :
    finrank K (Representation.invariants (k := K) (V := TripleSpace K)
      ((triple (K := K)).comp C.subtype)) = 2 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨g,hg⟩ := seven_conjugate_torus hK C hc
  have hh := fixed_finrank_of_conjugate_square_basis
    (W := TripleSpace K) (triple (K := K)) (torHom K) (upperOrbitBasis hK)
    (fun a t => torus_orbit_basis hK a t) C g hg
  exact hh

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Scalar extension preserves the literal fixed space of every subgroup of
order seven on the binary triple module. -/
public theorem binary_seven_fixed_finrank (hK : Nat.card K = 8)
    (σ : Representation (ZMod 2) SL(2,K) V) (hσ : IsTriple σ)
    (C : Subgroup SL(2,K)) (hc : Nat.card C = 7) :
    finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace σ C) = 2 := by
  obtain ⟨e⟩ := hσ
  let eC : Representation.Equiv ((extendScalars K σ).comp C.subtype)
      ((triple (K := K)).comp C.subtype) :=
    .mk e.toLinearEquiv (fun g => e.isIntertwining' g.val)
  have hbase := finrank_invariants_extendScalars_eq_of_finite (E := K) (σ.comp C.subtype)
  change finrank K (Representation.invariants ((extendScalars K σ).comp C.subtype)) =
    finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace σ C) at hbase
  rw [← hbase, (torusInvariantsEquiv (F := K) (W := TripleSpace K) eC).finrank_eq]
  exact triple_seven_fixed_finrank hK C hc

omit [Field K] [Finite K] [CharP K 2] in
/-- The conclusion applies to the actual irreducible binary action of degree
eight, with no supplied tensor comparison. -/
public theorem eight_irreducible_seven_fixed_finrank
    (σ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [σ.IsIrreducible]
    (hd : finrank (ZMod 2) V = 8)
    (C : Subgroup SL(2,GaloisField 2 3)) (hc : Nat.card C = 7) :
    finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace σ C) = 2 :=
  binary_seven_fixed_finrank (GaloisField.card 2 3 (by decide)) σ
    (eight_irreducible_isTriple σ hd) C hc

end
end Representation.SL2.BinarySmall.TripleFixedSpaces
