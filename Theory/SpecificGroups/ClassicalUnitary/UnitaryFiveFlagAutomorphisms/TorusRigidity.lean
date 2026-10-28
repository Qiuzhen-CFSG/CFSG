module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.RadicalRigidity

/-!
# Odd-torus normalization and the entire plane radical

An order-fifteen diagonal actor is fixed-point-free on the radical. Its
commutator map supplies one radical conjugation fixing that torus element;
no conjugacy of arbitrary Levi complements is assumed. The vector scalar
already determines the center scalar. Subtract these scalar formulas and
factor the error through the vector quotient. The torus's third power fixes
diagonal center coordinates, and its fifth power fixes off-diagonal ones;
neither has fixed vectors. Additivity therefore kills every error coordinate.
The remaining Levi displacement lies in the radical center and still obeys
the proved cocycle equation.

Source: the specialized coordinate reconstruction of Aschbacher–Smith
F.4.29(2), printed p.289 of refs/quasithin.pdf. Vanishing of the central Levi
cocycle, a matching unitary representative and opposite-endpoint agreement
remain separate obligations.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
open PlaneCore PlaneCore.ResidualAction
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem diagonalActor_mul (a b : Fˣ) : diagonalActor (a*b) = diagonalActor a * diagonalActor b := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

omit [CharP F 2] in
private theorem diagonalActor_pow (a : Fˣ) (n : ℕ) : diagonalActor (a^n) = diagonalActor a ^ n := by
  induction n with
  | zero =>
    rw [pow_zero,pow_zero]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalActor]
  | succ n ih => rw [pow_succ,diagonalActor_mul,ih,pow_succ]

omit [CharP F 2] in
private theorem additive_diagonal_fixed_zero (b : Fˣ) (hb : b ≠ 1)
    (f : (Fin 2 → F) →+ F) (hf : ∀ v, f ((diagonalActor b).val *ᵥ v) = f v) :
    ∀ v, f v = 0 := by
  have hb' : (b : F) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hb (Units.ext h))
  have hbi : ((b⁻¹ : Fˣ) : F) - 1 ≠ 0 := sub_ne_zero.mpr (fun h =>
    (inv_ne_one.mpr hb) (Units.ext h))
  intro v
  let w : Fin 2 → F := ![v 0 / ((b:F)-1),v 1 / (((b⁻¹ : Fˣ):F)-1)]
  have hdiv (a y : F) (ha : a-1 ≠ 0) : a*(y/(a-1))-y/(a-1)=y := by
    field_simp
  have hw : (diagonalActor b).val *ᵥ w - w = v := by
    change (Matrix.diagonal (fun i => ((![b,b⁻¹] : Fin 2 → Fˣ) i : F))) *ᵥ w - w = v
    ext i
    change (Matrix.diagonal (fun j => ((![b,b⁻¹] : Fin 2 → Fˣ) j : F)) *ᵥ w) i - w i = v i
    rw [Matrix.mulVec_diagonal]
    fin_cases i
    · exact hdiv (b:F) (v 0) hb'
    · exact hdiv ((b⁻¹:Fˣ):F) (v 1) hbi
  rw [←hw,map_sub,hf,sub_self]

omit [CharP F 2] in
private theorem torus_diagonal_fixed (hconj : ∀ b, J.conj b = b ^ 4)
    (a : Fˣ) (ha : a^15 = 1) (u : Parameters J) (i : Fin 2) :
    (Parameters.planeAction (diagonalActor (a^3)) u).z i i = u.z i i := by
  rw [diagonalActor_z J hconj]
  have h0 : a^3 * (a^3)^4 = 1 := by
    calc
      _ = a^15 := by group
      _ = 1 := ha
  have h1 : (a^3)⁻¹ * ((a^3)⁻¹)^4 = 1 := by
    calc
      _ = (a^15)⁻¹ := by group
      _ = 1 := by rw [ha,inv_one]
  fin_cases i
  · change ((a^3 * (a^3)^4 : Fˣ) : F) * u.z 0 0 = u.z 0 0
    rw [h0,Units.val_one,one_mul]
  · change (((a^3)⁻¹ * ((a^3)⁻¹)^4 : Fˣ) : F) * u.z 1 1 = u.z 1 1
    rw [h1,Units.val_one,one_mul]

omit [CharP F 2] in
private theorem torus_offdiagonal_fixed (hconj : ∀ b, J.conj b = b ^ 4)
    (a : Fˣ) (ha : a^15 = 1) (u : Parameters J) (i j : Fin 2) (hij : i ≠ j) :
    (Parameters.planeAction (diagonalActor (a^5)) u).z i j = u.z i j := by
  rw [diagonalActor_z J hconj]
  have h0 : a^5 * ((a^5)⁻¹)^4 = 1 := by
    calc
      _ = (a^15)⁻¹ := by group
      _ = 1 := by rw [ha,inv_one]
  have h1 : (a^5)⁻¹ * (a^5)^4 = 1 := by
    calc
      _ = a^15 := by group
      _ = 1 := ha
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change ((a^5 * ((a^5)⁻¹)^4 : Fˣ) : F) * u.z 0 1 = u.z 0 1
    rw [h0,Units.val_one,one_mul]
  · change (((a^5)⁻¹ * (a^5)^4 : Fˣ) : F) * u.z 1 0 = u.z 1 0
    rw [h1,Units.val_one,one_mul]
  · exact (hij rfl).elim

private def errorHom (a : MulAut (Parameters J)) (k : F) (hk : ∀ u, (a u).x = k • u.x) :
    Parameters J →* Multiplicative (Matrix (Fin 2) (Fin 2) F) where
  toFun u := Multiplicative.ofAdd ((a u).z - (k * J.conj k) • u.z)
  map_one' := by simp
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    ext i j
    change (a (u*v)).z i j - (k * J.conj k) * (u*v).z i j =
      ((a u).z i j - (k * J.conj k) * u.z i j) +
      ((a v).z i j - (k * J.conj k) * v.z i j)
    rw [map_mul]
    simp only [Parameters.mul_z,hk,Pi.smul_apply,smul_eq_mul,map_mul]
    ring

/-- The odd torus eliminates every central correction after the vector and
center scalars are known. Only the two indicated powers of its generator
are needed; no Levi-complement conjugacy is assumed. -/
theorem radical_full_scalar_of_torus (hconj : ∀ b, J.conj b = b ^ 4)
    (c : F) (hc : c + J.conj c = 1) (a : MulAut (Parameters J)) (k : F)
    (hk : ∀ u, (a u).x = k • u.x) (t : Fˣ) (ht : orderOf t = 15)
    (he : ∀ n u, a (Parameters.planeAction (diagonalActor (t^n)) u) =
      Parameters.planeAction (diagonalActor (t^n)) (a u)) :
    ∀ u : Parameters J, (a u).z = (k * J.conj k) • u.z := by
  let ε := errorHom J a k hk
  have hker : (Parameters.vectorHom J).ker ≤ ε.ker := by
    intro u hu
    have hu0 : u.x = 0 := hu
    change Multiplicative.ofAdd ((a u).z - (k * J.conj k) • u.z) = 1
    rw [radical_center_scalar J c hc a k hk u hu0,sub_self]
    rfl
  let f := (Parameters.vectorHom J).liftOfSurjective (Parameters.vectorHom_surjective J c hc) ⟨ε,hker⟩
  have hf (u : Parameters J) : f (Multiplicative.ofAdd u.x) = ε u := by
    change f (Parameters.vectorHom J u) = ε u
    simp [f]
  have hz (b : Fˣ) (hb : b ≠ 1) (i j : Fin 2)
      (hab : ∀ u, a (Parameters.planeAction (diagonalActor b) u) =
        Parameters.planeAction (diagonalActor b) (a u))
      (hfix : ∀ u : Parameters J, (Parameters.planeAction (diagonalActor b) u).z i j = u.z i j) :
      ∀ v : Fin 2 → F, (f (Multiplicative.ofAdd v)).toAdd i j = 0 := by
    let d : (Fin 2 → F) →+ F :=
      { toFun v := (f (Multiplicative.ofAdd v)).toAdd i j
        map_zero' := congrArg (fun z : Multiplicative (Matrix (Fin 2) (Fin 2) F) => z.toAdd i j) (map_one f)
        map_add' v w := congrArg (fun z : Multiplicative (Matrix (Fin 2) (Fin 2) F) => z.toAdd i j)
          (map_mul f (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
    apply additive_diagonal_fixed_zero b hb d
    intro v
    obtain ⟨u,hu⟩ := Parameters.vectorHom_surjective J c hc (Multiplicative.ofAdd v)
    have hv : u.x = v := congrArg Multiplicative.toAdd hu
    change (f (Multiplicative.ofAdd ((diagonalActor b).val *ᵥ v))).toAdd i j =
      (f (Multiplicative.ofAdd v)).toAdd i j
    rw [←hv,←Parameters.planeAction_x,hf,hf]
    change (a (Parameters.planeAction (diagonalActor b) u)).z i j -
      (k * J.conj k) * (Parameters.planeAction (diagonalActor b) u).z i j =
      (a u).z i j - (k * J.conj k) * u.z i j
    rw [hab,hfix,hfix]
  have ht15 : t^15 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ht3 : t^3 ≠ 1 := by
    intro hh
    have h := orderOf_dvd_of_pow_eq_one hh
    rw [ht] at h
    norm_num at h
  have ht5 : t^5 ≠ 1 := by
    intro hh
    have h := orderOf_dvd_of_pow_eq_one hh
    rw [ht] at h
    norm_num at h
  intro u
  ext i j
  have hzero : (f (Multiplicative.ofAdd u.x)).toAdd i j = 0 := by
    by_cases hij : i = j
    · subst j
      exact hz (t^3) ht3 i i (he 3) (fun v => torus_diagonal_fixed J hconj t ht15 v i) u.x
    · exact hz (t^5) ht5 i j (he 5) (fun v => torus_offdiagonal_fixed J hconj t ht15 v i j hij) u.x
  rw [hf] at hzero
  exact sub_eq_zero.mp hzero

variable [Finite F]

/-- Normalize an actual residual actor on one fixed-point-free odd torus
using a single radical conjugation. -/
theorem exists_torus_normalization (hconj : ∀ b, J.conj b = b ^ 4)
    (a : MulAut (PlaneSemidirect J)) (ha : ∀ p, (a p).right = p.right)
    (t : Fˣ) (ht : orderOf t = 15) :
    ∃ v : Parameters J,
      let b := (MulAut.conj (SemidirectProduct.inl v : PlaneSemidirect J))⁻¹ * a
      (∀ p, (b p).right = p.right) ∧
      b (SemidirectProduct.inr (diagonalActor t)) = SemidirectProduct.inr (diagonalActor t) := by
  let : Finite (Parameters J) := Finite.of_injective
    (fun u : Parameters J => (u.x,u.z)) (fun _ _ h => Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let A := diagonalActor t
  obtain ⟨v,hv⟩ := (diagonalActor_fixedPointFree J hconj t ht).commutatorMap_surjective (leviDeviation J a A)
  refine ⟨v,?_,?_⟩
  · intro p
    change ((SemidirectProduct.inl v : PlaneSemidirect J)⁻¹ * a p * SemidirectProduct.inl v).right = _
    simp only [←map_inv,SemidirectProduct.mul_right,SemidirectProduct.right_inl,one_mul,mul_one,ha]
  · change (SemidirectProduct.inl v : PlaneSemidirect J)⁻¹ * a (SemidirectProduct.inr A) *
      SemidirectProduct.inl v = SemidirectProduct.inr A
    apply SemidirectProduct.ext
    · simp only [←map_inv,SemidirectProduct.mul_left,SemidirectProduct.left_inl,
        SemidirectProduct.right_inl,SemidirectProduct.mul_right,map_one,MulAut.one_apply,one_mul,ha]
      change v⁻¹ * leviDeviation J a A * Parameters.planeAction A v = 1
      rw [←hv,MonoidHom.commutatorMap_apply,div_eq_mul_inv]
      dsimp only [A]
      group
    · simp only [←map_inv,SemidirectProduct.mul_right,SemidirectProduct.right_inl,one_mul,mul_one,ha]

/-- After this torus normalization the actor's full radical action is scalar,
including all noncentral parameters. -/
theorem radicalAction_full_scalar (hconj : ∀ b, J.conj b = b ^ 4)
    (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (PlaneSemidirect J)) (ha : ∀ p, (a p).right = p.right)
    (t : Fˣ) (ht : orderOf t = 15)
    (hfix : a (SemidirectProduct.inr (diagonalActor t)) = SemidirectProduct.inr (diagonalActor t)) :
    ∃ k : F, k ≠ 0 ∧ (∀ u, (radicalAction J a u).x = k • u.x) ∧
      (∀ u, (radicalAction J a u).z = (k * J.conj k) • u.z) := by
  obtain ⟨k,hk,hx⟩ := radicalAction_vector_scalar J c hc a ha
  refine ⟨k,hk,hx,radical_full_scalar_of_torus J hconj c hc (radicalAction J a) k hx t ht ?_⟩
  intro n u
  have hn : a (SemidirectProduct.inr (diagonalActor (t^n))) =
      SemidirectProduct.inr (diagonalActor (t^n)) := by
    rw [diagonalActor_pow,map_pow,map_pow,hfix]
  have hd : leviDeviation J a (diagonalActor (t^n)) = 1 := congrArg SemidirectProduct.left hn
  rw [radicalAction_compatibility J a ha,hd,one_mul,inv_one,mul_one]


/-- Once every radical coordinate has its scalar formula, the remaining
Levi displacement is central. This retains the actual cocycle; it does not
assert that it vanishes. -/
theorem leviDeviation_center (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (PlaneSemidirect J)) (ha : ∀ p, (a p).right = p.right)
    (k : F) (hx : ∀ u, (radicalAction J a u).x = k • u.x)
    (hz : ∀ u, (radicalAction J a u).z = (k * J.conj k) • u.z)
    (A : SpecialLinearGroup (Fin 2) F) : (leviDeviation J a A).x = 0 := by
  have he (u : Parameters J) : radicalAction J a (Parameters.planeAction A u) =
      Parameters.planeAction A (radicalAction J a u) := by
    apply Parameters.ext
    · rw [hx,Parameters.planeAction_x,Parameters.planeAction_x,hx,Matrix.mulVec_smul]
    · rw [hz,Parameters.planeAction_z,Parameters.planeAction_z,hz,Matrix.mul_smul,Matrix.smul_mul]
  apply (Parameters.mem_center_iff_x_eq_zero J c hc _).mp
  apply mem_center_iff.mpr
  intro v
  obtain ⟨u,rfl⟩ := (Parameters.planeAction A * radicalAction J a).surjective v
  have hh := (radicalAction_compatibility J a ha A u).symm
  rw [he] at hh
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
end Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
