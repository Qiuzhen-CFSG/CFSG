module

public import Theory.Representation.InvertedOddElement
public import Theory.GroupAction.OddInversePairDisplacement

open scoped IsMulCommutative

universe u v

public theorem invertedOddSubgroup_card_eq_commutator_sq
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (A : Subgroup G) (odd : Odd (Nat.card A)) (x : G) (hx : IsInvolution x)
    (hinv : ∀ a : A, x * (a : G) * x⁻¹ = (a : G)⁻¹)
    (fixed : FixedPoints.subgroup A V = ⊥) :
    Nat.card V = Nat.card (commutatorAction (Subgroup.zpowers x) V) ^ 2 := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let d : V →* V :=
    { toFun := fun w => w⁻¹ * (x • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxx : x * x = 1 := by simpa [pow_two] using hx.2
  have hker : d.ker = FixedPoints.subgroup R V := by
    ext w
    constructor
    · intro hw
      rw [FixedPoints.mem_subgroup]
      intro r
      have hwx : x • w = w := (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, _hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp (by simpa [R, Nat.card_zpowers] using hxorder)
        let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
        have hrx : rx ≠ 1 := by intro h; exact hx.1 (congrArg Subtype.val h)
        have : r = rx := (huniq r hr).trans (huniq rx hrx).symm
        simpa [this, rx] using hwx
    · intro hw
      rw [MonoidHom.mem_ker]
      have hwx := (FixedPoints.mem_subgroup (M := R) (a := w)).1 hw ⟨x, Subgroup.mem_zpowers x⟩
      exact inv_mul_eq_one.mpr (by simpa using hwx.symm)
  have hrange : d.range = commutatorAction R V := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨x, Subgroup.mem_zpowers x⟩, w, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      rintro z ⟨r, w, rfl⟩
      by_cases hr : r = 1
      · subst r; exact ⟨1, by simp [d]⟩
      · obtain ⟨z, _hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp (by simpa [R, Nat.card_zpowers] using hxorder)
        let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
        have hrx : rx ≠ 1 := by intro h; exact hx.1 (congrArg Subtype.val h)
        have : r = rx := (huniq r hr).trans (huniq rx hrx).symm
        exact ⟨w, by simp [d, this, rx]⟩
  have hfixrange : FixedPoints.subgroup R V = d.range := by
    apply le_antisymm
    · intro w hw
      obtain ⟨preimage, hpreimage⟩ :=
        (OddInversePairDisplacement.fixed_iff_exists_displacement A odd x hx hinv fixed w).mp
          ((FixedPoints.mem_subgroup (M := R) (a := w)).1 hw ⟨x, Subgroup.mem_zpowers x⟩)
      exact ⟨preimage, by simpa [d] using hpreimage⟩
    · intro w hw
      rcases hw with ⟨preimage, rfl⟩
      rw [FixedPoints.mem_subgroup]
      intro r
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, _hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp (by simpa [R, Nat.card_zpowers] using hxorder)
        let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
        have hrx : rx ≠ 1 := by intro h; exact hx.1 (congrArg Subtype.val h)
        have hrx : r = rx := (huniq r hr).trans (huniq rx hrx).symm
        simpa [hrx, rx, d, hxx] using
          (show x • (preimage⁻¹ * (x • preimage)) = preimage⁻¹ * (x • preimage) by
            simp only [smul_mul', smul_inv', ← mul_smul, hxx, one_smul]
            have hinvself (y : V) : y⁻¹ = y := by
              apply inv_eq_of_mul_eq_one_right
              simpa only [pow_two] using
                Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (IsElementaryAbelian.exponent_dvd_p 2 V) y
            rw [hinvself, hinvself]
            ac_rfl)
  calc
    Nat.card V = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
    _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
    _ = Nat.card (FixedPoints.subgroup R V) * Nat.card (commutatorAction R V) := by rw [hker, hrange]
    _ = Nat.card d.range * Nat.card d.range := by rw [hfixrange, ← hrange]
    _ = Nat.card (commutatorAction R V) ^ 2 := by rw [hrange, pow_two]
