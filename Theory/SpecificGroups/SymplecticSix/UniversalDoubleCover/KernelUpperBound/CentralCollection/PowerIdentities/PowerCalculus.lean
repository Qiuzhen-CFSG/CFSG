module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.Inputs


/-!
# Cyclic consequences and powers of central word equations

An equation u = v c, with c a central relator product, gives the central
word u v⁻¹. The inverse-word correction records every occurrence of a,
since a⁻¹ is represented by a c₀⁻¹. Cyclic splitting of this derived word
can therefore reuse the existing seed calculus. Taking powers multiplies
the central exponent vector by the same natural number.

These two operations supply the missing zero-exponent power identity in
F/[F,R]. Source: Wilson–Nickerson–Bray, ATLAS `S62G1-P1.M`;
see `PowerIdentities/source/README.md` for the certificate and conventions.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay

theorem eqn_relator {g : Fin 3 → Central}
    (hi : ∀ i, g (inverseLetter i) = (g i)⁻¹ * (centralRelator 0 : Central) ^
      (if i = 0 then 1 else 0 : ℕ))
    {u v : List (Fin 3)} {z : Fin 7 → ℤ} (h : Eqn g u v z) :
    Eqn g (u ++ inverseWord v) [] (z + zeroCoordinate (countA v)) := by
  dsimp only [Eqn] at h ⊢
  rw [readWord_nil, one_mul, readWord_append, readWord_inverse g _ hi, h,
    collect_add, collect_zeroCoordinate]
  have hc : (collect z : Central) * (readWord g v)⁻¹ =
      (readWord g v)⁻¹ * (collect z : Central) :=
    (Subgroup.mem_center_iff.mp (collect z).property _).symm
  simp only [Subgroup.coe_mul, zpow_natCast, Subgroup.coe_pow]
  rw [mul_assoc, ← mul_assoc (collect z : Central), hc]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

def repeatWord (w : List (Fin 3)) (n : ℕ) : List (Fin 3) := (List.replicate n w).flatten

theorem readWord_repeat {G : Type*} [Group G] (g : Fin 3 → G)
    (w : List (Fin 3)) (n : ℕ) : readWord g (repeatWord w n) = readWord g w ^ n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
    change readWord g (w ++ repeatWord w n) = _
    rw [readWord_append, ih, pow_succ']

theorem collect_nsmul (n : ℕ) (z : Fin 7 → ℤ) : collect (n • z) = collect z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, collect_add, ih, pow_succ]

theorem eqn_power {g : Fin 3 → Central} {u v : List (Fin 3)} {z : Fin 7 → ℤ}
    (h : Eqn g u v z) (n : ℕ) : Eqn g (repeatWord u n) (repeatWord v n) (n • z) := by
  dsimp only [Eqn] at h ⊢
  rw [readWord_repeat, readWord_repeat, h, collect_nsmul]
  exact (show Commute (readWord g v) (collect z : Central) from
    Subgroup.mem_center_iff.mp (collect z).property _).mul_pow n

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
