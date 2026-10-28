module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OddOpposition

/-!
# Cartan opposition, independent-root kernels, and the literal Weyl relation

Conjugation identifies each actual root-action kernel with the fixed subgroup
of its Weyl reflection. The perpendicular-root kernel equality then forces
opposition to invert the whole odd Cartan. In the octagon every two distinct
root reflections have a product with a power equal to opposition, proving
trivial common Cartan centralizer for independent roots. The only finite
calculation is the eight-element rotation group, checked by kernel reduction.

For any actual simple lifts, their product's eighth power lies in the Cartan
and is fixed by its fourth power, a lift of opposition. Inversion and oddness
kill this error and prove the relation in N itself. No relation on actual
lifts or native-model identification is an input.

Source: Fong--Seitz I (1973), proof of (6H)(a), p.51; II (1974), end of
section 10, p.232. Opposition gives a uniform argument including the binary
case. The field-dependent perpendicular-kernel input is discharged by the
CFSG ReeSource.Opposition consumer on the same quotient.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem rootAction_kernel_conjugate (i : Fin 2) (w : Weyl Q) :
    (rootAction Q split i w).ker =
      (cartanPanelMap Q i).ker.comap (weylCartanAction Q split w).toMonoidHom := by
  rw [← simpleRootAction_kernel Q split i]
  ext h
  have he := DFunLike.congr_fun
    (RootAction.conjugate_action (Q.tits.B ⊓ Q.tits.N) (simpleRoot Q split i)
      (torus_normalizes_simpleRoot Q split i)
      ⟨representative w,torus_normalizes (representative w)⟩) h
  have hw : weylCartanAction Q split w = normalizerCartanAction Q (representative w) := by
    conv_lhs => rw [← representative_spec w, weylCartanAction_lift]
  change rootAction Q split i w h = 1 ↔
    simpleRootAction Q split i (weylCartanAction Q split w h) = 1
  rw [hw]
  change (MulAut.congr (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)))
    (rootAction Q split i w h) = simpleRootAction Q split i
      (normalizerCartanAction Q (representative w) h) at he
  rw [← he]
  exact ((MulAut.congr (RootAction.conjugateEquiv (simpleRoot Q split i)
    (representative w))).map_eq_one_iff).symm

theorem rootAction_kernel_fixed (i : Fin 2)
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker)
    (w : Weyl Q) (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    h ∈ (rootAction Q split i w).ker ↔
      weylCartanAction Q split (w⁻¹*Q.simple i*w) h = h := by
  rw [rootAction_kernel_conjugate, ← hfix]
  change simpleCartanAction Q split i (weylCartanAction Q split w h) =
    weylCartanAction Q split w h ↔ _
  rw [map_mul, map_mul, map_inv]
  change _ ↔ (weylCartanAction Q split w)⁻¹
    (simpleCartanAction Q split i (weylCartanAction Q split w h)) = h
  exact ((weylCartanAction Q split w).symm_apply_eq).symm

private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem sinv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (ssq Q i)

private theorem longest_eight (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
      Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
  have h0 := alternatingWord_longest Q false
  have h1 := alternatingWord_longest Q true
  rw [hm] at h0 h1
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h0.symm
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h1.symm
  · exact (hij rfl).elim

theorem longest_eq_rotation_four (hm : rotationOrder Q = 8) :
    longest Q = (Q.simple 0*Q.simple 1)^4 := by
  rw [longest_eight Q hm 0 1 (by decide)]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

private theorem longest_comm (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Q.simple i * longest Q = longest Q * Q.simple i := by
  conv_lhs => rw [longest_eight Q hm i j hij]
  conv_rhs => rw [longest_eight Q hm j i hij.symm]
  simp only [mul_assoc, ← mul_assoc (Q.simple i) (Q.simple i), ssq,
    one_mul, mul_one]

private theorem perpendicular_reflection (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    (Q.simple j*Q.simple i*Q.simple j)⁻¹*Q.simple i*
      (Q.simple j*Q.simple i*Q.simple j) = longest Q*Q.simple i := by
  rw [longest_eight Q hm j i hij.symm]
  simp only [mul_inv_rev, sinv, mul_assoc, ssq, mul_one]

/-- Perpendicular source root kernels force opposition to invert the whole Cartan. -/
theorem longestCartanAction_inversion (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker)
    (hperp : (rootAction Q split i (Q.simple j*Q.simple i*Q.simple j)).ker =
      reflectionInverted Q split i) :
    ∀ h, weylCartanAction Q split (longest Q) h = h⁻¹ := by
  let := split.abelian
  apply OddReflection.inversion_of_perpendicular_fixed (simpleCartanAction Q split i)
    (weylCartanAction Q split (longest Q)) (simpleCartanAction_involutive Q split i)
  · intro h
    change ((weylCartanAction Q split (longest Q) *
      weylCartanAction Q split (longest Q)) h) = h
    rw [← map_mul, longest_mul_self, map_one]
    rfl
  · intro h
    change ((weylCartanAction Q split (longest Q) *
      weylCartanAction Q split (Q.simple i)) h) =
      ((weylCartanAction Q split (Q.simple i) *
        weylCartanAction Q split (longest Q)) h)
    rw [← map_mul, ← map_mul, longest_comm Q hm i j hij]
  · exact split.odd
  · intro h
    have he := rootAction_kernel_fixed Q split i hfix (Q.simple j*Q.simple i*Q.simple j) h
    rw [hperp, perpendicular_reflection Q hm i j hij, map_mul] at he
    exact he.symm

/-- Opposition removes the odd-Cartan error from the Weyl relation on any
actual lifts of the two ordered simple classes. -/
theorem reflection_product_eight_of_opposition (hm : rotationOrder Q = 8)
    (hop : ∀ h, weylCartanAction Q split (longest Q) h = h⁻¹)
    (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple 0)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple 1) :
    (a*b)^8 = 1 := by
  let t := a*b
  have ht : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) t =
      Q.simple 0*Q.simple 1 := by rw [map_mul, ha, hb]
  have ht8 : t^8 ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (t^8) = 1
    rw [map_pow, ht, ← hm]
    exact pow_orderOf_eq_one _
  let h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := ⟨t^8, ht8⟩
  have ht4 : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (t^4) =
      longest Q := by rw [map_pow, ht, longest_eq_rotation_four Q hm]
  have hfix : weylCartanAction Q split (longest Q) h = h := by
    rw [← ht4, weylCartanAction_lift]
    apply Subtype.ext
    change ((t : X ⧸ Q.D)^4)*((t : X ⧸ Q.D)^8)*((t : X ⧸ Q.D)^4)⁻¹ = _
    rw [← pow_add, Nat.add_comm 4 8, pow_add, mul_inv_cancel_right]
  have h2 : h^2 = 1 := by
    rw [pow_two]
    exact (congrArg (h * ·) (hfix.symm.trans (hop h))).trans (mul_inv_cancel h)
  have he : h = 1 := split.odd.symm.pow_left_bijective.injective
    (h2.trans (one_pow 2).symm)
  apply Subtype.ext
  change ((t : X ⧸ Q.D)^8) = 1
  exact congrArg (fun c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) => (c : X ⧸ Q.D)) he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

private theorem dihedral_reflection_product {d : ℕ} (hd : d = 8)
    (i j : ZMod d) (hij : i ≠ j) :
    ∃ k : ℕ, (DihedralGroup.sr i * DihedralGroup.sr j)^k = DihedralGroup.r 4 := by
  subst d
  have hc : ∀ a : ZMod 8, a ≠ 0 → ∃ k : Fin 8, a*(k.val : ZMod 8) = 4 := by decide
  obtain ⟨k,hk⟩ := hc (j-i) (sub_ne_zero.mpr hij.symm)
  exact ⟨k, by rw [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow, hk]⟩

open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem reflection_image (i : Fin 2) (w : Weyl Q) :
    ∃ a, weylEquiv Q (w⁻¹*Q.simple i*w) = DihedralGroup.sr a := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> cases hw : weylEquiv Q w with
  | r a => simp [map_mul, map_inv, hw]
  | sr a => simp [map_mul, map_inv, hw]

/-- Distinct root reflections in the octagon generate its central rotation. -/
theorem independent_reflection_product (hm : rotationOrder Q = 8)
    (i j : Fin 2) (w v : Weyl Q)
    (hne : w⁻¹*Q.simple i*w ≠ v⁻¹*Q.simple j*v) :
    ∃ k : ℕ, ((w⁻¹*Q.simple i*w)*(v⁻¹*Q.simple j*v))^k = longest Q := by
  obtain ⟨a,ha⟩ := reflection_image Q i w
  obtain ⟨b,hb⟩ := reflection_image Q j v
  have hab : a ≠ b := by
    intro he
    apply hne
    apply (weylEquiv Q).injective
    rw [ha,hb,he]
  obtain ⟨k,hk⟩ := dihedral_reflection_product hm a b hab
  refine ⟨k,(weylEquiv Q).injective ?_⟩
  rw [map_pow,map_mul,ha,hb,hk,longest_eq_rotation_four Q hm,map_pow,map_mul,
    weylEquiv_simple_zero,weylEquiv_simple_one]
  simp only [DihedralGroup.sr_mul_sr,sub_zero,DihedralGroup.r_pow,one_mul,Nat.cast_ofNat]

theorem independent_rootAction_kernels (hm : rotationOrder Q = 8)
    (hfix : ∀ i, reflectionFixed Q split i = (cartanPanelMap Q i).ker)
    (hop : ∀ h, weylCartanAction Q split (longest Q) h = h⁻¹)
    (i j : Fin 2) (w v : Weyl Q)
    (hne : w⁻¹*Q.simple i*w ≠ v⁻¹*Q.simple j*v) :
    (rootAction Q split i w).ker ⊓ (rootAction Q split j v).ker = ⊥ := by
  apply eq_bot_iff.mpr
  intro h hh
  have hi := (rootAction_kernel_fixed Q split i (hfix i) w h).mp hh.1
  have hj := (rootAction_kernel_fixed Q split j (hfix j) v h).mp hh.2
  obtain ⟨k,hk⟩ := independent_reflection_product Q hm i j w v hne
  have hprod : weylCartanAction Q split ((w⁻¹*Q.simple i*w)*(v⁻¹*Q.simple j*v)) h = h := by
    rw [map_mul,MulAut.mul_apply,hj,hi]
  have hp (n : ℕ) :
      weylCartanAction Q split (((w⁻¹*Q.simple i*w)*(v⁻¹*Q.simple j*v))^n) h = h := by
    induction n with
    | zero => simp only [pow_zero,map_one,MulAut.one_apply]
    | succ n ih => rw [pow_succ,map_mul,MulAut.mul_apply,hprod,ih]
  have hlong := hp k
  rw [hk,hop] at hlong
  have h2 : h^2 = 1 := by
    rw [pow_two]
    exact (congrArg (h * ·) hlong.symm).trans (mul_inv_cancel h)
  exact split.odd.symm.pow_left_bijective.injective (h2.trans (one_pow 2).symm)

/-- The actual common Cartan centralizer of any two independent roots is trivial. -/
theorem independent_root_centralizer_eq_bot (hm : rotationOrder Q = 8)
    (hfix : ∀ i, reflectionFixed Q split i = (cartanPanelMap Q i).ker)
    (hop : ∀ h, weylCartanAction Q split (longest Q) h = h⁻¹)
    (i j : Fin 2) (w v : Weyl Q)
    (hne : w⁻¹*Q.simple i*w ≠ v⁻¹*Q.simple j*v) :
    (((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) ⊓
      centralizer (rootAt Q split j v : Set (X ⧸ Q.D))) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  let h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := ⟨x,hx.1.1⟩
  have hh : h ∈ (rootAction Q split i w).ker ⊓ (rootAction Q split j v).ker := by
    change h ∈ (RootAction.action _ _ _).ker ⊓ (RootAction.action _ _ _).ker
    rw [RootAction.action_kernel,RootAction.action_kernel]
    exact ⟨hx.1.2,hx.2⟩
  rw [independent_rootAction_kernels Q split hm hfix hop i j w v hne] at hh
  exact congrArg Subtype.val (mem_bot.mp hh)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
