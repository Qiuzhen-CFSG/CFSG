module
public import Theory.GroupTheory.QuaternionSwapModel
public import Theory.GroupTheory.SpecificGroups.QuaternionEightResidual.Permutation
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Product.CubicGeneration
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The intrinsic quaternion-swap parabolic

The diagonal action of a point stabilizer S₃ ≤ Aut(Q₈) ≃ S₄ on the
quaternion wreath product fixes its diagonal center and the factor swap.
It therefore descends to QH and defines the actual semidirect product
H0 = QH ⋊ S₃. The embedding and both quaternion coordinate maps are retained.

The two-core calculation uses the quotient H0 → S₃. A nontrivial cubic
automorphism generates each quaternion factor by its differences; the
corresponding complement element lies in the intrinsic two-residual.

Source: Aschbacher–Smith, proof of Lemma 14.2.21, printed p.988
(PDF p.1005), refs/quasithin.pdf. Comparison with the concrete Aut(M₁₂)
compatible pair belongs to the source-model assembly.
-/

@[expose] public section
namespace QuaternionSwapModel
abbrev S3 := Equiv.Perm (Fin 3)
abbrev S4 := Equiv.Perm (Fin 4)

def permThreeLift : S3 →* S4 :=
  ((finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4).permCongrHom).toMonoidHom.comp
    ({ toFun := fun σ : S3 => Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) σ
       map_one' := by apply Equiv.ext; intro x; rcases x with _|x <;> simp
       map_mul' := by intro a b; apply Equiv.ext; intro x; rcases x with _|x <;> simp } :
      S3 →* Equiv.Perm (Fin 1 ⊕ Fin 3))

noncomputable def q8PermAction : S3 →* MulAut (QuaternionGroup 2) :=
  QuaternionGroup.Residual.autEquivPerm.symm.toMonoidHom.comp permThreeLift

noncomputable def rawAut (e : MulAut (QuaternionGroup 2)) : MulAut Raw where
  toFun w := ⟨fun t => e (w.left t), w.right⟩
  invFun w := ⟨fun t => e.symm (w.left t), w.right⟩
  left_inv w := by
    apply RegularWreathProduct.ext
    · funext t; simp
    · rfl
  right_inv w := by
    apply RegularWreathProduct.ext
    · funext t; simp
    · rfl
  map_mul' x y := by
    apply RegularWreathProduct.ext
    · funext t
      simp [RegularWreathProduct.mul_left]
    · rfl

noncomputable def rawAutHom : MulAut (QuaternionGroup 2) →* MulAut Raw where
  toFun := rawAut
  map_one' := by
    apply MulEquiv.ext
    intro w
    apply RegularWreathProduct.ext
    · funext t; simp [rawAut]
    · simp [rawAut]
  map_mul' e f := by
    apply MulEquiv.ext
    intro w
    apply RegularWreathProduct.ext
    · funext t; simp [rawAut]
    · rfl

theorem rawAut_killed (e : MulAut (QuaternionGroup 2)) : rawAut e killed = killed := by
  apply RegularWreathProduct.ext
  · funext t
    change e (QuaternionGroup.a 2) = QuaternionGroup.a 2
    have hne : (e (QuaternionGroup.a 1 : QuaternionGroup 2)) ^ 2 ≠ 1 := by
      intro h
      have hi : (QuaternionGroup.a 1 : QuaternionGroup 2)^2 ≠ 1 := by decide
      apply hi
      apply e.injective
      simpa only [map_pow, map_one] using h
    have hsq : (e (QuaternionGroup.a 1 : QuaternionGroup 2)) ^ 2 = QuaternionGroup.a 2 := by
      have hh : ∀ q : QuaternionGroup 2, q ^ 2 ≠ 1 → q ^ 2 = QuaternionGroup.a 2 := by decide
      exact hh _ hne
    calc
      e (QuaternionGroup.a 2) = e ((QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2) := by
        exact congrArg e (QuaternionGroup.a_one_pow 2).symm
      _ = (e (QuaternionGroup.a 1)) ^ 2 := map_pow e _ _
      _ = QuaternionGroup.a 2 := hsq
  · rfl

noncomputable def qhAut (e : MulAut (QuaternionGroup 2)) : MulAut QH :=
  QuotientGroup.congr diagonalCenter diagonalCenter (rawAut e) (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · change rawAut e 1 ∈ diagonalCenter
        rw [map_one]
        exact diagonalCenter.one_mem
      · change rawAut e killed ∈ diagonalCenter
        rw [rawAut_killed]
        exact show killed ∈ diagonalCenter from Or.inr rfl
    · intro x hx
      rcases hx with rfl | rfl
      · change 1 ∈ Subgroup.map (rawAut e).toMonoidHom diagonalCenter
        refine ⟨1, diagonalCenter.one_mem, ?_⟩
        simp
      · refine ⟨killed, (show killed ∈ diagonalCenter from Or.inr rfl), ?_⟩
        change rawAut e killed = killed
        exact rawAut_killed e)

noncomputable def qhAutHom : MulAut (QuaternionGroup 2) →* MulAut QH where
  toFun := qhAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
    rfl
  map_mul' e f := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
    rfl

noncomputable def s3Action : S3 →* MulAut QH := qhAutHom.comp q8PermAction



theorem qhAut_left (e : MulAut (QuaternionGroup 2)) (q : QuaternionGroup 2) :
    qhAut e (leftEmbedding q) = leftEmbedding (e q) := by
  change qhAut e (projection (leftRaw q)) = projection (leftRaw (e q))
  unfold qhAut
  change (QuotientGroup.congr diagonalCenter diagonalCenter (rawAut e) _)
      (QuotientGroup.mk' diagonalCenter (leftRaw q)) = _
  rw [QuotientGroup.congr_mk']
  apply congrArg projection
  apply RegularWreathProduct.ext
  · funext t
    by_cases ht : t = 1 <;> simp [rawAut, leftRaw, ht]
  · rfl
theorem qhAut_right (e : MulAut (QuaternionGroup 2)) (q : QuaternionGroup 2) :
    qhAut e (rightEmbedding q) = rightEmbedding (e q) := by
  change qhAut e (projection (rightRaw q)) = projection (rightRaw (e q))
  unfold qhAut
  change (QuotientGroup.congr diagonalCenter diagonalCenter (rawAut e) _)
      (QuotientGroup.mk' diagonalCenter (rightRaw q)) = _
  rw [QuotientGroup.congr_mk']
  apply congrArg projection
  apply RegularWreathProduct.ext
  · funext t
    by_cases ht : t = turn <;> simp [rawAut, rightRaw, ht]
  · rfl
theorem qhAut_swap (e : MulAut (QuaternionGroup 2)) : qhAut e swap = swap := by
  change qhAut e (projection swapRaw) = projection swapRaw
  unfold qhAut
  change (QuotientGroup.congr diagonalCenter diagonalCenter (rawAut e) _)
      (QuotientGroup.mk' diagonalCenter swapRaw) = _
  rw [QuotientGroup.congr_mk']
  apply congrArg projection
  apply RegularWreathProduct.ext
  · funext t; simp [rawAut, swapRaw]
  · rfl
theorem qhAut_diag (e : MulAut (QuaternionGroup 2)) (q : QuaternionGroup 2) :
    qhAut e (projection (diagonalRaw q)) = projection (diagonalRaw (e q)) := by
  unfold qhAut
  change (QuotientGroup.congr diagonalCenter diagonalCenter (rawAut e) _)
      (QuotientGroup.mk' diagonalCenter (diagonalRaw q)) = _
  rw [QuotientGroup.congr_mk']
  apply congrArg projection
  apply RegularWreathProduct.ext
  · funext t; simp [rawAut, diagonalRaw]
  · rfl


abbrev H0 := QH ⋊[s3Action] S3
instance : Finite H0 := Finite.of_equiv (QH × S3) SemidirectProduct.equivProd.symm
noncomputable def i : QH →* H0 := SemidirectProduct.inl
noncomputable def π : H0 →* S3 := SemidirectProduct.rightHom

theorem π_surj : Function.Surjective π := SemidirectProduct.rightHom_surjective

theorem qh_isPGroup : IsPGroup 2 QH := by
  apply IsPGroup.of_card (n := 6)
  rw [card_QH]
  norm_num

theorem i_range_eq_ker : i.range = π.ker := SemidirectProduct.range_inl_eq_ker_rightHom

theorem pcore_eq_i_range : pCore 2 H0 = i.range := by
  have hker : IsPGroup 2 π.ker := by
    rw [← i_range_eq_ker]
    exact qh_isPGroup.of_equiv (MonoidHom.ofInjective (f := i)
      SemidirectProduct.inl_injective)
  exact (ker_eq_twoCore_of_surjective_perm_three π π_surj hker).symm.trans
    i_range_eq_ker.symm


def cubic : S3 := Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2

theorem cubic_pow : cubic ^ 3 = 1 := by decide +kernel
theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel
theorem cubic_lift_ne_one : permThreeLift cubic ≠ 1 := by
  intro h
  have h1 : permThreeLift cubic (1 : Fin 4) = 1 := congrArg (fun p : S4 => p (1 : Fin 4)) h
  have hcontra : permThreeLift cubic (1 : Fin 4) ≠ 1 := by decide +kernel
  exact hcontra h1
theorem q8Action_cubic_pow : q8PermAction cubic ^ 3 = 1 := by
  rw [← map_pow, cubic_pow, map_one]
theorem q8Action_cubic_ne_one : q8PermAction cubic ≠ 1 := by
  intro h
  apply cubic_lift_ne_one
  apply QuaternionGroup.Residual.autEquivPerm.symm.injective
  simpa [q8PermAction] using h
theorem s3Action_cubic_pow : s3Action cubic ^ 3 = 1 := by
  rw [← map_pow, cubic_pow, map_one]
theorem s3Action_cubic_ne_one : s3Action cubic ≠ 1 := by
  intro h
  have heq : qhAut (q8PermAction cubic) = 1 := by
    simpa [s3Action, qhAutHom] using h
  have he : q8PermAction cubic = 1 := by
    ext q
    apply leftEmbedding_injective
    have hh := congrArg (fun f : MulAut QH => f (leftEmbedding q)) heq
    simpa [qhAut_left] using hh
  exact q8Action_cubic_ne_one he
theorem s3Action_left (a : S3) (q : QuaternionGroup 2) :
    s3Action a (leftEmbedding q) = leftEmbedding (q8PermAction a q) := by
  exact qhAut_left _ _
theorem s3Action_right (a : S3) (q : QuaternionGroup 2) :
    s3Action a (rightEmbedding q) = rightEmbedding (q8PermAction a q) := by
  exact qhAut_right _ _
theorem s3Action_swap (a : S3) : s3Action a swap = swap := by
  exact qhAut_swap _


theorem card_H0 : Nat.card H0 = 384 := by
  rw [SemidirectProduct.card, card_QH]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem qhAut_mem_A (e : MulAut (QuaternionGroup 2)) (x : QH) (hx : x ∈ A) :
    qhAut e x ∈ A := by
  have he2 : e (QuaternionGroup.a 2 : QuaternionGroup 2) = QuaternionGroup.a 2 := by
    have hne : (e (QuaternionGroup.a 1 : QuaternionGroup 2)) ^ 2 ≠ 1 := by
      intro h
      have hi : (QuaternionGroup.a 1 : QuaternionGroup 2)^2 ≠ 1 := by decide
      apply hi
      apply e.injective
      simpa only [map_pow, map_one] using h
    have hsq : (e (QuaternionGroup.a 1 : QuaternionGroup 2)) ^ 2 = QuaternionGroup.a 2 := by
      have hh : ∀ q : QuaternionGroup 2, q ^ 2 ≠ 1 → q ^ 2 = QuaternionGroup.a 2 := by decide
      exact hh _ hne
    calc
      e (QuaternionGroup.a 2) = e ((QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2) := by
        exact congrArg e (QuaternionGroup.a_one_pow 2).symm
      _ = (e (QuaternionGroup.a 1)) ^ 2 := map_pow e _ _
      _ = QuaternionGroup.a 2 := hsq
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  change quaternionQuotient (e (r.left 1)) = quaternionQuotient (e (r.left turn))
  change quaternionQuotient (r.left 1) = quaternionQuotient (r.left turn) at hx
  have hrel : ∀ q r : QuaternionGroup 2,
      quaternionQuotient q = quaternionQuotient r →
        q⁻¹ * r = 1 ∨ q⁻¹ * r = QuaternionGroup.a 2 := by decide +kernel
  have hrel2 : ∀ q r : QuaternionGroup 2,
      q⁻¹ * r = 1 ∨ q⁻¹ * r = QuaternionGroup.a 2 →
        quaternionQuotient q = quaternionQuotient r := by decide +kernel
  rcases hrel _ _ hx with h | h
  · apply hrel2
    left
    simpa only [map_inv, map_mul, map_one] using congrArg e h
  · apply hrel2
    right
    simpa only [map_inv, map_mul, he2] using congrArg e h


theorem s3Action_mem_A (a : S3) (x : QH) (hx : x ∈ A) : s3Action a x ∈ A :=
  qhAut_mem_A _ _ hx

theorem map_i_normal_of_invariant (K : Subgroup QH) [K.Normal]
    (hinv : ∀ a : S3, ∀ x : QH, x ∈ K → s3Action a x ∈ K) :
    (K.map i).Normal := by
  constructor
  intro g hg y
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
  rw [← SemidirectProduct.inl_left_mul_inr_right y]
  let k' := y.left * s3Action y.right k * y.left⁻¹
  have hk' : k' ∈ K := by
    dsimp [k']
    exact (inferInstance : K.Normal).conj_mem (s3Action y.right k) (hinv y.right k hk) y.left
  refine ⟨k', hk', ?_⟩
  calc
    i k' = i y.left * i (s3Action y.right k) * i y.left⁻¹ := by
      simp [k', map_mul]
    _ = i y.left * (SemidirectProduct.inr y.right * i k * (SemidirectProduct.inr y.right)⁻¹) * i y.left⁻¹ := by
      simp only [i]
      rw [SemidirectProduct.inl_aut]
      rw [← map_inv (SemidirectProduct.inr : S3 →* H0) y.right]
    _ = (SemidirectProduct.inl y.left * SemidirectProduct.inr y.right) * i k *
        (SemidirectProduct.inl y.left * SemidirectProduct.inr y.right)⁻¹ := by
      simp only [i, map_inv]
      group

theorem A_map_i_normal : (A.map i).Normal :=
  map_i_normal_of_invariant A s3Action_mem_A


theorem i_inj : Function.Injective i := SemidirectProduct.inl_injective

theorem inr_conj_i (a : S3) (x : QH) :
    (SemidirectProduct.inr a : H0) * i x * (SemidirectProduct.inr a)⁻¹ = i (s3Action a x) := by
  change (SemidirectProduct.inr a : H0) * SemidirectProduct.inl x *
      (SemidirectProduct.inr a)⁻¹ = SemidirectProduct.inl (s3Action a x)
  simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := s3Action) a x).symm

theorem inr_cubic_mem_residual : (SemidirectProduct.inr cubic : H0) ∈ pResidual 2 H0 := by
  apply Subgroup.mem_pResidual_of_orderOf_coprime
  have hpow : (SemidirectProduct.inr cubic : H0) ^ 3 = 1 := by rw [← map_pow, cubic_pow, map_one]
  have hd : orderOf (SemidirectProduct.inr cubic : H0) ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
  exact Nat.Coprime.of_dvd_right hd (by decide : Nat.Coprime 2 3)

theorem qk_le_commutator : QK.map i ≤ ⁅i.range, pResidual 2 H0⁆ := by
  rw [QK, Subgroup.map_sup]
  apply sup_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    obtain ⟨u, v, hq⟩ := QuaternionGroup.eq_mul_cubic_differences_two
      (q8PermAction cubic) q8Action_cubic_pow q8Action_cubic_ne_one q
    rw [hq, map_mul, map_mul]
    apply Subgroup.mul_mem
    · have hmem := Subgroup.commutator_mem_commutator
        (show i (leftEmbedding u)⁻¹ ∈ i.range by exact ⟨(leftEmbedding u)⁻¹, by simp⟩)
        inr_cubic_mem_residual
      have he : i ((leftEmbedding u)⁻¹) * (SemidirectProduct.inr cubic : H0) *
          (i ((leftEmbedding u)⁻¹))⁻¹ * (SemidirectProduct.inr cubic : H0)⁻¹ =
          i (leftEmbedding (u⁻¹ * q8PermAction cubic u)) := by
        simp only [map_inv, inv_inv]
        calc
          (i (leftEmbedding u))⁻¹ * (SemidirectProduct.inr cubic : H0) *
              i (leftEmbedding u) * (SemidirectProduct.inr cubic : H0)⁻¹ =
              (i (leftEmbedding u))⁻¹ *
                ((SemidirectProduct.inr cubic : H0) * i (leftEmbedding u) *
                  (SemidirectProduct.inr cubic : H0)⁻¹) := by group
          _ = (i (leftEmbedding u))⁻¹ * i (s3Action cubic (leftEmbedding u)) := by
            rw [inr_conj_i]
          _ = i (leftEmbedding (u⁻¹ * q8PermAction cubic u)) := by
            rw [s3Action_left]
            rw [← map_inv i, ← leftEmbedding.map_inv, ← map_mul i, ← leftEmbedding.map_mul]
      rw [commutatorElement_def, he] at hmem
      exact hmem
    · have hmem := Subgroup.commutator_mem_commutator
        (show i (leftEmbedding v)⁻¹ ∈ i.range by exact ⟨(leftEmbedding v)⁻¹, by simp⟩)
        inr_cubic_mem_residual
      have he : i ((leftEmbedding v)⁻¹) * (SemidirectProduct.inr cubic : H0) *
          (i ((leftEmbedding v)⁻¹))⁻¹ * (SemidirectProduct.inr cubic : H0)⁻¹ =
          i (leftEmbedding (v⁻¹ * q8PermAction cubic v)) := by
        simp only [map_inv, inv_inv]
        calc
          (i (leftEmbedding v))⁻¹ * (SemidirectProduct.inr cubic : H0) *
              i (leftEmbedding v) * (SemidirectProduct.inr cubic : H0)⁻¹ =
              (i (leftEmbedding v))⁻¹ *
                ((SemidirectProduct.inr cubic : H0) * i (leftEmbedding v) *
                  (SemidirectProduct.inr cubic : H0)⁻¹) := by group
          _ = (i (leftEmbedding v))⁻¹ * i (s3Action cubic (leftEmbedding v)) := by
            rw [inr_conj_i]
          _ = i (leftEmbedding (v⁻¹ * q8PermAction cubic v)) := by
            rw [s3Action_left]
            rw [← map_inv i, ← leftEmbedding.map_inv, ← map_mul i, ← leftEmbedding.map_mul]
      rw [commutatorElement_def, he] at hmem
      exact hmem
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    obtain ⟨u, v, hq⟩ := QuaternionGroup.eq_mul_cubic_differences_two
      (q8PermAction cubic) q8Action_cubic_pow q8Action_cubic_ne_one q
    rw [hq, map_mul, map_mul]
    apply Subgroup.mul_mem
    · have hmem := Subgroup.commutator_mem_commutator
        (show i (rightEmbedding u)⁻¹ ∈ i.range by exact ⟨(rightEmbedding u)⁻¹, by simp⟩)
        inr_cubic_mem_residual
      have he : i ((rightEmbedding u)⁻¹) * (SemidirectProduct.inr cubic : H0) *
          (i ((rightEmbedding u)⁻¹))⁻¹ * (SemidirectProduct.inr cubic : H0)⁻¹ =
          i (rightEmbedding (u⁻¹ * q8PermAction cubic u)) := by
        simp only [map_inv, inv_inv]
        calc
          (i (rightEmbedding u))⁻¹ * (SemidirectProduct.inr cubic : H0) *
              i (rightEmbedding u) * (SemidirectProduct.inr cubic : H0)⁻¹ =
              (i (rightEmbedding u))⁻¹ *
                ((SemidirectProduct.inr cubic : H0) * i (rightEmbedding u) *
                  (SemidirectProduct.inr cubic : H0)⁻¹) := by group
          _ = (i (rightEmbedding u))⁻¹ * i (s3Action cubic (rightEmbedding u)) := by
            rw [inr_conj_i]
          _ = i (rightEmbedding (u⁻¹ * q8PermAction cubic u)) := by
            rw [s3Action_right]
            rw [← map_inv i, ← rightEmbedding.map_inv, ← map_mul i, ← rightEmbedding.map_mul]
      rw [commutatorElement_def, he] at hmem
      exact hmem
    · have hmem := Subgroup.commutator_mem_commutator
        (show i (rightEmbedding v)⁻¹ ∈ i.range by exact ⟨(rightEmbedding v)⁻¹, by simp⟩)
        inr_cubic_mem_residual
      have he : i ((rightEmbedding v)⁻¹) * (SemidirectProduct.inr cubic : H0) *
          (i ((rightEmbedding v)⁻¹))⁻¹ * (SemidirectProduct.inr cubic : H0)⁻¹ =
          i (rightEmbedding (v⁻¹ * q8PermAction cubic v)) := by
        simp only [map_inv, inv_inv]
        calc
          (i (rightEmbedding v))⁻¹ * (SemidirectProduct.inr cubic : H0) *
              i (rightEmbedding v) * (SemidirectProduct.inr cubic : H0)⁻¹ =
              (i (rightEmbedding v))⁻¹ *
                ((SemidirectProduct.inr cubic : H0) * i (rightEmbedding v) *
                  (SemidirectProduct.inr cubic : H0)⁻¹) := by group
          _ = (i (rightEmbedding v))⁻¹ * i (s3Action cubic (rightEmbedding v)) := by
            rw [inr_conj_i]
          _ = i (rightEmbedding (v⁻¹ * q8PermAction cubic v)) := by
            rw [s3Action_right]
            rw [← map_inv i, ← rightEmbedding.map_inv, ← map_mul i, ← rightEmbedding.map_mul]
      rw [commutatorElement_def, he] at hmem
      exact hmem

open scoped commutatorElement

def parity : QH →* C2 := RegularWreathProduct.rightHom.comp wreathMap

theorem parity_qhAut (e : MulAut (QuaternionGroup 2)) (x : QH) :
    parity (qhAut e x) = parity x := by
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  rfl

noncomputable def parabolicParity : H0 →* C2 where
  toFun h := parity h.left
  map_one' := map_one parity
  map_mul' x y := by
    change parity (x.left * s3Action x.right y.left) = _
    rw [map_mul, show parity (s3Action x.right y.left) = parity y.left from parity_qhAut _ _]

theorem parabolicParity_i (x : QH) : parabolicParity (i x) = parity x := rfl

theorem pi_i (x : QH) : π (i x) = 1 := rfl

theorem commutator_le_qk : ⁅i.range, (⊤ : Subgroup H0)⁆ ≤ QK.map i := by
  apply Subgroup.commutator_le.mpr
  rintro a ⟨q,rfl⟩ b _
  have hpi : π ⁅i q,b⁆ = 1 := by
    simp only [commutatorElement_def, map_mul, map_inv, pi_i]
    group
  have hrange : ⁅i q,b⁆ ∈ i.range := by rw [i_range_eq_ker]; exact hpi
  obtain ⟨r,hr⟩ := hrange
  refine ⟨r, ?_, hr⟩
  rw [QK_eq_comap_base]
  change parity r = 1
  rw [← parabolicParity_i, hr]
  simp only [commutatorElement_def, map_mul, map_inv]
  simp only [mul_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem commutator_residual_eq_qk : ⁅i.range, pResidual 2 H0⁆ = QK.map i := by
  apply le_antisymm
  · exact (Subgroup.commutator_mono le_rfl le_top).trans commutator_le_qk
  · exact qk_le_commutator

end QuaternionSwapModel
