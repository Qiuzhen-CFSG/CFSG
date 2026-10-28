module

public import Theory.SpecificGroups.ReeG2.DefiningLocalRank
public import Theory.SpecificGroups.SL2.DefiningRank

/-!
# The involution-centralizing C₂ × PSL₂ subgroup of the small Ree model

In the actual seven-dimensional Ree basis, SL₂ acts as the direct sum of
its tensor product with its theta twist (coordinates 0, 2, 4, 6) and the
symmetric square of its theta twist (coordinates 1, 3, 5), with the signs
specified below. Upper transvections map to `beta m b` with the same
parameter b, and the Weyl matrix maps to `upsilon`. Transvection generation
therefore places the entire image in the actual generated Ree subgroup.

Three entries in the symmetric-square block detect the SL₂ center. They
prove the exact quotient kernel, and also show that the torus involution
h(−1) is outside the projective image: its symmetric-square block is the
identity, whereas it acts as minus identity on the tensor block. The two
commuting, independent factors give the injective product homomorphism.
The final theorem applies the projective-product local rank theorem to it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of Lemma A.2.17, printed p.38. The generator
conventions are those of the imported ATLAS adaptations; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. The construction also
works in the full model at m=0; no assertion about its derived subgroup is
made here.
-/

@[expose] public section

open Matrix
noncomputable section
namespace Atlas.ReeG2.InvolutionProduct
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Twisted tensor square and symmetric square, in the actual Ree basis. -/
def matrix (m : ℕ) (g : SpecialLinearGroup (Fin 2) F) : Mat F :=
  let a := g 0 0; let b := g 0 1; let c := g 1 0; let d := g 1 1
  let A := theta F m a; let B := theta F m b
  let C := theta F m c; let D := theta F m d
  !![a*A, 0, -(a*B), 0, -(b*A), 0, -(b*B);
     0, A^2, 0, -2*A*B, 0, -(B^2), 0;
     -(a*C), 0, a*D, 0, b*C, 0, b*D;
     0, -(A*C), 0, A*D+B*C, 0, B*D, 0;
     -(c*A), 0, c*B, 0, d*A, 0, d*B;
     0, -(C^2), 0, 2*C*D, 0, D^2, 0;
     -(c*C), 0, c*D, 0, d*C, 0, d*D]

private lemma matrix_one (m : ℕ) : matrix (F := F) m 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix, -theta_apply]

private lemma matrix_mul (m : ℕ) (g h : SpecialLinearGroup (Fin 2) F) :
    matrix m (g*h) = matrix m g * matrix m h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_succ, map_add, map_mul, -theta_apply] <;> ring

/-- The seven-dimensional representation with the actual Ree generator conventions. -/
noncomputable def representation (m : ℕ) : SpecialLinearGroup (Fin 2) F →* Ambient F where
  toFun g :=
    { val := matrix m g
      inv := matrix m g⁻¹
      val_inv := by rw [← matrix_mul, mul_inv_cancel, matrix_one]
      inv_val := by rw [← matrix_mul, inv_mul_cancel, matrix_one] }
  map_one' := by exact Units.ext (matrix_one m)
  map_mul' g h := by exact Units.ext (matrix_mul m g h)

/-- The positive SL₂ root maps to beta without changing its field parameter. -/
lemma representation_upper (m : ℕ) (b : F) :
    representation m (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) b) =
      beta m b := by
  have htwo : (-2 : F) = 1 := by
    have hthree : (3 : F) = 0 := CharP.cast_eq_zero F 3
    linear_combination -hthree
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [representation, matrix, beta_val, betaMatrix, SpecialLinearGroup.transvection_coe,
      htwo, -theta_apply]
  exact mul_comm _ _

/-- The SL₂ Weyl matrix whose image is the actual Ree Weyl involution. -/
noncomputable def weyl : SpecialLinearGroup (Fin 2) F := ⟨!![0,1;-1,0], by simp⟩

/-- The seven-dimensional Weyl image is exactly upsilon. -/
lemma representation_weyl (m : ℕ) : representation (F := F) m weyl = upsilon := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [representation, matrix, weyl, upsilon, upsilonMatrix, -theta_apply]

private lemma representation_mem (m : ℕ) (g : SpecialLinearGroup (Fin 2) F) :
    representation m g ∈ generated F m := by
  have hu (b : F) : representation m
      (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) b) ∈
        generated F m := by
    rw [representation_upper]
    exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨b,rfl⟩))))
  have hw : representation (F := F) m weyl ∈ generated F m := by
    rw [representation_weyl]
    exact Subgroup.subset_closure (Or.inr rfl)
  apply Matrix.SL2.transvection_induction
    (fun g => representation m g ∈ generated F m) ?_ ?_ g
  · intro i j hij b
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu b
    · have he : SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) b =
          weyl * SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (-b) *
            weyl⁻¹ := by
        apply Subtype.ext
        simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [weyl, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.adjugate_fin_two, Matrix.vecMul, dotProduct]
      rw [he, map_mul, map_mul, map_inv]
      exact (generated F m).mul_mem ((generated F m).mul_mem hw (hu (-b)))
        ((generated F m).inv_mem hw)
    · exact (hij rfl).elim
  · intro a b ha hb
    rw [map_mul]
    exact (generated F m).mul_mem ha hb

/-- The SL₂ representation, with its image proved to lie in the generated Ree group. -/
noncomputable def specialLinearHom (m : ℕ) : SpecialLinearGroup (Fin 2) F →* Model F m :=
  (representation m).codRestrict _ (by exact representation_mem m)

private lemma central_of_entries (m : ℕ) (g : SpecialLinearGroup (Fin 2) F)
    (ha : (theta F m (g 0 0))^2 = 1)
    (hb : (theta F m (g 0 1))^2 = 0)
    (hc : (theta F m (g 1 0))^2 = 0) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  have ha' : (g 0 0)^2 = 1 := (theta F m).injective (by simpa only [map_pow, map_one] using ha)
  have hb' : g 0 1 = 0 := (theta F m).injective (by simpa using (eq_zero_of_pow_eq_zero hb))
  have hc' : g 1 0 = 0 := (theta F m).injective (by simpa using (eq_zero_of_pow_eq_zero hc))
  have hd : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two] at h
    simpa only [hb', hc', zero_mul, sub_zero] using h
  have ha0 : g 0 0 ≠ 0 := by intro h; simp [h] at ha'
  have hd' : g 1 1 = g 0 0 := mul_left_cancel₀ ha0 (hd.trans (by simpa [pow_two] using ha'.symm))
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨g 0 0, by simpa using ha', ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb', hc', hd']

/-- The exact kernel is the full SL₂ center, so the representation factors faithfully through PSL₂. -/
lemma specialLinearHom_ker (m : ℕ) :
    (specialLinearHom (F := F) m).ker = Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  ext g
  change specialLinearHom m g = 1 ↔ g ∈ Subgroup.center _
  constructor
  · intro h
    have he : matrix m g = 1 := congrArg (fun x : Model F m => x.val.val) h
    apply central_of_entries m g
    · exact congrArg (fun M : Mat F => M 1 1) he
    · have h' := congrArg (fun M : Mat F => M 1 5) he
      simpa [matrix] using h'
    · have h' := congrArg (fun M : Mat F => M 5 1) he
      simpa [matrix] using h'
  · intro h
    obtain ⟨r, hr, hg⟩ := SpecialLinearGroup.mem_center_iff.mp h
    have hr' : r^2 = 1 := by simpa using hr
    have hentry (i j : Fin 2) : g i j = Matrix.scalar (Fin 2) r i j :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hg.symm
    apply Subtype.ext
    apply Units.ext
    change matrix m g = 1
    rcases sq_eq_one_iff.mp hr' with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [matrix, hentry, Matrix.scalar_apply, -theta_apply]

/-- The resulting homomorphism from the literal central quotient of SL₂ into Ree. -/
noncomputable def projectiveHom (m : ℕ) :
    (SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F)) →*
      Model F m :=
  QuotientGroup.lift _ (specialLinearHom m) (by rw [specialLinearHom_ker])

/-- The projective representation is faithful. -/
lemma projectiveHom_injective (m : ℕ) : Function.Injective (projectiveHom (F := F) m) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  induction g using QuotientGroup.induction_on with | H g =>
    change projectiveHom m (QuotientGroup.mk g) = 1 at hg
    change specialLinearHom m g = 1 at hg
    exact (QuotientGroup.eq_one_iff _).mpr (by rw [← specialLinearHom_ker m]; exact hg)

/-- The SL₂ image centralizes the torus involution h(−1). -/
lemma specialLinearHom_commute (m : ℕ) (g : SpecialLinearGroup (Fin 2) F) :
    Commute (torusInvolution m) (specialLinearHom m g) := by
  apply Subtype.ext
  apply Units.ext
  change (torus m (-1)).val * matrix m g = matrix m g * (torus m (-1)).val
  change Matrix.diagonal _ * matrix m g = matrix m g * Matrix.diagonal _
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [matrix, torusDiagonal, -theta_apply]

/-- The PSL₂ image centralizes the torus involution h(−1). -/
lemma projectiveHom_commute (m : ℕ)
    (g : SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    Commute (torusInvolution m) (projectiveHom m g) := by
  induction g using QuotientGroup.induction_on with | H g =>
    exact specialLinearHom_commute m g

/-- The involution is outside the PSL₂ image, proving independence of the factors. -/
lemma projectiveHom_ne_involution (m : ℕ)
    (g : SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    projectiveHom m g ≠ torusInvolution m := by
  induction g using QuotientGroup.induction_on with | H g =>
    intro h
    have he : matrix m g = (torus m (-1)).val :=
      congrArg (fun x : Model F m => x.val.val) h
    have hc : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
      apply central_of_entries m g
      · have h' := congrArg (fun M : Mat F => M 1 1) he
        simpa [matrix, torus, diagonalUnit, torusDiagonal, -theta_apply] using h'
      · have h' := congrArg (fun M : Mat F => M 1 5) he
        simpa [matrix, torus, diagonalUnit, torusDiagonal, -theta_apply] using h'
      · have h' := congrArg (fun M : Mat F => M 5 1) he
        simpa [matrix, torus, diagonalUnit, torusDiagonal, -theta_apply] using h'
    have hg : specialLinearHom m g = 1 := by
      change g ∈ (specialLinearHom m).ker
      rw [specialLinearHom_ker]
      exact hc
    exact torusInvolution_ne_one m (h.symm.trans hg)

private lemma two_cases (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have h : a.toAdd = 0 ∨ a.toAdd = 1 := by
    generalize a.toAdd = b
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h with h | h
  · exact Or.inl (Multiplicative.toAdd.injective h)
  · exact Or.inr (Multiplicative.toAdd.injective h)

/-- The cyclic factor with its generator explicitly mapped to h(−1). -/
noncomputable def involutionHom (m : ℕ) : Multiplicative (ZMod 2) →* Model F m where
  toFun a := if a = 1 then 1 else torusInvolution m
  map_one' := if_pos rfl
  map_mul' a b := by
    rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl <;>
      norm_num [show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 by decide,
        show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide, ← pow_two, torusInvolution_sq]

/-- The nonidentity element of the cyclic factor maps to the torus involution. -/
lemma involutionHom_generator (m : ℕ) :
    involutionHom (F := F) m (Multiplicative.ofAdd 1) = torusInvolution m := by
  simp [involutionHom, show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide]

/-- The concrete C₂ × PSL₂ homomorphism into the actual Ree model. -/
noncomputable def productHom (m : ℕ) :
    Multiplicative (ZMod 2) ×
      (SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F)) →*
        Model F m where
  toFun g := involutionHom m g.1 * projectiveHom m g.2
  map_one' := by simp
  map_mul' a b := by
    change involutionHom m (a.1*b.1) * projectiveHom m (a.2*b.2) = _
    rw [map_mul, map_mul]
    have hc : Commute (projectiveHom m a.2) (involutionHom m b.1) := by
      rcases two_cases b.1 with h | h
      · rw [h, map_one]; exact Commute.one_right _
      · rw [h, involutionHom_generator]; exact (projectiveHom_commute m a.2).symm
    exact hc.symm.mul_mul_mul_comm _ _

/-- Both factors are faithful and have trivial intersection. -/
lemma productHom_injective (m : ℕ) : Function.Injective (productHom (F := F) m) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a,g⟩ h
  change involutionHom m a * projectiveHom m g = 1 at h
  rcases two_cases a with rfl | rfl
  · simp only [map_one, one_mul] at h
    have hg : g = 1 := projectiveHom_injective m (h.trans (map_one _).symm)
    simp [hg]
  · rw [involutionHom_generator] at h
    have he : projectiveHom m g = torusInvolution m := by
      have h' := congrArg (torusInvolution m * ·) h
      simpa only [← mul_assoc, ← pow_two, torusInvolution_sq, one_mul, mul_one] using h'
    exact (projectiveHom_ne_involution m g he).elim

/-- The marked first-factor involution is exactly h(−1). -/
lemma productHom_first (m : ℕ) :
    productHom (F := F) m (Multiplicative.ofAdd 1, 1) = torusInvolution m := by
  change involutionHom m (Multiplicative.ofAdd 1) * projectiveHom m 1 = _
  rw [involutionHom_generator, map_one, mul_one]

/-- The projective upper root parameter is literally the Ree beta parameter. -/
lemma projectiveHom_upper (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (b : Multiplicative F) :
    projectiveHom m (QuotientGroup.mk (SpecialLinearGroup.upperUnipotentHom F b)) =
      betaHom m hcard b := by
  apply Subtype.ext
  exact representation_upper m b.toAdd

/-- Both factors of the constructed product centralize its marked involution. -/
lemma productHom_commute (m : ℕ)
    (g : Multiplicative (ZMod 2) ×
      (SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) F))) :
    Commute (torusInvolution m) (productHom m g) := by
  rw [← productHom_first]
  apply Commute.map
  change (Multiplicative.ofAdd (1 : ZMod 2), (1 : SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) F))) * g = g * (Multiplicative.ofAdd 1, 1)
  ext <;> simp [mul_comm]

/-- The product subgroup gives the source's defining-characteristic local rank witness. -/
theorem exists_involution_primeRank_ge {G : Type*} [Group G] [Finite G]
    (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (f : Model F m →* G) (hf : Function.Injective f) :
    ∃ z : G, z ≠ 1 ∧ z^2 = 1 ∧
      2*m+1 ≤ primeRank 3 (Subgroup.centralizer ({z} : Set G)) :=
  SpecialLinearGroup.exists_involution_primeRank_ge_of_projective_product hcard
    (f.comp (productHom m)) (hf.comp (productHom_injective m))

end Atlas.ReeG2.InvolutionProduct
