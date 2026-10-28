module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Geometry
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Coordinates

/-!
# Five conjugates of the sign involution in PSU₃

For the antidiagonal Hermitian form, the torus element at −1 is
`diag(−1, 1, −1)`. Its commutator with an upper root element doubles the
first root coordinate. Choose first coordinates 1 and an element outside
the fixed field. The two resulting commutators do not commute, and hence
generate the entire root group of order p³: every proper subgroup of a
group of this order is abelian.

The sign involution commutes with the Weyl element, so the same two
coordinates generate the opposite root. The five conjugators are the
identity, these two upper root elements, and their two opposite root
counterparts. Simplicity and the existing isotropic-point geometry show
that the two roots generate the actual projective matrix group.

This is a direct uniform inner-involution argument for the conjugate bound
used in Guralnick–Malle, *Classification of 2F-modules I*, §2 and
Proposition 4.3, and Aschbacher–Smith K.2, printed p.453. Proposition 4.3
explicitly gives five at seven; the argument here works for every odd
prime fixed-field order. Root coordinates and geometry are Huppert
II.10.12, as formalized in the imported modules.
-/

public section

open Matrix Subgroup BenderSuzuki.External
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner
open OddPrimeSylow.NormalizedOuter.Coverage

private theorem eq_top_of_noncommuting_mem {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card G = p ^ 3)
    (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (hxy : x * y ≠ y * x) : H = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  have hdiv : Nat.card H ∣ p ^ 3 := hcard ▸ H.card_subgroup_dvd_card
  obtain ⟨n, hn, hH⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hnot : ¬ IsMulCommutative H := by
    intro h
    exact hxy (congrArg Subtype.val (h.is_comm.comm (⟨x, hx⟩ : H) ⟨y, hy⟩))
  interval_cases n
  · exact (hnot (by
      let : IsCyclic H := isCyclic_of_card_dvd_prime (p := p) (by simp [hH])
      infer_instance)).elim
  · exact (hnot (by
      let : IsCyclic H := isCyclic_of_card_dvd_prime (p := p) (by simp [hH])
      infer_instance)).elim
  · exact (hnot (IsPGroup.isMulCommutative_of_card_eq_prime_sq hH)).elim
  · exact H.eq_top_of_card_eq (hH.trans hcard.symm)

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private def displacement (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  z * hermitianTorusAction J (-1) z⁻¹

private theorem displacement_fst (z : hermitianUnipotentCoord J) :
    (displacement J z).val.1 = 2 * z.val.1 := by
  change z.val.1 + (hermitianTorusAction J (-1) z⁻¹).val.1 = _
  simp only [hermitianTorusAction_fst, Units.val_neg, Units.val_one, map_neg,
    map_one, inv_neg, inv_one, neg_one_sq, mul_one, mul_neg_one]
  change z.val.1 + -(-z.val.1) = _
  ring

private theorem exists_moved [Finite E] {p : ℕ} (hp : 1 < p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p) :
    ∃ a : E, J.conj a ≠ a := by
  by_contra! hall
  let e : {x : E // J.conj x = x} ≃ E :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hall x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := hfixed.symm.trans ((Nat.card_congr e).trans hcard)
  nlinarith

/-- Two commutators with the sign involution generate the whole upper root
coordinate group. The fixed-field order is prime, so every proper subgroup of
its group of order p³ is abelian. -/
private theorem exists_displacement_generators [Finite E]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {p : ℕ} (hp : p.Prime)
    (h2 : (2 : E) ≠ 0) (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p) :
    ∃ z w : hermitianUnipotentCoord J,
      ∀ H : Subgroup (hermitianUnipotentCoord J),
        displacement J z ∈ H → displacement J w ∈ H → H = ⊤ := by
  obtain ⟨a, ha⟩ := exists_moved J hp.one_lt hcard hfixed
  obtain ⟨z, hz⟩ := coord_first_surjective J h2 1
  obtain ⟨w, hw⟩ := coord_first_surjective J h2 a
  change z.val.1 = 1 at hz
  change w.val.1 = a at hw
  have hn : displacement J z * displacement J w ≠
      displacement J w * displacement J z := by
    intro heq
    have he := congrArg (fun v : hermitianUnipotentCoord J => v.val.2) heq
    change (displacement J z).val.2 + (displacement J w).val.2 -
      (displacement J z).val.1 * J.conj (displacement J w).val.1 =
      (displacement J w).val.2 + (displacement J z).val.2 -
      (displacement J w).val.1 * J.conj (displacement J z).val.1 at he
    rw [displacement_fst, displacement_fst, hz, hw, map_mul, map_ofNat,
      mul_one, map_ofNat] at he
    apply ha
    apply mul_left_cancel₀ h2
    apply mul_left_cancel₀ h2
    linear_combination -he
  have hc : Nat.card (hermitianUnipotentCoord J) = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective (root_injective J hJ)).toEquiv).trans
      (rootGroup_card J hJ p hcard hfixed)
  exact ⟨z, w, fun H hz hw => eq_top_of_noncommuting_mem hp hc H hz hw hn⟩

private theorem range_le_of_displacements {G : Type*} [Group G]
    (f : hermitianUnipotentCoord J →* G) (t : G)
    (hact : ∀ z, t * f z = f (hermitianTorusAction J (-1) z) * t)
    {z w : hermitianUnipotentCoord J}
    (hgen : ∀ H : Subgroup (hermitianUnipotentCoord J),
      displacement J z ∈ H → displacement J w ∈ H → H = ⊤)
    (H : Subgroup G) (ht : t ∈ H)
    (hz : f z * t * (f z)⁻¹ ∈ H) (hw : f w * t * (f w)⁻¹ ∈ H) :
    f.range ≤ H := by
  have hmem (v : hermitianUnipotentCoord J) (hv : f v * t * (f v)⁻¹ ∈ H) :
      displacement J v ∈ H.comap f := by
    change f (v * hermitianTorusAction J (-1) v⁻¹) ∈ H
    have he : f (v * hermitianTorusAction J (-1) v⁻¹) =
        (f v * t * (f v)⁻¹) * t⁻¹ := by
      rw [map_mul, mul_assoc (f v) t, ← map_inv, hact]
      group
    rw [he]
    exact H.mul_mem hv (H.inv_mem ht)
  have he := hgen (H.comap f) (hmem z hz) (hmem w hw)
  rintro x ⟨v, rfl⟩
  exact (show v ∈ H.comap f from he ▸ mem_top v)

/-- The sign involution is the actual projective torus element at −1. -/
abbrev signInvolution (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    ProjectiveSpecialUnitaryMatrixGroup J := hermitianTorusPSU J hJ (-1)

private theorem weyl_commutes_sign (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    weyl J hJ * signInvolution J hJ = signInvolution J hJ * weyl J hJ := by
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL *
      ProjGenLinGroup.mk (hermitianTorusGL J (-1)) =
    ProjGenLinGroup.mk (hermitianTorusGL J (-1)) * ProjGenLinGroup.mk hermitianWeylGL
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, hermitianTorusGL,
      hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sign_opposite_action (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (z : hermitianUnipotentCoord J) :
    signInvolution J hJ * oppositeRoot J hJ z =
      oppositeRoot J hJ (hermitianTorusAction J (-1) z) * signInvolution J hJ := by
  have hc := weyl_commutes_sign J hJ
  have ha := hermitianTorusPSU_mul_unipotent J hJ (-1) z
  simp only [oppositeRoot_apply]
  calc
    _ = weyl J hJ * (signInvolution J hJ * root J hJ z) * (weyl J hJ)⁻¹ := by
      rw [← mul_assoc, ← mul_assoc, ← hc]
      group
    _ = weyl J hJ * (root J hJ (hermitianTorusAction J (-1) z) *
        signInvolution J hJ) * (weyl J hJ)⁻¹ := by rw [ha]
    _ = _ := by
      have hi : signInvolution J hJ * (weyl J hJ)⁻¹ =
          (weyl J hJ)⁻¹ * signInvolution J hJ := (Commute.symm hc).inv_right
      simp only [mul_assoc]
      rw [hi]

/-- Five explicit inner conjugators generate the full projective group from
the sign involution. -/
theorem sign_five_generate [Finite E]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (h2 : (2 : E) ≠ 0)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p) :
    ∃ s : Fin 5 → ProjectiveSpecialUnitaryMatrixGroup J,
      closure (Set.range fun i => s i * signInvolution J hJ * (s i)⁻¹) = ⊤ := by
  obtain ⟨z, w, hgen⟩ := exists_displacement_generators J hJ hp h2 hcard hfixed
  let s : Fin 5 → ProjectiveSpecialUnitaryMatrixGroup J :=
    ![1, root J hJ z, root J hJ w, oppositeRoot J hJ z, oppositeRoot J hJ w]
  let H := closure (Set.range fun i => s i * signInvolution J hJ * (s i)⁻¹)
  have hs (i : Fin 5) : s i * signInvolution J hJ * (s i)⁻¹ ∈ H :=
    subset_closure ⟨i, rfl⟩
  have ht : signInvolution J hJ ∈ H := by simpa [s] using hs 0
  have hU : rootGroup J hJ ≤ H :=
    range_le_of_displacements J (root J hJ) (signInvolution J hJ)
      (hermitianTorusPSU_mul_unipotent J hJ (-1)) hgen H ht
      (by simpa [s] using hs 1) (by simpa [s] using hs 2)
  have hV : oppositeRootGroup J hJ ≤ H :=
    range_le_of_displacements J (oppositeRoot J hJ) (signInvolution J hJ)
      (sign_opposite_action J hJ) hgen H ht
      (by simpa [s] using hs 3) (by simpa [s] using hs 4)
  refine ⟨s, top_unique ?_⟩
  rw [← rootGroup_sup_oppositeRootGroup J hJ hp.one_lt hcard hfixed]
  exact sup_le hU hV

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner
