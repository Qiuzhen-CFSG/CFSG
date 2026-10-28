module

public import Theory.SpecificGroups.SU3.EvenTwoRank

/-!
# Generation by distinct binary PSU₃ Sylow subgroups

Two distinct Sylow two-subgroups of the actual simple projective unitary
matrix group generate it. A root subgroup acts regularly away from its fixed
isotropic point. Two distinct roots therefore generate a transitive subgroup;
that subgroup contains every conjugate root, and simplicity finishes the proof.
Sylow conjugacy gives arbitrary pairs. An actual projective matrix equivalence
then transports arbitrary Hermitian forms to the standard antidiagonal form,
retaining the stored quadratic Frobenius and both field cardinalities.

The action and normal-closure argument are adapted from the private proofs in
`SU3/OddPrimeSylowAutomorphisms/NormalizedOuterInvolutions/Coverage/Geometry`.
The binary Sylow construction is `EvenTwoRank.rootSylow`; no prime fixed-field
or outer-automorphism coverage assumption is used.

Source: Huppert, *Endliche Gruppen I*, II.10.12, as formalized in
`BenderSuzuki/External/Huppert/II/theorem_10_12.lean`. This supplies the pair
geometry used in Aschbacher–Smith E.1.14(1), citing Aschbacher 1982, Lemma 4.7.
-/

open Matrix BenderSuzuki.External
open scoped LinearAlgebra.Projectivization
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenRootPairs
open OddPrimeSylow.NormalizedOuter.Coverage

private abbrev isotropicPoints {E : Type*} [Field E] (J : HermitianForm 3 E) :=
  {x : ℙ E (Fin 3 → E) // ∃ (v : Fin 3 → E) (hv : v ≠ 0),
    x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}

private theorem root_action {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (isotropicPoints J))
      (alpha : isotropicPoints J),
      (∀ u ∈ rootGroup J hJ, rho u alpha = alpha) ∧
      (∀ g, rho g alpha = alpha →
        (rootGroup J hJ).map (MulAut.conj g).toMonoidHom = rootGroup J hJ) ∧
      (∀ x y, x ≠ alpha → y ≠ alpha →
        ∃! u : rootGroup J hJ, rho u.val x = y) ∧
      (∀ x y z t, x ≠ y → z ≠ t →
        ∃ g, rho g x = z ∧ rho g y = t) := by
  obtain ⟨_, rho, alpha, _, _, _, hroot, htwo, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, hRfix, _, hRnorm, _, _, _, _, _, _, _, hregular,
    ⟨coord, hcoord⟩, _⟩ := hroot
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = root J hJ z := by
    obtain ⟨M, hM, heq⟩ := hcoord z
    have hM' : M = hermitianUnipotentGL J z := Units.ext hM
    apply Subtype.ext
    simpa only [hM', hermitianUnipotentPSU_val] using heq
  have hR : R = rootGroup J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨z, (hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z, rfl⟩
      rw [← hcoord_eq z]
      exact (coord z).property
  subst R
  refine ⟨rho, alpha, ?_, ?_, hregular, htwo⟩
  · exact fun u hu => hRfix hu
  · intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnorm hg)

private theorem map_conj_mul {G : Type*} [Group G] (U : Subgroup G) (g h : G) :
    (U.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      U.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]


private theorem conjugate_eq_of_point_eq {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hnorm : ∀ g, rho g alpha = alpha → U.map (MulAut.conj g).toMonoidHom = U)
    (g h : G) (hpoint : rho g alpha = rho h alpha) :
    U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj h).toMonoidHom := by
  have hn : U.map (MulAut.conj (h⁻¹ * g)).toMonoidHom = U := by
    apply hnorm
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [hpoint]
    exact (rho h).symm_apply_apply alpha
  calc
    U.map (MulAut.conj g).toMonoidHom =
        (U.map (MulAut.conj (h⁻¹ * g)).toMonoidHom).map
          (MulAut.conj h).toMonoidHom := by rw [map_conj_mul]; simp
    _ = U.map (MulAut.conj h).toMonoidHom := by rw [hn]


private theorem conjugate_transitive {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hregular : ∀ x y, x ≠ alpha → y ≠ alpha →
      ∃! u : U, rho u.val x = y)
    (w : G) (x y : X) (hx : x ≠ rho w alpha) (hy : y ≠ rho w alpha) :
    ∃ v ∈ U.map (MulAut.conj w).toMonoidHom, rho v x = y := by
  have hx' : (rho w).symm x ≠ alpha := by
    intro heq
    apply hx
    rw [← heq, Equiv.apply_symm_apply]
  have hy' : (rho w).symm y ≠ alpha := by
    intro heq
    apply hy
    rw [← heq, Equiv.apply_symm_apply]
  obtain ⟨u, hu, _⟩ := hregular _ _ hx' hy'
  refine ⟨w * u.val * w⁻¹, ⟨u.val, u.property, rfl⟩, ?_⟩
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  change rho w (rho u.val ((rho w).symm x)) = y
  rw [hu, Equiv.apply_symm_apply]

private theorem sup_conjugate_eq_top {G X : Type*} [Group G] [IsSimpleGroup G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hnorm : ∀ g, rho g alpha = alpha → U.map (MulAut.conj g).toMonoidHom = U)
    (hregular : ∀ x y, x ≠ alpha → y ≠ alpha →
      ∃! u : U, rho u.val x = y)
    (hU : U ≠ ⊥) (w : G) (hw : rho w alpha ≠ alpha) :
    U ⊔ U.map (MulAut.conj w).toMonoidHom = ⊤ := by
  let V := U.map (MulAut.conj w).toMonoidHom
  let H := U ⊔ V
  let beta := rho w alpha
  have hUle : U ≤ H := le_sup_left
  have hVle : V ≤ H := le_sup_right
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hmove : rho u.val beta ≠ beta := by
    intro hbad
    obtain ⟨r, _, hr⟩ := hregular beta beta hw hw
    apply hu
    exact (hr u hbad).trans (hr 1 (by simp)).symm
  obtain ⟨v, hv, hvpoint⟩ := conjugate_transitive rho U alpha hregular w
    alpha (rho u.val beta) hw.symm hmove
  let t := u.val⁻¹ * v
  have ht : t ∈ H := H.mul_mem
    (H.inv_mem (hUle u.property)) (hVle hv)
  have htpoint : rho t alpha = beta := by
    simp only [t, map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [hvpoint]
    exact (rho u.val).symm_apply_apply beta
  have htrans (x : X) : ∃ h ∈ H, rho h alpha = x := by
    by_cases hx : x = alpha
    · exact ⟨1, H.one_mem, by simp [hx]⟩
    · obtain ⟨r, hr, _⟩ := hregular beta x hw hx
      refine ⟨r.val * t, H.mul_mem (hUle r.property) ht, ?_⟩
      simpa only [map_mul, Equiv.Perm.mul_apply, htpoint] using hr
  have hconjugates (g : G) : U.map (MulAut.conj g).toMonoidHom ≤ H := by
    obtain ⟨h, hh, hpoint⟩ := htrans (rho g alpha)
    rw [conjugate_eq_of_point_eq rho U alpha hnorm g h hpoint.symm]
    rintro x ⟨u, hu, rfl⟩
    exact H.mul_mem (H.mul_mem hh (hUle hu)) (H.inv_mem hh)
  have hclosure : Subgroup.normalClosure (U : Set G) ≤ H := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨u, hu, hg⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hg
    exact hconjugates g ⟨u, hu, rfl⟩
  have htop : Subgroup.normalClosure (U : Set G) = ⊤ := by
    apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
    intro hbot
    exact hU (le_bot_iff.mp (hbot ▸ Subgroup.le_normalClosure))
  exact top_le_iff.mp (htop ▸ hclosure)

private theorem rootGroup_sup_conjugate_eq_top {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {q : ℕ} (hq : 1 < q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hne : (rootGroup J hJ).map (MulAut.conj g).toMonoidHom ≠ rootGroup J hJ) :
    rootGroup J hJ ⊔ (rootGroup J hJ).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨rho, alpha, _, hnorm, hregular, _⟩ := root_action J hJ q hcard hfixed
  have hU : rootGroup J hJ ≠ ⊥ := by
    intro hbot
    have hc := rootGroup_card J hJ q hcard hfixed
    rw [hbot, Subgroup.card_bot] at hc
    have hq3 : 1 < q ^ 3 := one_lt_pow₀ hq (by decide)
    omega
  exact sup_conjugate_eq_top rho (rootGroup J hJ) alpha hnorm hregular hU g
    (fun heq => hne (hnorm g heq))

private theorem sylow_pair_of_conjugate_pair {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (U : Sylow p G)
    (hU : ∀ g : G, (U : Subgroup G).map (MulAut.conj g).toMonoidHom ≠ U →
      (U : Subgroup G) ⊔ (U : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤)
    (P Q : Sylow p G) (hne : P ≠ Q) : (P : Subgroup G) ⊔ Q = ⊤ := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G U P
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G U Q
  have ha' : (U : Subgroup G).map (MulAut.conj a).toMonoidHom = P :=
    congrArg Sylow.toSubgroup ha
  have hb' : (U : Subgroup G).map (MulAut.conj b).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup hb
  have hQ : (Q : Subgroup G).map (MulAut.conj a⁻¹).toMonoidHom =
      (U : Subgroup G).map (MulAut.conj (a⁻¹ * b)).toMonoidHom := by
    rw [← hb', map_conj_mul]
  have hP : (P : Subgroup G).map (MulAut.conj a⁻¹).toMonoidHom = U := by
    rw [← ha', map_conj_mul, inv_mul_cancel, map_one]
    exact Subgroup.map_id _
  have hne' : (U : Subgroup G).map (MulAut.conj (a⁻¹ * b)).toMonoidHom ≠ U := by
    intro heq
    apply hne
    apply Sylow.ext
    apply Subgroup.map_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
      (MulAut.conj a⁻¹).injective
    rw [hP, hQ, heq]
  apply Subgroup.map_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
    (MulAut.conj a⁻¹).injective
  rw [Subgroup.map_sup, hP, hQ, hU _ hne', Subgroup.map_top_of_surjective _
    (MulAut.conj a⁻¹).surjective]

private instance {E : Type*} [Field E] [Finite E] :
    Finite (ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

private theorem standard_sylow_sup_eq_top {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (P Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (hne : P ≠ Q) :
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ Q = ⊤ := by
  apply sylow_pair_of_conjugate_pair (EvenTwoRank.rootSylow J hJ hn hcard hfixed) _ P Q hne
  intro g hg
  exact rootGroup_sup_conjugate_eq_top J hJ
    (one_lt_pow₀ (by decide : 1 < 2) (by omega : n ≠ 0)) hcard hfixed g hg

/-- Any two distinct Sylow two-subgroups of the actual simple projective
unitary group over a binary quadratic field generate the whole group.
The Hermitian form is arbitrary and its involution is the prescribed Frobenius. -/
public theorem sylow_sup_eq_top {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (P Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (hne : P ≠ Q) :
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ Q = ⊤ := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup
      (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)) := e.symm.isSimpleGroup
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hne' : P' ≠ Q' := by
    intro heq
    apply hne
    apply Sylow.ext
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective
      (congrArg Sylow.toSubgroup heq)
  have ht := standard_sylow_sup_eq_top
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl
    hn hcard hfixed P' Q' hne'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.surjective]
  exact ht

end BenderSuzuki.MatrixGroups.HermitianForm.EvenRootPairs
