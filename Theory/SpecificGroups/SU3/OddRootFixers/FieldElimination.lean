module

public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.FieldFaithfulness
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.OddRootFixers.FieldElimination.Matrix
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Odd-order unitary root fixers have trivial field component

Sylow conjugacy carries the specified Sylow subgroup onto the canonical upper
root image. Central-root fixation then forces the semilinear representative
to be triangular with equal outer diagonal entries, and its field parameter
to fix the Hermitian fixed field. That parameter has square one. Semilinear
faithfulness detects its power at the order of the actor, so odd order forces
the parameter itself to be the identity.

For SU₃ the special scalar kernel is retained: its exponent-three property
identifies special and projective Sylow groups. The special semilinear
coverage theorem gives equality on actual matrices, and projective
faithfulness detects the field parameter of a formula for the special
identity. Neither argument excludes the identity actor.

These are the field-elimination and triangular-normalization steps of GLS4,
Chapter 4, Lemma 3.6(c), used with part (d) in Chapter 2, Lemma 13.2.
Diagonalization and the fixed PSL₂ construction are separate steps; the
conditional application is `FieldElimination.LinearReduction`.
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
open BorelTorus BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

omit [Finite E] in
private theorem rootSU_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h)

include hn hcard hfixed in
private theorem special_root_sylow :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup J.specialSubgroup) = specialRoot J hJ := by
  let R := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  let ec := SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ R
  let es : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
    MonoidHom.ofInjective (rootSU_injective J hJ)
  have hp : IsPGroup 2 (specialRoot J hJ) := (R.isPGroup'.of_equiv ec).of_equiv es
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hc : Nat.card S = Nat.card (specialRoot J hJ) :=
    Nat.card_congr (((SylowOmega.specialSylowEquivProjective J S).trans
      (SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ _)).trans es).toEquiv
  exact ⟨S, (eq_of_le_of_card_ge hS hc.le).symm⟩

private theorem sylow_normalization {G : Type*} [Group G] [Finite G]
    (P Q : Sylow 2 G) :
    ∃ e : MulAut G, (P : Subgroup G).map e.toMonoidHom = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨MulAut.conj g, congrArg Sylow.toSubgroup hg⟩

private theorem center_fixed_congr {G : Type*} [Group G]
    (P R : Subgroup G) (a e : MulAut G) (hP : P.map e.toMonoidHom = R)
    (hfix : ∀ x ∈ (center P).map P.subtype, a x = x) :
    ∀ x ∈ (center R).map R.subtype, MulAut.congr e a x = x := by
  rw [← hP, ← map_embeddedCenter P e.toMonoidHom e.injective]
  rintro x ⟨y, hy, rfl⟩
  change e (a (e.symm (e y))) = e y
  rw [e.symm_apply_apply, hfix y hy]

omit [Finite E] in
private theorem special_central_mem [CharP E 2] (b : fixedField J) :
    hermitianUnipotentSU J hJ (centralCoord J (.ofAdd b)) ∈
      (center (specialRoot J hJ)).map (specialRoot J hJ).subtype := by
  refine ⟨⟨_, ⟨centralCoord J (.ofAdd b), rfl⟩⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  rintro ⟨_, z, rfl⟩
  apply Subtype.ext
  exact (map_mul (hermitianUnipotentSU J hJ) _ _).symm.trans
    ((congrArg (hermitianUnipotentSU J hJ)
      (mem_center_iff.mp (centralCoord_mem_center J (.ofAdd b)) z)).trans
      (map_mul (hermitianUnipotentSU J hJ) _ _))

include hJ hn hcard hfixed in
private theorem special_identity_field (σ : E ≃+* E)
    (hσ : J.HasSpecialUnitarySemilinearForm 1 σ) : σ = 1 := by
  apply J.semilinear_identity_field_eq_one n hn hJ hcard hfixed σ
  obtain ⟨u, hu⟩ := hσ
  refine ⟨u, ?_⟩
  intro b
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  have h := congrArg ProjGenLinGroup.mk (hu x)
  simpa only [MulAut.one_apply, specialToProjective_apply_val, map_mul, map_inv,
    ProjGenLinGroup.map_mk] using h

private theorem eq_one_of_square_and_odd_power {G : Type*} [Group G]
    (x : G) (hs : x ^ 2 = 1) {m : ℕ} (hm : Odd m) (hp : x ^ m = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hm
  have he : m = 2 * k + 1 := by omega
  simpa only [he, pow_add, pow_mul, hs, one_pow, pow_one, one_mul] using hp


include hn hcard hfixed in
/-- Every odd-order SU₃ root fixer has a triangular identity-field formula,
with an actual automorphism carrying the marked Sylow onto the upper root. -/
theorem special_triangular_form
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map (P : Subgroup J.specialSubgroup).subtype, a x = x) :
    HasSpecialRootForm J hJ (IsRootTriangular J) P a := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨S, hS⟩ := special_root_sylow J hJ hn hcard hfixed
  obtain ⟨e, he⟩ := sylow_normalization P S
  have hP : (P : Subgroup J.specialSubgroup).map e.toMonoidHom = specialRoot J hJ :=
    he.trans hS
  let b := MulAut.congr e a
  have hb : Odd (orderOf b) := by simpa only [b, MulEquiv.orderOf_eq] using ha
  have hfixb := center_fixed_congr (P : Subgroup J.specialSubgroup)
    (specialRoot J hJ) a e hP hfix
  obtain ⟨σ, u, hu⟩ := EvenSemilinear.special_semilinear_coverage J hJ hn hcard
    (huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed) b
  obtain ⟨hshape, hfield⟩ := central_roots_force_triangular J σ u (fun t => by
    have hx := hu (hermitianUnipotentSU J hJ (centralCoord J (.ofAdd t)))
    rw [show b (hermitianUnipotentSU J hJ (centralCoord J (.ofAdd t))) =
      hermitianUnipotentSU J hJ (centralCoord J (.ofAdd t)) from
        hfixb _ (special_central_mem J hJ t)] at hx
    change hermitianUnipotentGL J (centralCoord J (.ofAdd t)) =
      u.val * GeneralLinearGroup.map σ.toRingHom
        (hermitianUnipotentGL J (centralCoord J (.ofAdd t))) * u.val⁻¹ at hx
    simpa only [map_mul, map_inv, ProjGenLinGroup.map_mk] using
      congrArg ProjGenLinGroup.mk hx)
  have hp := (show J.HasSpecialUnitarySemilinearForm b σ from ⟨u, hu⟩).pow
    J hJ (orderOf b)
  rw [pow_orderOf_eq_one] at hp
  have hσ : σ = 1 := eq_one_of_square_and_odd_power σ
    (field_square_of_fixed J σ hfield) hb
    (special_identity_field J hJ hn hcard hfixed _ hp)
  refine ⟨e, u, hshape, hP, fun x => ?_⟩
  simpa only [hσ, show (1 : E ≃+* E).toRingHom = RingHom.id E from rfl,
    GeneralLinearGroup.map_id, MonoidHom.id_apply] using hu x

include hn hcard hfixed in
/-- The corresponding normalization on the literal projective unitary image.
Trace one retains and then removes the projective scalar in the root equations. -/
theorem projective_triangular_form
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map
      (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype, a x = x) :
    HasProjectiveRootForm J hJ (IsRootTriangular J) P a := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let S := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  obtain ⟨e, hP⟩ := sylow_normalization P S
  change (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom =
    projectiveRoot J hJ at hP
  let b := MulAut.congr e a
  have hb : Odd (orderOf b) := by simpa only [b, MulEquiv.orderOf_eq] using ha
  have hfixb := center_fixed_congr (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (projectiveRoot J hJ) a e hP hfix
  obtain ⟨σ, u, hu⟩ := J.semilinear_coverage n hn hJ hcard hfixed b
  obtain ⟨hshape, hfield⟩ := central_roots_force_triangular J σ u (fun t => by
    have hx := hu (centralMap J hJ (.ofAdd t))
    rw [show b (centralMap J hJ (.ofAdd t)) = centralMap J hJ (.ofAdd t) from
      hfixb _ (centralImage_le_center J hJ ⟨.ofAdd t, rfl⟩)] at hx
    exact hx)
  have hp := (show J.HasUnitarySemilinearForm b σ from ⟨u, hu⟩).pow J hJ (orderOf b)
  rw [pow_orderOf_eq_one] at hp
  have hσ : σ = 1 := eq_one_of_square_and_odd_power σ
    (field_square_of_fixed J σ hfield) hb
    (J.semilinear_identity_field_eq_one n hn hJ hcard hfixed _ hp)
  refine ⟨e, u, hshape, hP, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [J.unitaryConj_apply_val]
  simpa only [hσ, show (1 : E ≃+* E).toRingHom = RingHom.id E from rfl,
    ProjGenLinGroup.map_id, MonoidHom.id_apply] using hu x

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
