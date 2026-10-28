module
public import Theory.SpecificGroups.SU3.ExtensionBorel.Actors
public import Theory.SpecificGroups.SU3.BinaryInvolutionTable

/-!
# The Sylow normalizer and an outer involution of PSU₃(2)

The full projective Borel torus is trivial over the field of order four.
Consequently every Sylow two-subgroup of the actual projective unitary
matrix group is self-normalizing, including for arbitrary Hermitian forms.
The entrywise Hermitian involution preserves the standard root Sylow but
is outer: inner root normalizers preserve the first Heisenberg coordinate,
whereas the field involution changes it.

Thus a two-power automorphism preserving a Sylow and acting trivially on
its normalizer quotient need not be inner at fixed-field order two. This
is the precise obstruction to extending the degree-at-least-two detector
in `NormalizerDisplacements`. It does not exclude the small row under an
ambient amalgam hypothesis.

Source: Huppert II.10.12 for the actual root and torus coordinates;
DGS, Groups and Graphs (1985), pp.94,104,118--119. The latter explicitly
retains U₃(2); its 6.1 argument cannot use a noncentral projective torus in
this row. `LocalStructure.SmallProjectiveUnitaryBorel` gives the literal
F.1.1 Borel and starred-endpoint applications.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwoNormalizer
open BorelTorus BorelTorus.SemilinearActors ExtensionBorel
open OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem root_normalizer_eq_borel {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    normalizer (projectiveRoot J hJ : Set _) = projectiveBorel J hJ := by
  obtain ⟨_,rho,p,_,_,_,hr,_⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R,T,hRU,_,hn,_,hRT,_,hRc,_,_,_,hreg,⟨coord,hcoord⟩,hT,hTall⟩ := hr
  have hcoord_eq (w : hermitianUnipotentCoord J) :
      (coord w).val = hermitianUnipotentPSU J hJ w := by
    obtain ⟨M,hM,he⟩ := hcoord w
    have hh : M = hermitianUnipotentGL J w := Units.ext hM
    apply Subtype.ext
    simpa only [hh,hermitianUnipotentPSU_val] using he
  have heR : R = projectiveRoot J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨w,hw⟩ := coord.surjective ⟨r,hr⟩
      exact ⟨w,(hcoord_eq w).symm.trans (congrArg Subtype.val hw)⟩
    · rintro _ ⟨w,rfl⟩
      rw [←hcoord_eq w]
      exact (coord w).property
  have heT : T = projectiveTorus J hJ := by
    apply le_antisymm
    · intro t ht
      obtain ⟨k,M,hM,he⟩ := hT ⟨t,ht⟩
      refine ⟨k,?_⟩
      apply Subtype.ext
      have hh : M = hermitianTorusGL J k := Units.ext hM
      simpa only [hh,hermitianTorusPSU_val] using he.symm
    · rintro _ ⟨k,rfl⟩
      obtain ⟨t,M,hM,he⟩ := hTall k
      have hh : (t : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        have hM' : M = hermitianTorusGL J k := Units.ext hM
        simpa only [hM',hermitianTorusPSU_val] using he
      exact hh ▸ t.property
  have hne : R ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at hRc
    have := one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)
    omega
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (BinaryInvolutionTable.IsotropicPoint J) :=
    MulAction.compHom _ rho
  have heN := BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl
    R p (fun _ hx => hRU hx) hne hreg hn
  rw [←heR,projectiveBorel,←heR,←heT,hRT]
  exact heN


private theorem fixed_card (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) : Nat.card {x : F // J.conj x = x} = 2 := by
  simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
    (by decide) (by simpa using hcard) (by simpa using hconj)

omit [Finite F] in
/-- The full projective torus vanishes at fixed-field order two. -/
theorem torus_eq_bot (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) : projectiveTorus J hJ = ⊥ := by
  apply bot_unique
  rintro _ ⟨k,rfl⟩
  apply mem_bot.mpr
  apply (projective_eq_one_iff J hJ k).mpr
  have hk : k^3=1 := by
    simpa [Nat.card_units,hcard] using pow_card_eq_one' (x := k)
  refine ⟨?_,hk⟩
  change J.conj (k : F) = (k : F)⁻¹
  rw [hconj]
  apply eq_inv_of_mul_eq_one_left
  have hh := congrArg Units.val hk
  change (k : F)^3=1 at hh
  simpa only [pow_succ] using hh

/-- The actual standard root group is self-normalizing. -/
theorem root_normalizer_eq (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) :
    normalizer (projectiveRoot J hJ : Set _) = projectiveRoot J hJ := by
  rw [root_normalizer_eq_borel J hJ (by decide) hcard (fixed_card J hcard hconj),
    projectiveBorel,torus_eq_bot J hJ hcard hconj,sup_bot_eq]

private theorem field_root (σ : F ≃+* F) (z : hermitianUnipotentCoord J) :
    fieldActorHom J hJ σ (root J hJ z) = root J hJ (rootFieldEquiv J σ z) := by
  apply Subtype.ext
  change (fieldActor J hJ σ (root J hJ z)).val = _
  rw [fieldActor_apply_val]
  change ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk (hermitianUnipotentGL J z)) =
    ProjGenLinGroup.mk (hermitianUnipotentGL J (rootFieldEquiv J σ z))
  rw [ProjGenLinGroup.map_mk,field_map_root]

private theorem field_preserves_root (σ : F ≃+* F) :
    (projectiveRoot J hJ).map (fieldActorHom J hJ σ).toMonoidHom = projectiveRoot J hJ :=
  actorBorel_preserves_root J hJ _ (mem_sup_right ⟨σ,rfl⟩)

/-- An entrywise field actor on PSU₃(2) is inner only for the identity coefficient. -/
theorem field_eq_one_of_inner (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) (σ : F ≃+* F)
    (hi : fieldActorHom J hJ σ ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    σ = 1 := by
  obtain ⟨g,hg⟩ := hi
  have hgn : g ∈ normalizer (projectiveRoot J hJ : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hg]
    exact field_preserves_root J hJ σ
  rw [root_normalizer_eq J hJ hcard hconj] at hgn
  obtain ⟨t,rfl⟩ := hgn
  apply RingEquiv.ext
  intro a
  obtain ⟨z,hz⟩ := EvenSemilinear.coord_first_surjective J hcard (fixed_card J hcard hconj) a
  have he := congrArg (fun f : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => f (root J hJ z)) hg
  change root J hJ t * root J hJ z * (root J hJ t)⁻¹ = _ at he
  rw [field_root,←map_inv,←map_mul,←map_mul] at he
  have hh := congrArg (fun w : hermitianUnipotentCoord J => w.val.1) ((root_injective J hJ) he)
  rw [rootFieldEquiv_val] at hh
  change t.val.1 + z.val.1 + -t.val.1 = σ z.val.1 at hh
  simpa [hz,add_comm,add_left_comm,add_assoc] using hh.symm

/-- The stored field involution is nontrivial at matrix-field order four. -/
theorem conjugation_ne_one (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) : J.conj ≠ 1 := by
  intro he
  have ha (x : F) : J.conj x = x := by rw [he]; rfl
  have hh := Nat.card_congr (Equiv.subtypeUnivEquiv ha)
  rw [fixed_card J hcard hconj,hcard] at hh
  norm_num at hh

include hJ in
/-- The small projective group violates the proposed unrestricted normalizer-displacement detector. -/
theorem outer_involution_with_trivial_normalizer_displacements
    (hcard : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2) :
    ∃ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      a^2=1 ∧ (S : Subgroup _).map a.toMonoidHom = S ∧
      (∀ x ∈ normalizer (S : Set _), x⁻¹*a x ∈ S) ∧
      a ∉ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let S := EvenTwoRank.rootSylow J hJ (n := 1) (by decide)
    (by simpa using hcard) (by simpa using fixed_card J hcard hconj)
  let a := fieldActorHom J hJ J.conj
  have hm : (S : Subgroup _).map a.toMonoidHom = S := field_preserves_root J hJ J.conj
  have hn : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := root_normalizer_eq J hJ hcard hconj
  refine ⟨S,a,?_,hm,?_,?_⟩
  · change fieldActorHom J hJ J.conj ^ 2=1
    rw [←map_pow]
    have hh : J.conj^2=1 := by
      apply RingEquiv.ext
      intro x
      exact J.conj_involutive x
    rw [hh,map_one]
  · intro x hx
    have hxS : x ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [←hn]; exact hx
    have haS : a x ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [←hm]; exact mem_map_of_mem a.toMonoidHom hxS
    exact (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).mul_mem
      ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).inv_mem hxS) haS
  · exact fun hi => conjugation_ne_one J hcard hconj (field_eq_one_of_inner J hJ hcard hconj J.conj hi)

private theorem normalizer_transport {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (R : Subgroup H)
    (hn : normalizer (R.map e.toMonoidHom : Set K) = R.map e.toMonoidHom) :
    normalizer (R : Set H) = R := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rwa [map_equiv_normalizer_eq]

include hJ in
/-- Every Sylow in the standard model is self-normalizing. -/
theorem standard_sylow_normalizer_eq (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let S := EvenTwoRank.rootSylow J hJ (n := 1) (by decide)
    (by simpa using hcard) (by simpa using fixed_card J hcard hconj)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) T S
  have he : (T : Subgroup _).map (MulAut.conj g).toMonoidHom = (S : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  apply normalizer_transport (MulAut.conj g)
  rw [he]
  exact root_normalizer_eq J hJ hcard hconj

/-- Genuine Hermitian basis change gives self-normalization for every form and Sylow. -/
theorem sylow_normalizer_eq (hcard : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J 2 hcard (fixed_card J hcard hconj)
  apply normalizer_transport e
  exact standard_sylow_normalizer_eq
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hcard hconj
    (T.mapSurjective (f := e.toMonoidHom) e.surjective)

end BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwoNormalizer
