module
public import Theory.SpecificGroups.SU3.QuinticSylow
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner.Conjugacy
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import ABG.ChapterII.Section2.UnitaryCard
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.TorusPreservation
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootSylow
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Recognizing quintic root centers in PSU₃(5)

An involution centralizer has order dividing 720, by lifting the involution
to SU₃(5) and identifying its centralizer with GU₂(5). Thus its subgroups of
order five are Sylow. The explicit diagonal involution centralizes the
center of the upper root Sylow: the first root coordinate vanishes on the
commutator subgroup. Involution conjugacy and Sylow conjugacy inside the
centralizer show that every order-five subgroup centralized by an involution
is the center of an actual Sylow five-group. Hermitian basis transport
retains the supplied subgroup exactly.

This supplies the model step in Aschbacher--Smith, original 4.3.2, printed
p.618. The local source must still exhibit the involution centralizing its
prescribed quintic image. Matrix inputs are Huppert II.10.12 and the unitary
involution-centralizer calculations cited in the imported modules.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.QuinticRootCenter
open OddPrimeSylow.NormalizedOuter.Coverage
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem standard_centralizer_card_dvd
    (k : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 5 1 one_ne_zero))
    (hk : orderOf k = 2) :
    Nat.card (centralizer ({k} : Set _)) ∣ 720 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let J3 := ABG.unitaryForm 3 5 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 5 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := Matrix.SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube k hk
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    Matrix.SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  let ec : C ≃* J2.unitarySubgroup :=
    (Matrix.SU3.involutionCentralizerEquiv (by decide : 5 ≠ 2)
      (GaloisField.card 5 (2 * 1) (by decide)) J3 J2 rfl rfl
      (by intro x; simp only [J3, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one])
      (by intro x; simp only [J2, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]) z hz).symm
  have hd := card_dvd_of_surjective f hf
  rw [Nat.card_congr ec.toEquiv] at hd
  have hcard : Nat.card J2.unitarySubgroup = 720 := by
    change Nat.card (ABG.GU2 5 1 one_ne_zero) = 720
    rw [ABG.GU2_card 5 1 (by decide) one_ne_zero]
    norm_num
  exact hcard ▸ hd

/-- An involution centralizer has no subgroup of order 25. -/
theorem centralizer_card_dvd {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hF : Nat.card F = 5 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 5)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set _)) ∣ 720 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e⟩ := Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard 5 F J hF hc
  rw [Nat.card_congr (Matrix.SU3.InnerThreeRank.centralizerEquiv e t).toEquiv]
  exact standard_centralizer_card_dvd (e t) ((e.orderOf_eq t).trans ht)

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def rootEquiv : hermitianUnipotentCoord J ≃* rootGroup J hJ :=
  MulEquiv.ofBijective (root J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
      (root J hJ).rangeRestrict_surjective⟩

private def firstCoordinate : hermitianUnipotentCoord J →* Multiplicative F where
  toFun z := Multiplicative.ofAdd z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem root_commutator_eq_center (hF : Nat.card F = 5 ^ 2)
    (hf : Nat.card {x : F // J.conj x = x} = 5) :
    commutator (rootGroup J hJ) = center (rootGroup J hJ) := by
  obtain ⟨_, _, _, _, _, _, hroot, _⟩ := huppert_II_10_12 J 5 hF hf hJ
  obtain ⟨R, _, _, _, _, _, _, _, _, hd, _, _, _, ⟨e, he⟩, _⟩ := hroot
  have heq (z : hermitianUnipotentCoord J) :
      (e z : ProjectiveSpecialUnitaryMatrixGroup J) = root J hJ z := by
    obtain ⟨M, hM, heM⟩ := he z
    apply Subtype.ext
    rw [heM]
    change ProjGenLinGroup.mk M = ProjGenLinGroup.mk (hermitianUnipotentGL J z)
    congr 1
    exact Units.ext hM
  have hR : R = rootGroup J hJ := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, (heq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro ⟨z, rfl⟩
      rw [← heq z]
      exact (e z).property
  exact hR ▸ hd

/-- The diagonal involution centralizes the full center of the actual root Sylow. -/
theorem root_center_centralizes_torus (hF : Nat.card F = 5 ^ 2)
    (hf : Nat.card {x : F // J.conj x = x} = 5) :
    (center (rootGroup J hJ)).map (rootGroup J hJ).subtype ≤
      centralizer ({hermitianTorusPSU J hJ (-1)} : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, rfl⟩ := (rootEquiv J hJ).surjective x
  have hz0 : z.val.1 = 0 := by
    let f := (firstCoordinate J).comp (rootEquiv J hJ).symm.toMonoidHom
    have hk : (rootEquiv J hJ z) ∈ f.ker :=
      Abelianization.commutator_subset_ker f ((root_commutator_eq_center J hJ hF hf).symm ▸ hx)
    change f (rootEquiv J hJ z) = 1 at hk
    have hh : firstCoordinate J z = 1 := by
      simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using hk
    exact congrArg Multiplicative.toAdd hh
  have ha : hermitianTorusAction J (-1) z = z := by
    apply Subtype.ext
    apply Prod.ext
    · simp [hermitianTorusAction_fst, hz0]
    · simp [hermitianTorusAction_snd]
  apply mem_centralizer_singleton_iff.mpr
  change root J hJ z * hermitianTorusPSU J hJ (-1) =
    hermitianTorusPSU J hJ (-1) * root J hJ z
  rw [hermitianTorusPSU_mul_unipotent, ha]

include hJ in
/-- A root Sylow center can be placed in the centralizer of any involution. -/
theorem exists_center_in_centralizer (hF : Nat.card F = 5 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 5)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ∃ P : Sylow 5 (ProjectiveSpecialUnitaryMatrixGroup J),
      (center P).map (P : Subgroup _).subtype ≤ centralizer ({t} : Set _) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  let t₀ := hermitianTorusPSU J hJ (-1)
  have ht₀ : orderOf t₀ = 2 := torus_neg_orderOf J hJ
    (CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by decide : 5 ≠ 2))
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (InvolutionConjugateBounds.Inner.projective_involutions_isConj J
      (by decide : Nat.Prime 5) (by decide) hF hc t₀ t ht₀ ht)
  let P₀ := rootSylow J hJ (by decide : Nat.Prime 5) hF hf
  let f := MulAut.conj g
  let P := P₀.mapSurjective (f := f.toMonoidHom) f.surjective
  refine ⟨P, ?_⟩
  change (center ((P₀ : Subgroup _).map f.toMonoidHom)).map
    ((P₀ : Subgroup _).map f.toMonoidHom).subtype ≤ _
  rw [← map_embeddedCenter (P₀ : Subgroup _) f.toMonoidHom f.injective]
  have hz : (center P₀).map (P₀ : Subgroup _).subtype ≤ centralizer ({t₀} : Set _) :=
    by
      have he : (P₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = rootGroup J hJ :=
        rootSylow_coe J hJ (by decide : Nat.Prime 5) hF hf
      rw [he]
      exact root_center_centralizes_torus J hJ hF hf
  have hmap := (map_mono (f := f.toMonoidHom) hz).trans
    (map_centralizer_le_centralizer_image ({t₀} : Set _) f.toMonoidHom)
  simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom,
    show f t₀ = t from hg] using hmap

private theorem quintic_isSylow {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H ∣ 720) (X : Subgroup H) (hc : Nat.card X = 5) :
    ¬ 5 ∣ X.index := by
  intro hd
  have h25 : 25 ∣ Nat.card H := by
    have hm := X.card_mul_index
    rw [hc] at hm
    exact hm ▸ (Nat.mul_dvd_mul_left 5 hd)
  have hbad := h25.trans hH
  norm_num at hbad

include hJ in
/-- In PSU₃(5), an order-five subgroup centralizing an involution is a
Sylow five-center, retaining the original subgroup. -/
theorem center_eq_of_centralizes_involution (hF : Nat.card F = 5 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 5)
    (X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hX : Nat.card X = 5)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (hXt : X ≤ centralizer ({t} : Set _)) :
    ∃ P : Sylow 5 (ProjectiveSpecialUnitaryMatrixGroup J),
      (center P).map (P : Subgroup _).subtype = X := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨P₀, hZ⟩ := exists_center_in_centralizer J hJ hF hc t ht
  let Z : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (center P₀).map (P₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype
  have hZc : Nat.card Z = 5 := by
    let := (QuinticSylow.extraspecial_card J hF hc P₀).1
    change Nat.card ((center P₀).map
      (P₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype) = 5
    rw [card_map_of_injective
      (P₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype_injective]
    exact IsExtraspecial.center_order_p 5 P₀
  let C := centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  have hcC := centralizer_card_dvd J hF hc t ht
  have hzcard : Nat.card (Z.subgroupOf C) = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv).trans hZc
  have hxcard : Nat.card (X.subgroupOf C) = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXt).toEquiv).trans hX
  let R : Sylow 5 C := (IsPGroup.of_card (n := 1) (by simpa using hzcard)).toSylow
    (quintic_isSylow hcC _ hzcard)
  let S : Sylow 5 C := (IsPGroup.of_card (n := 1) (by simpa using hxcard)).toSylow
    (quintic_isSylow hcC _ hxcard)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C R S
  have hsub : (Z.subgroupOf C).map (MulAut.conj g).toMonoidHom = X.subgroupOf C :=
    congrArg Sylow.toSubgroup hg
  have hmap : Z.map (MulAut.conj (g : ProjectiveSpecialUnitaryMatrixGroup J)).toMonoidHom = X := by
    have hh := congrArg (Subgroup.map C.subtype) hsub
    rw [Subgroup.map_map, map_subgroupOf_eq_of_le hXt] at hh
    have he : C.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : ProjectiveSpecialUnitaryMatrixGroup J)).toMonoidHom.comp C.subtype := by
      ext x
      rfl
    rw [he, ← Subgroup.map_map, map_subgroupOf_eq_of_le hZ] at hh
    exact hh
  let a := MulAut.conj (g : ProjectiveSpecialUnitaryMatrixGroup J)
  refine ⟨P₀.mapSurjective (f := a.toMonoidHom) a.surjective, ?_⟩
  exact (map_embeddedCenter (P₀ : Subgroup _) a.toMonoidHom a.injective).symm.trans hmap


/-- Root-center recognition is independent of the stored Hermitian basis. -/
theorem center_eq_of_centralizes_involution_arbitrary (hF : Nat.card F = 5 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 5)
    (X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hX : Nat.card X = 5)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (hXt : X ≤ centralizer ({t} : Set _)) :
    ∃ P : Sylow 5 (ProjectiveSpecialUnitaryMatrixGroup J),
      (center P).map (P : Subgroup _).subtype = X := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J 5 hF hf
  have hx : Nat.card (X.map e.toMonoidHom) = 5 := by
    rw [card_map_of_injective e.injective, hX]
  have hn : X.map e.toMonoidHom ≤ centralizer ({e t} : Set _) := by
    simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      (map_mono (f := e.toMonoidHom) hXt).trans
        (map_centralizer_le_centralizer_image ({t} : Set _) e.toMonoidHom)
  obtain ⟨P, hP⟩ := center_eq_of_centralizes_involution
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hF hc
    (X.map e.toMonoidHom) hx (e t) ((e.orderOf_eq t).trans ht) hn
  refine ⟨P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
  change (center ((P : Subgroup _).map e.symm.toMonoidHom)).map
    ((P : Subgroup _).map e.symm.toMonoidHom).subtype = X
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [← map_embeddedCenter (P : Subgroup _) e.symm.toMonoidHom e.symm.injective, hP,
    Subgroup.map_map, he, Subgroup.map_id]

end BenderSuzuki.MatrixGroups.HermitianForm.QuinticRootCenter
