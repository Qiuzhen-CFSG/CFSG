module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.BlocksGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedCentralizer

/-!
# The original moved module from the retained plane geometry

For the actual offender plane Z = [V,B], construct the original moved
subgroup U = [⟨Z^X⟩,X], its action through X/O₂(X), and its generating
Sylow-fixed seed U ∩ Z directly from ResidualInput.  Sylow averaging also
identifies the literal C_X(Z) image with the pointwise seed fixer.
The construction uses no identity for O^{3′}(Mc).

Source: Aschbacher--Smith 15.2.23, printed pp.1116--1117, using B.2.14;
refs/quasithin.pdf. These are the geometric inputs to LinearRows.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open PlaneUniquenessPreceding TerminalLinear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ResidualInput hsource H B)
include d

/-- Elementarity is inherited from Ω₁Z(O₂(I)), not assumed as model data. -/
theorem U_elementary (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    IsElementaryAbelian 2 (U X ⁅V,B⁆) := by
  let := d.plane_span_elementary hI hfit hXI
  exact IsElementaryAbelian.of_injective (inclusion (U_le_span X ⁅V,B⁆))
    (inclusion_injective (U_le_span X ⁅V,B⁆))

/-- Containment in the literal QI, needed for the maximum-elementary argument. -/
theorem U_le_QI (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    U X ⁅V,B⁆ ≤ QI H T ⁅V,B⁆ :=
  (U_le_span X ⁅V,B⁆).trans (d.plane_span_le_planeParabolicCore hI hfit hXI)

/-- Relative normality of X in I gives normalization of the original U by XQI. -/
theorem U_normalized (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hn : I ≤ normalizer (X : Set G)) :
    X ⊔ QI H T ⁅V,B⁆ ≤ normalizer (U X ⁅V,B⁆ : Set G) := by
  have hQI : QI H T ⁅V,B⁆ ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)
  have hX : X ⊔ QI H T ⁅V,B⁆ ≤ normalizer (X : Set G) :=
    sup_le X.le_normalizer (hQI.trans hn)
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅conjugateSpanBy ⁅V,B⁆ X, X⁆).map (MulAut.conj g).toMonoidHom = _
  have hw : (conjugateSpanBy ⁅V,B⁆ X).map (MulAut.conj g).toMonoidHom =
      conjugateSpanBy ⁅V,B⁆ X := mem_normalizer_iff_map_conj_eq.mp
        (d.plane_span_normalized hI hn hg)
  have hx : X.map (MulAut.conj g).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (hX hg)
  rw [map_commutator, hw, hx]
  rfl

/-- The actual QI-action has the same kernel on U and on the whole span. -/
theorem QI_centralizer_U_eq_span :
    QI H T ⁅V,B⁆ ⊓ centralizer (U X ⁅V,B⁆ : Set G) =
      QI H T ⁅V,B⁆ ⊓ centralizer (conjugateSpanBy ⁅V,B⁆ X : Set G) :=
  centralizer_U_eq_span ((pCoreIn_le 2 _).trans
    (sup_le d.residual_centralizes_plane inf_le_right))

/-- The genuine FF* witness for the orthogonal row, on U rather than on an
unrelated section. Only the marked core calculation remains an input. -/
theorem U_bestOffender
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hcore : (X ⊔ QI H T ⁅V,B⁆).pCoreIn 2 =
      QI H T ⁅V,B⁆ ⊓ centralizer (conjugateSpanBy ⁅V,B⁆ X : Set G)) :
    let E := X ⊔ QI H T ⁅V,B⁆
    let W := (U X ⁅V,B⁆).subgroupOf E
    let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
    let : IsElementaryAbelian 2 W := by
      let := U_elementary d hI hfit hXI
      exact IsElementaryAbelian.subgroupOf
        ((U_le_QI d hI hfit hXI).trans le_sup_right)
    let q := QuotientGroup.mk' (centralizer (W : Set E))
    ∃ A ∈ elementaryAbelianMaxSubgroups ((QI H T ⁅V,B⁆).subgroupOf E),
      Representation.BinaryOffender.IsBestOffender
        (Representation.NormalElementaryQuotient.representation W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) := by
  classical
  dsimp only
  let E := X ⊔ QI H T ⁅V,B⁆
  let W := (U X ⁅V,B⁆).subgroupOf E
  let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
  let : IsElementaryAbelian 2 (U X ⁅V,B⁆) := U_elementary d hI hfit hXI
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
    ((U_le_QI d hI hfit hXI).trans le_sup_right)
  let q := QuotientGroup.mk' (centralizer (W : Set E))
  let R := (QI H T ⁅V,B⁆).subgroupOf E
  have hR : R.map E.subtype = QI H T ⁅V,B⁆ := map_subgroupOf_eq_of_le le_sup_right
  have hJ : (elementaryAbelianMaxJ R).map E.subtype =
      elementaryAbelianMaxJ (QI H T ⁅V,B⁆) := by
    rw [← elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective, hR]
  have hj : ¬ elementaryAbelianMaxJ R ≤ q.ker := by
    intro hh
    apply d.planeParabolicCore_thompson_not_le_core hI hout (hcore.le.trans inf_le_left)
    change elementaryAbelianMaxJ (QI H T ⁅V,B⁆) ≤ (X ⊔ QI H T ⁅V,B⁆).pCoreIn 2
    rw [hcore, ← QI_centralizer_U_eq_span d]
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    rw [← hJ]
    rintro _ ⟨a, ha, rfl⟩ u hu
    let uE : E := ⟨u, ((U_le_QI d hI hfit hXI).trans le_sup_right) hu⟩
    have hc : a ∈ centralizer (W : Set E) := by
      simpa only [q, QuotientGroup.ker_mk'] using hh ha
    exact congrArg E.subtype (hc uE hu)
  obtain ⟨A, hA, hne⟩ : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hh
    exact hj (sSup_le fun A hA => (Subgroup.map_eq_bot_iff A).mp (hh A hA))
  exact ⟨A, hA, Representation.NormalElementaryQuotient.maxElementary_isBestOffender
    W q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) R A
    (fun _ hw => U_le_QI d hI hfit hXI hw) hA hne⟩


include d in
/-- The original U lies in the central elementary layer of the escaping I. -/
theorem U_le_omegaCore (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    U X ⁅V,B⁆ ≤ omegaOneCenterAmbient (I.pCoreIn 2) :=
  (U_le_span X ⁅V,B⁆).trans (conjugateSpanBy_le (d.plane_le_escape_core_omega hI hfit)
    (hXI.trans (I.le_normalizer.trans ((normalizer_le_normalizer_characteristic_image I (pCore 2 I)).trans
      (normalizer_le_normalizer_omegaCenter _)))))

include d in
/-- Core restriction retains the actual ambient embeddings. -/
theorem X_core_centralizes_U (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) :
    X.pCoreIn 2 ≤ centralizer (U X ⁅V,B⁆ : Set G) := by
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  have hcore : X.pCoreIn 2 ≤ I.pCoreIn 2 := by
    have hh := map_mono (f := I.subtype)
      (pCoreIn_le_of_subnormal 2 (inferInstance : (X.subgroupOf I).Normal).isSubnormal)
    rwa [map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hXI] at hh
  intro x hx u hu
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp
    (U_le_omegaCore d hI hfit hXI hu)).2.2 x (hcore hx)).symm

/-- Conjugation by X, acting on U with its original subgroup carrier. -/
noncomputable def U_conjugation (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hn : I ≤ normalizer (X : Set G)) : X →* MulAut (U X ⁅V,B⁆) :=
  (U X ⁅V,B⁆).normalizerMonoidHom.comp
    (inclusion (le_sup_left.trans (U_normalized d hI hn)))

/-- Descent of the actual conjugation action through X/O₂(X). -/
noncomputable def U_quotientConjugation (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) :
    (X ⧸ pCore 2 X) →* MulAut (U X ⁅V,B⁆) :=
  QuotientGroup.lift _ (U_conjugation d hI hn) (by
    intro x hx
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change (x : G) * (u : G) * (x : G)⁻¹ = u
    have hc : (u : G) * (x : G) = (x : G) * (u : G) :=
      X_core_centralizes_U d hI hfit hXI hn (mem_map_of_mem X.subtype hx) u u.property
    rw [← hc, mul_inv_cancel_right])

/-- The binary representation is constructed on Additive U itself. -/
noncomputable def U_representation (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) :
    letI := U_elementary d hI hfit hXI
    Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ⁅V,B⁆)) := by
  let := U_elementary d hI hfit hXI
  let a := U_quotientConjugation d hI hfit hXI hn
  exact {
    toFun g := (a g).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      change Additive.ofMul (a 1 v.toMul) = v
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro v
      change Additive.ofMul (a (g*h) v.toMul) = _
      rw [map_mul]
      rfl }

/-- The action equation uses the original core quotient, with no hidden map. -/
theorem U_representation_apply (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) (x : X) (u : Additive (U X ⁅V,B⁆)) :
    letI := U_elementary d hI hfit hXI
    (((U_representation d hI hfit hXI hn) (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
      (x : G) * (u.toMul : G) * (x : G)⁻¹ := rfl


/-- B.2.14 on the original subgroup, including its literal generating seed. -/
theorem U_seed_generates
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) :
    conjugateSpanBy (U X ⁅V,B⁆ ⊓ ⁅V,B⁆) X = U X ⁅V,B⁆ := by
  let S := planeSylow T ⁅V,B⁆
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right
  let := d.plane_span_elementary hI hfit hXI
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape_for_blocks hI).restrict
    (show S ≤ X ⊔ S from le_sup_right) (sup_le hXI hSI)
  exact conjugateSpanBy_moved_inf_omegaCenter X S ⁅V,B⁆ d.plane_omega_for_blocks
    (hSI.trans hn)
    ((d.plane_span_le_planeParabolicCore hI hfit hXI).trans
      (d.planeParabolicCore_le_plane hI)) P hP

/-- The literal quotient action is generated by the same seed in additive
coordinates. No identification with the star quotient is made. -/
theorem U_seed_module_generates
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    [IsElementaryAbelian 2 (U X ⁅V,B⁆)]
    (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ⁅V,B⁆)))
    (hσ : ∀ (x : X) (u : Additive (U X ⁅V,B⁆)),
      ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
        (x : G) * (u.toMul : G) * (x : G)⁻¹) :
    let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
    (⨆ g : X ⧸ pCore 2 X, Z.map (σ g)) = ⊤ := by
  let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
  let L := ⨆ g : X ⧸ pCore 2 X, Z.map (σ g)
  let C := L.toAddSubgroup.toSubgroup'.map (U X ⁅V,B⁆).subtype
  have hseed : U X ⁅V,B⁆ ⊓ ⁅V,B⁆ ≤ C := by
    intro z hz
    exact ⟨⟨z,hz.1⟩, le_iSup_maps σ Z hz.2, rfl⟩
  have hXC : X ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx c hc
    obtain ⟨u,hu,rfl⟩ := hc
    let v := σ (QuotientGroup.mk' (pCore 2 X) ⟨x,hx⟩) (Additive.ofMul u)
    refine ⟨v.toMul, ?_, hσ ⟨x,hx⟩ (Additive.ofMul u)⟩
    exact (iSup_maps_invariant σ Z (mem_top _) (Additive.ofMul u)).2 hu
  have hUC : U X ⁅V,B⁆ ≤ C :=
    (U_seed_generates d hI hfit hXI hn).ge.trans (conjugateSpanBy_le hseed hXC)
  apply top_unique
  intro v _
  obtain ⟨u,hu,he⟩ := hUC v.toMul.property
  have he' : u = v.toMul := Subtype.ext he
  rw [he'] at hu
  exact hu


/-- The centralizer of the original moved seed is exactly M₁. -/
theorem U_seed_centralizer
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) :
    X ⊓ centralizer ((U X ⁅V,B⁆ ⊓ ⁅V,B⁆ : Subgroup G) : Set G) = M1 X ⁅V,B⁆ := by
  let S := planeSylow T ⁅V,B⁆
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right
  let := d.plane_span_elementary hI hfit hXI
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape_for_blocks hI).restrict
    (show S ≤ X ⊔ S from le_sup_right) (sup_le hXI hSI)
  exact centralizer_moved_omegaCenter_eq X S ⁅V,B⁆ d.plane_omega_for_blocks
    (hSI.trans hn)
    ((d.plane_span_le_planeParabolicCore hI hfit hXI).trans
      (d.planeParabolicCore_le_plane hI)) P hP

/-- The original centralizer maps onto the seed fixer in X/O₂(X). -/
theorem M1_image_eq_seedKernel
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
    ((M1 X ⁅V,B⁆).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) =
      subspaceKernel σ Z ⊤ := by
  let := U_elementary d hI hfit hXI
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 X)
  ext a
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) a
  constructor
  · rintro ⟨y,hy,he⟩
    rw [← he]
    refine ⟨mem_top _, ?_⟩
    intro u hu
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply]
    have hh : (u.toMul : G) * (y : G) = (y : G) * (u.toMul : G) := hy.2 _ hu
    rw [← hh, mul_inv_cancel_right]
  · intro ha
    refine ⟨x, ?_, rfl⟩
    change (x : G) ∈ M1 X ⁅V,B⁆
    rw [← U_seed_centralizer d hI hfit hXI hn]
    refine ⟨x.property, ?_⟩
    intro u hu
    let v : Additive (U X ⁅V,B⁆) := Additive.ofMul ⟨u,hu.1⟩
    have he := congrArg (fun w : Additive (U X ⁅V,B⁆) => (w.toMul : G)) (ha.2 v hu.2)
    rw [U_representation_apply] at he
    change (x : G) * u * (x : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
