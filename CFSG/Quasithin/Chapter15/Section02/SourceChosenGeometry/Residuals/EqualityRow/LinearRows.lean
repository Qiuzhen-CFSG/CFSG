module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearModule
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearProductExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.LinearFourExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.Residual

/-!
# Direct equality-row exclusions on the original moved module

The original rank-two residual fixes the generating Sylow-fixed seed of U.
The natural-dual and repeated-natural four-space centralizers have cubic
rank at most one. In repeated-natural degree five the same seed identifies
the original M₁ point parabolic and KI/O₂(KI) with SL₄(2). In the exterior
row it identifies KI/O₂(KI) with C₃ × SL₃(2). Both endpoint quotients
contradict solvable cubic closure in the equality-row partner Mc.

All actions use the literal X/O₂(X) and U = [⟨[V,B]^X⟩,X]. No partner
residual identity, KS quotient, irreducibility packet or terminal callback
is assumed. Source: Aschbacher--Smith 15.2.23(a),(b),(d), pp.1116--1117.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterB.QuasisimpleSource
open Representation.SL5TenDimensional
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ResidualInput hsource H B)

/-- Literal natural-dual exclusion from generation by U∩(⁅V,B⁆ : Subgroup G). Sylow fixation
and K-centralization of that seed follow from the ambient source action.
The B.2.14 generation premise is the remaining recognition input. -/
theorem false_of_naturalDual_generated_on_U
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H B X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : ResidualInput hsource H B)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    [IsElementaryAbelian 2 (U X ⁅V,B⁆)]
    (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ⁅V,B⁆)))
    (hσ : ∀ (x : X) (u : Additive (U X ⁅V,B⁆)),
      ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
        (x : G) * (u.toMul : G) * (x : G)⁻¹)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hnat : IsNaturalPlusDual σ n)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype ≤ planeSylow T ⁅V,B⁆)
    (hgen :
      let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
      (⨆ g : X ⧸ pCore 2 X, Z.map (σ g)) = ⊤) : False := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
  have hfix (x : X) (hc : (x : G) ∈ centralizer ((⁅V,B⁆ : Subgroup G) : Set G))
      (u : Additive (U X ⁅V,B⁆)) (hu : u ∈ Z) : σ (q x) u = u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hc _ hu
    rw [← hh, mul_inv_cancel_right]
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    exact hfix x (hS (mem_map_of_mem X.subtype hx)).2 u hu
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hr : 2 ≤ primeRank 3 A := by
    rw [Theory.GroupTheory.ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact d.residual_rank_two.ge
  apply naturalDual_not_le_seedCentralizer hn hnat P Z hZ hgen A hr
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨mem_top _, hfix x (d.residual_centralizes_plane hx)⟩

/-- The natural-dual row is impossible on the literal quotient action on U.
All geometric alignment and generation conditions are proved internally. -/
theorem false_of_naturalDual_source
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ⁅V,B⁆))),
      (∀ (x : X) (u : Additive (U X ⁅V,B⁆)),
        ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
          (x : G) * (u.toMul : G) * (x : G)⁻¹) →
      ∀ n : ℕ, (n = 4 ∨ n = 5) → IsNaturalPlusDual σ n → False := by
  let := U_elementary d hI hfit hXI
  intro σ hσ n hn' hnat
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape_for_blocks hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  exact false_of_naturalDual_generated_on_U d hKX σ hσ hn' hnat S
    (hS.le.trans inf_le_left) (U_seed_module_generates d hI hfit hXI hn σ hσ)

/-- Source row (b) is excluded on the canonical action, with no action equation
or generating-space premise left for the classification consumer. -/
theorem not_naturalDual_canonical
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)

    (n : ℕ) (hdegree : n = 4 ∨ n = 5) :
    letI := U_elementary d hI hfit hXI
    ¬ IsNaturalPlusDual (U_representation d hI hfit hXI hn) n :=
  false_of_naturalDual_source d hI hfit hXI hn hKX
    (U_representation d hI hfit hXI hn) (U_representation_apply d hI hfit hXI hn) n hdegree

/-- The original U-action cannot be a positive sum of natural four-spaces. -/
theorem not_repeatedNatural_four_canonical
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)

    (r : ℕ) (hr : 0 < r) :
    letI := U_elementary d hI hfit hXI
    ¬ Nonempty (ActionEquiv (U_representation d hI hfit hXI hn)
      (repeated (linearNatural BinaryField.two 4) r)) := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  let σ := U_representation d hI hfit hXI hn
  let q := QuotientGroup.mk' (pCore 2 X)
  let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hA : 2 ≤ primeRank 3 A := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact d.residual_rank_two.ge
  apply repeatedNatural_four_not_le_seedCentralizer σ r hr e Z
    (U_seed_module_generates d hI hfit hXI hn σ
      (U_representation_apply d hI hfit hXI hn)) A hA
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro u hu
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [U_representation_apply]
  have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) :=
    d.residual_centralizes_plane hx _ hu
  rw [← hh, mul_inv_cancel_right]

include d in
/-- In row (a), the image of the literal M₁ is the natural point parabolic. -/
theorem M1_image_pointStabilizer_of_repeatedNatural
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {n r : ℕ} (hdegree : 2 ≤ n) (hr : 0 < r) :
    letI := U_elementary d hI hfit hXI
    ∀ e : ActionEquiv (U_representation d hI hfit hXI hn)
      (repeated (linearNatural BinaryField.two n) r),
    ∃ v : Fin n → ZMod 2, v ≠ 0 ∧
      (((M1 X ⁅V,B⁆).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.groupEquiv.toMonoidHom =
        MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) v := by
  let := U_elementary d hI hfit hXI
  intro e
  let σ := U_representation d hI hfit hXI hn
  let q := QuotientGroup.mk' (pCore 2 X)
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape_for_blocks hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply]
    have hxc : (x : G) ∈ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) :=
      ((hS.le.trans inf_le_left) (mem_map_of_mem X.subtype hx)).2
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hxc _ hu
    rw [← hh, mul_inv_cancel_right]
  rw [M1_image_eq_seedKernel d hI hfit hXI hn]
  exact repeatedNatural_seedKernel σ hdegree hr e P Z hZ
    (U_seed_module_generates d hI hfit hXI hn σ (U_representation_apply d hI hfit hXI hn))

include d in
/-- The image of the original M₁ is the actual 2+3 exterior parabolic. -/
theorem M1_image_parabolic_of_exterior
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    ∀ e : ActionEquiv (U_representation d hI hfit hXI hn) (exteriorAction r),
    ∃ (f : ActionEquiv (U_representation d hI hfit hXI hn) (exteriorAction 2))
      (g : SL5TenDimensional.Group),
      (f.groupEquiv = e.groupEquiv ∨
        f.groupEquiv = e.groupEquiv.trans SL5ExteriorSquare.Duality.graph) ∧
      ((((M1 X ⁅V,B⁆).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        f.groupEquiv.toMonoidHom).map (MulAut.conj g).toMonoidHom =
          SL5ExteriorSquare.parabolic 2 := by
  let := U_elementary d hI hfit hXI
  intro e
  let σ := U_representation d hI hfit hXI hn
  obtain ⟨f,hf⟩ := exterior_square_coordinates σ hr e
  let q := QuotientGroup.mk' (pCore 2 X)
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape_for_blocks hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B⁆ : Subgroup G).subgroupOf (U X ⁅V,B⁆)).toAddSubgroup
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply]
    have hxc : (x : G) ∈ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) :=
      ((hS.le.trans inf_le_left) (mem_map_of_mem X.subtype hx)).2
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hxc _ hu
    rw [← hh,mul_inv_cancel_right]
  obtain ⟨g,hg⟩ := exterior_seedKernel σ f P Z hZ
    (U_seed_module_generates d hI hfit hXI hn σ (U_representation_apply d hI hfit hXI hn))
  refine ⟨f,g,hf,?_⟩
  rw [M1_image_eq_seedKernel d hI hfit hXI hn]
  exact hg

/-- The exterior row constructs the printed C₃ × L₃(2) quotient of KI. -/
theorem KI_quotient_of_exterior
    {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    Nonempty (ActionEquiv (U_representation d hI hfit hXI hn) (SL5TenDimensional.exteriorAction r)) →
    Nonempty ((KI X ⁅V,B⁆ ⧸ pCore 2 (KI X ⁅V,B⁆)) ≃*
      (alternatingGroup (Fin 3) × SL(3,ZMod 2))) := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  obtain ⟨f,g,_,hg⟩ := M1_image_parabolic_of_exterior d hI hfit hXI hn hr e
  let a := f.groupEquiv.trans (MulAut.conj g)
  have hmark : (((M1 X ⁅V,B⁆).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      a.toMonoidHom = SL5ExteriorSquare.parabolic 2 := by
    rw [show a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp f.groupEquiv.toMonoidHom from rfl,
      ← map_map]
    exact hg
  obtain ⟨em⟩ := M1_quotient_of_exterior_image a hmark
  exact ⟨KI_quotientEquiv_residual.trans ((primeToResidualEquiv 3 em).trans
    BinaryLinear.ExteriorParabolic.leviResidualEquiv)⟩

/-- The original degree-five repeated-natural row is excluded by its marked KI quotient. -/
theorem not_repeatedNatural_five_canonical_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (r : ℕ) (hr : 0 < r) :
    letI := U_elementary d hI hfit hXI
    ¬ Nonempty (ActionEquiv (U_representation d hI hfit hXI hn)
      (repeated (linearNatural BinaryField.two 5) r)) := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  obtain ⟨v,hv,hmark⟩ := M1_image_pointStabilizer_of_repeatedNatural
    d hI hfit hXI hn (by decide) hr e
  obtain ⟨a⟩ := KI_quotient_of_point_image e.groupEquiv v hv hmark
  exact d.original_KI_not_linear_four_of_eq he X a

/-- The original exterior row is excluded by its marked C₃ × L₃(2) quotient. -/
theorem not_exteriorFive_canonical_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    ¬ Nonempty (ActionEquiv (U_representation d hI hfit hXI hn)
      (SL5TenDimensional.exteriorAction r)) := by
  let := U_elementary d hI hfit hXI
  intro hrow
  obtain ⟨e⟩ := KI_quotient_of_exterior d hI hfit hXI hn hr hrow
  exact d.original_KI_not_exterior_quotient_of_eq he X e

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
