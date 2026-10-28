module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Normal
public import Theory.SpecificGroups.SL2.NoLinearThreeSection
public import Theory.SpecificGroups.Suzuki.SylowSquares
public import Theory.SpecificGroups.PSL3Two.ClassicalSectionObstructions
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSpecialLinear
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ParabolicSixExclusion
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Suzuki sections in the terminal C.2.7 models

A perfect group with actual Suzuki two-core quotient cannot map with
solvable kernel into binary SL₂: the preimage of a Suzuki Sylow is a
two-group, but its quotient contains a nonidentity square. The parabolic
residual maps extend this obstruction to SL₃, Sp₄ and G₂. Their radical
normalizer geometry excludes every large star model. The small models
are bounded by order, and direct divisibility excludes SL₅(2).

The final theorem consumes an actual radical and its normalization by the
original perfect subgroup. Its source consumer constructs both in the
literal C.2.7 star quotient; no full eight-case C.2.7 theorem is assumed.
Source: Aschbacher--Smith, terminal proof of 4.2.5, printed p.610, and
C.2.7, pp.145--147. Suzuki Sylow squares: Huppert--Blackburn III, XI.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.SuzukiModels
variable {B D F : Type*} [Group B] [Finite B] [Group.IsPerfect B] [Group D]
    [Field F] [Finite F] [CharP F 2] {m : ℕ}

private theorem no_linearTwo (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (f : B →* SL(2,F)) [Group.IsSolvable f.ker] : False := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hk := PerfectCoreTwoExtension.solvable_ker_le_core f
  let q := QuotientGroup.mk' (pCore 2 B)
  let S : Sylow 2 (B ⧸ pCore 2 B) := Classical.choice inferInstance
  obtain ⟨x,hx⟩ := suzukiSylow_exists_nontrivial_square hm e S
  let P := (S : Subgroup (B ⧸ pCore 2 B)).comap q
  have hp : IsPGroup 2 P := S.isPGroup'.comap_of_ker_isPGroup q (by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x.val
  have hbP : b ∈ P := by
    change q b ∈ (S : Subgroup (B ⧸ pCore 2 B))
    change q b = x.val at hb
    rw [hb]
    exact x.property
  have hsq := Matrix.SpecialLinearGroup.twoSubgroup_pow_two (P.map f) (hp.map f)
    ⟨f b,mem_map_of_mem f hbP⟩
  have hfb : f (b^2) = 1 := by
    rw [map_pow]
    exact congrArg (P.map f).subtype hsq
  have hqb : q (b^2) = 1 := (QuotientGroup.eq_one_iff _).mpr (hk hfb)
  apply hx
  apply Subtype.ext
  change (x : B ⧸ pCore 2 B)^2 = 1
  simpa only [q,map_pow,hb] using hqb

private theorem no_rankOne_local (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (f : B →* D) [Group.IsSolvable f.ker]
    (r : D →* SL(2,F)) [Group.IsSolvable r.ker] : False := by
  let : Group.IsSolvable (r.comp f).ker := by
    rw [←MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker f r.ker
  exact no_linearTwo hm e (r.comp f)

open Theory.SpecificGroups.SymplecticFour
omit [Finite B] [Finite F] [CharP F 2] in
private theorem perfect_image_local
    (f : B →* Sp F) (W : Submodule F (Vector F)) (hf : f.range ≤ stabilizer W) :
    f.range ≤ determinantKernel W := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact (le_map_solvableResidual_of_isPerfect f.range (stabilizer W) hf).trans
    (determinantKernel_solvableResidual_le W)

private theorem no_symplectic_parabolic (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (f : B →* Sp F) [Group.IsSolvable f.ker]
    (hp : f.range ≤ pointParabolic ∨ f.range ≤ planeParabolic) : False := by
  rcases hp with hp | hp
  · have hl : f.range ≤ pointLocal := perfect_image_local f (point F) hp
    let j := f.codRestrict pointLocal (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let : Group.IsSolvable (pointQuotient (F := F)).ker := by
      rw [pointQuotient_ker]
      let : Group.IsNilpotent (pointRadical (F := F)) :=
        (IsElementaryAbelian.isPGroup 2 _).isNilpotent
      infer_instance
    exact no_rankOne_local hm e j pointQuotient
  · have hl : f.range ≤ planeLocal := perfect_image_local f (plane F) hp
    let j := f.codRestrict planeLocal (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let : Group.IsSolvable (Plane.quotientMap (F := F)).ker := by
      rw [Plane.quotientMap_ker]
      let : Group.IsNilpotent (Plane.radical (F := F)) :=
        (IsElementaryAbelian.isPGroup 2 _).isNilpotent
      infer_instance
    exact no_rankOne_local hm e j Plane.quotientMap


open Atlas.G2 Atlas.G2.LieParabolicSetup
private theorem no_g2_parabolic (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hq : 2 < Nat.card F)
    (f : B →* Model F) [Group.IsSolvable f.ker]
    (hp : f.range ≤ parabolic₁ ∨ f.range ≤ parabolic₂) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hp with hp | hp
  · have hl : f.range ≤ local₁ := by
      rw [←HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict local₁ (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := shortSLHom (F := F)
    let : Group.IsSolvable r.ker := by
      rw [show r.ker = radical₁.subgroupOf local₁ from shortSLHom_ker]
      let : Group.IsNilpotent ((radical₁ (F := F)).subgroupOf local₁) :=
        radical₁_isTwoGroup.comap_subtype.isNilpotent
      infer_instance
    exact no_rankOne_local hm e j r
  · have hl : f.range ≤ local₂ := by
      rw [←HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict local₂ (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := longSLHom (F := F)
    let : Group.IsSolvable r.ker := by
      rw [show r.ker = radical₂.subgroupOf local₂ from longSLHom_ker]
      let : Group.IsNilpotent ((radical₂ (F := F)).subgroupOf local₂) :=
        radical₂_isTwoGroup.comap_subtype.isNilpotent
      infer_instance
    exact no_rankOne_local hm e j r



open Matrix.PSL3.LinearThree in
private theorem no_linearThree_parabolic (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hF : 4 ≤ Nat.card F)
    (f : B →* SL(3,F)) [Group.IsSolvable f.ker]
    (hp : f.range ≤ pointParabolicSL F ∨ f.range ≤ lineParabolicSL F) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hp with hp | hp
  · have hl : f.range ≤ pointLocalSL F := by
      rw [←pointParabolicSL_residual F hF]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict (pointLocalSL F) (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := (pointLocalSLCoreQuotientEquiv F).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (pointLocalSL F)))
    let : Group.IsSolvable r.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ (pointLocalSLCoreQuotientEquiv F).injective,
        QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 (pointLocalSL F)) := pCore_isPGroup.isNilpotent
      infer_instance
    exact no_rankOne_local hm e j r
  · have hl : f.range ≤ lineLocalSL F := by
      rw [←lineParabolicSL_residual F hF]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict (lineLocalSL F) (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := (lineLocalSLCoreQuotientEquiv F).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (lineLocalSL F)))
    let : Group.IsSolvable r.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ (lineLocalSLCoreQuotientEquiv F).injective,
        QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 (lineLocalSL F)) := pCore_isPGroup.isNilpotent
      infer_instance
    exact no_rankOne_local hm e j r

private theorem no_linearThree_subspace (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hF : 4 ≤ Nat.card F)
    (W : Submodule F (Fin 3 → F)) (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    (f : B →* Matrix.HigherLinear.parabolicSL W) [Group.IsSolvable f.ker] : False := by
  rcases Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv W hW hWt with ha | ha
  all_goals obtain ⟨a⟩ := ha
  · let j := (Matrix.PSL3.LinearThree.pointParabolicSL F).subtype.comp (a.toMonoidHom.comp f)
    let : Group.IsSolvable j.ker := by
      dsimp only [j]
      rw [MonoidHom.ker_comp_of_injective _ _ (Matrix.PSL3.LinearThree.pointParabolicSL F).subtype_injective,
        MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    exact no_linearThree_parabolic hm e hF j
      (Or.inl (by rintro _ ⟨x,rfl⟩; exact (a (f x)).property))
  · let j := (Matrix.PSL3.LinearThree.lineParabolicSL F).subtype.comp (a.toMonoidHom.comp f)
    let : Group.IsSolvable j.ker := by
      dsimp only [j]
      rw [MonoidHom.ker_comp_of_injective _ _ (Matrix.PSL3.LinearThree.lineParabolicSL F).subtype_injective,
        MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    exact no_linearThree_parabolic hm e hF j
      (Or.inr (by rintro _ ⟨x,rfl⟩; exact (a (f x)).property))

private theorem no_linearThree_radical (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) (hF : 4 ≤ Nat.card F)
    (U : Subgroup SL(3,F)) (hU : U.IsPRadical 2)
    (f : B →* SL(3,F)) [Group.IsSolvable f.ker]
    (hn : f.range ≤ normalizer (U : Set SL(3,F))) : False := by
  obtain ⟨k,W,hk,_,_,hW,he⟩ :=
    Matrix.HigherLinear.radical_normalizer_eq_partialFlag (by decide : 2 ≤ 3) U hU
  let i : Fin k := ⟨0,hk⟩
  have hf : f.range ≤ Matrix.HigherLinear.parabolicSL (W i) :=
    hn.trans (he.le.trans (iInf_le _ i))
  let j := f.codRestrict _ (fun x => hf ⟨x,rfl⟩)
  have hj : j.ker = f.ker := by ext x; exact Subtype.ext_iff
  let : Group.IsSolvable j.ker := hj.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  exact no_linearThree_subspace hm e hF (W i) (hW i).1 (hW i).2 j

private theorem no_symplectic_radical (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (U : Subgroup (Sp F)) (hU : U.IsPRadical 2)
    (f : B →* Sp F) [Group.IsSolvable f.ker]
    (hn : f.range ≤ normalizer (U : Set (Sp F))) : False := by
  obtain ⟨g,hg⟩ := radical_normalizer_parabolic_cover U hU
  let j := (MulAut.conj g).toMonoidHom.comp f
  let : Group.IsSolvable j.ker := by
    dsimp only [j]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    infer_instance
  have hj : j.range ≤ (normalizer (U : Set (Sp F))).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]; exact map_mono hn
  exact no_symplectic_parabolic hm e j (hg.imp hj.trans hj.trans)

private theorem no_g2_radical (hm : 0 < m)
    (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) (hF : 2 < Nat.card F)
    (U : Subgroup (Model F)) (hU : U.IsPRadical 2)
    (f : B →* Model F) [Group.IsSolvable f.ker]
    (hn : f.range ≤ normalizer (U : Set (Model F))) : False := by
  obtain ⟨g,hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic U hU.1 hU.isPGroup
  let j := (MulAut.conj g).toMonoidHom.comp f
  let : Group.IsSolvable j.ker := by
    dsimp only [j]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    infer_instance
  have hj : j.range ≤ (normalizer (U : Set (Model F))).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]; exact map_mono hn
  exact no_g2_parabolic hm e hF j (hg.imp hj.trans hj.trans)


private theorem no_suzuki_order_dvd_linearFive (hm : 0 < m) :
    ¬ Nat.card (SuzukiMatrixGroup m) ∣ Nat.card SL(5,ZMod 2) := by
  intro hd
  have hGL : Nat.card (GL (Fin 5) (ZMod 2)) = 9999360 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hh := hd.trans (card_dvd_of_injective
    (Matrix.SpecialLinearGroup.toGL : SL(5,ZMod 2) →* GL (Fin 5) (ZMod 2))
    Matrix.SpecialLinearGroup.toGL_injective)
  rw [hGL,suzukiMatrixGroup_card m hm] at hh
  have hd2 : 2 ^ (4*m+2) ∣ 9999360 := by
    apply dvd_trans ?_ hh
    have he : 2 ^ (4*m+2) = (2^(2*m+1))^2 := by
      rw [←pow_mul]; congr 1; omega
    rw [he]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hcop : Nat.Coprime (2^(4*m+2)) 9765 :=
    (by decide : Nat.Coprime 2 9765).pow_left _
  have hb : 2^(4*m+2) ≤ 2^10 := Nat.le_of_dvd (by decide)
    (hcop.dvd_of_dvd_mul_left (by norm_num at hd2 ⊢; exact hd2))
  have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hb
  have hm2 : m ≤ 2 := by omega
  interval_cases m <;> norm_num at hh

theorem no_radical_model {X : Type*} [Group X] [Finite X]
    (hm : 0 < m) (e : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (model : ChapterC.C27Source.StarModels.Model X) (hlarge : 40320 < Nat.card X)
    (U : Subgroup X) (hU : U.IsPRadical 2)
    (f : B →* X) (hf : Function.Injective f)
    (hn : f.range ≤ normalizer (U : Set X)) : False := by
  have hd : Nat.card (SuzukiMatrixGroup m) ∣ Nat.card X := by
    rw [←Nat.card_congr e.toEquiv]
    exact (card_quotient_dvd_card _).trans (card_dvd_of_injective f hf)
  cases model with
  | linearTwo F a =>
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [j.ker_eq_bot (a.injective.comp hf)]; infer_instance
    exact no_linearTwo hm e j
  | linearThree F a =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      by_contra hh
      have hn : F.degree = 1 := by
        have hpos := F.degree_pos
        have hh' : ¬ 2^2 ≤ 2^F.degree := by simpa only [F.card_eq,show (2:ℕ)^2 = 4 by decide] using hh
        have hh'' := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).not.mp hh'
        omega
      have htwo : Nat.card F.Carrier = 2 := by rw [F.card_eq,hn]; norm_num
      have hs := (center SL(3,F.Carrier)).card_mul_index
      rw [index_eq_card,Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,htwo,
        Matrix.PSL3.LinearThree.card_projective,htwo] at hs
      rw [Nat.card_congr a.toEquiv] at hlarge
      norm_num at hs
      omega
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [j.ker_eq_bot (a.injective.comp hf)]; infer_instance
    apply no_linearThree_radical hm e hF (U.map a.toMonoidHom) (hU.map_equiv a) j
    rw [MonoidHom.range_comp,←map_equiv_normalizer_eq]
    exact map_mono hn
  | symplectic F hF a =>
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [j.ker_eq_bot (a.injective.comp hf)]; infer_instance
    apply no_symplectic_radical hm e (U.map a.toMonoidHom) (hU.map_equiv a) j
    rw [MonoidHom.range_comp,←map_equiv_normalizer_eq]
    exact map_mono hn
  | g2 F hF a =>
    have hq : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (show 2^1 < 2^F.degree from Nat.pow_lt_pow_right (by decide) hF)
    let j := a.toMonoidHom.comp f
    let : Group.IsSolvable j.ker := by
      rw [j.ker_eq_bot (a.injective.comp hf)]; infer_instance
    apply no_g2_radical hm e hq (U.map a.toMonoidHom) (hU.map_equiv a) j
    rw [MonoidHom.range_comp,←map_equiv_normalizer_eq]
    exact map_mono hn
  | g2DerivedTwo a =>
    rw [Nat.card_congr a.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hlarge
    norm_num at hlarge
  | alternating n hn a =>
    rw [Nat.card_congr a.toEquiv] at hlarge
    rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] at hlarge <;>
      norm_num [Nat.factorial] at hlarge
  | linearFiveTwo a =>
    rw [Nat.card_congr a.toEquiv] at hd
    exact no_suzuki_order_dvd_linearFive hm hd
  | tripleSix ez a =>
    rw [card_eq_card_quotient_mul_card_subgroup (center X),Nat.card_congr a.toEquiv,
      Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hlarge
    norm_num [Nat.factorial] at hlarge

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.SuzukiModels
