module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneResidual
public import Theory.Representation.BinaryConjugationSection.PlaneResidual
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Lifting the original reciprocal-plane cubic

For the actual plane P containing V₁, the relative normalizer in L₁ has
the same two-residual as C_{L₁}(P). The central denominator V₁ causes
only two-group errors, killed by two-perfectness. Transport through the
literal H/O₂(H) map identifies L_Y* with the two-residual of the actual
plane-normalizer image.

On any specified U/V₁ conjugation section, that image is exactly the
subgroup of L₁* fixing the nonzero plane vector. Every cubic in this
fixer lifts to a cubic in L_Y with the same star image. The original
quotient L₁/O₂(L₁) of order three then gives L₁ = L_Y O₂(L₁) and an
actual order-three supplement inside L_Y.

This module gives the conditional lifting and generation step.
BinaryPlaneCubic constructs the fixed cubic in the original exchanged
orthogonal branch and applies this lift to the same Y and I₀. The guarded
whole-branch specialization, later reductions through 14.7.52 and all four
Data inputs retain their original assembly owner.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem star_embedded_residual (A : Subgroup G) (hAH : A ≤ F.H) :
    star F ((pResidual 2 A).map A.subtype) =
      (pResidual 2 (star F A)).map (star F A).subtype := by
  have he : ((pResidual 2 A).map A.subtype).subgroupOf F.H =
      (pResidual 2 (A.subgroupOf F.H)).map (A.subgroupOf F.H).subtype := by
    apply map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hAH),
      map_embedded_pResidual,map_subgroupOf_eq_of_le hAH]
  change (((pResidual 2 A).map A.subtype).subgroupOf F.H).map (starMap F) = _
  rw [he,map_embedded_pResidual]
  rfl

/-- The original plane-centralizer residual equals its relative-normalizer residual. -/
theorem point_plane_residual_eq_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4) :
    (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
        (F.Li L 1 ⊓ centralizer (P : Set G)).subtype =
      (pResidual 2 (F.Li L 1 ⊓ normalizer (P : Set G) : Subgroup G)).map
        (F.Li L 1 ⊓ normalizer (P : Set G)).subtype := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hc : Nat.card (s.imageSpace P) = 2 := by
    rw [s.imageSpace_card_eq_relIndex P hPU]
    have hh := relIndex_mul_card_of_le hZP
    have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hz,hfour] at hh
    omega
  exact (s.residual_normalizer_eq_centralizer (IsElementaryAbelian.isPGroup 2 F.U)
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
    (F.Li L 1) P ((F.Li_le L 1).trans inf_le_right) hPU hc).symm

/-- The literal star map preserves this residual after passing to the plane normalizer. -/
theorem point_plane_residual_star_image
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4) :
    star F ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
        (F.Li L 1 ⊓ centralizer (P : Set G)).subtype) =
      (pResidual 2 (star F (F.Li L 1 ⊓ normalizer (P : Set G)))).map
        (star F (F.Li L 1 ⊓ normalizer (P : Set G))).subtype := by
  rw [point_plane_residual_eq_normalizer h hab P hPU hZP hfour]
  exact star_embedded_residual _ (inf_le_left.trans ((F.Li_le L 1).trans inf_le_right))

omit [Finite G] in
/-- The actual normalizer image is the fixer of the specified nonzero section point. -/
theorem point_plane_star_normalizer_iff
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0) (x : HStar F.H) :
    x ∈ star F (F.Li L 1 ⊓ normalizer (P : Set G)) ↔
      x ∈ star F (F.Li L 1) ∧ σ x w = w := by
  have hc : Nat.card (s.imageSpace P) = 2 := by
    rw [s.imageSpace_card_eq_relIndex P hPU]
    have hh := relIndex_mul_card_of_le hZP
    have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hz,hfour] at hh
    omega
  constructor
  · rintro ⟨g,⟨hg,hgn⟩,rfl⟩
    exact ⟨mem_map_of_mem _ hg,
      (s.mem_normalizer_iff_fixed_of_image_card_two P hPU hZP hc w hw hw0 g).mp hgn⟩
  · rintro ⟨⟨g,hg,rfl⟩,hfix⟩
    exact ⟨g,⟨hg,(s.mem_normalizer_iff_fixed_of_image_card_two P hPU hZP hc w hw hw0 g).mpr hfix⟩,rfl⟩

/-- An actual cubic fixing the quotient plane lifts, with its exact star
image and order, into the literal plane-centralizer residual. -/
theorem point_plane_cubic_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0)
    (x : HStar F.H) (hx : x ∈ star F (F.Li L 1)) (hxw : σ x w = w)
    (hx3 : orderOf x = 3) :
    ∃ l : F.H,
      (l : G) ∈ (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
        (F.Li L 1 ⊓ centralizer (P : Set G)).subtype ∧
      orderOf (l : G) = 3 ∧ starMap F l = x := by
  let C := F.Li L 1 ⊓ centralizer (P : Set G)
  let R := (pResidual 2 C).map C.subtype
  let D := star F (F.Li L 1 ⊓ normalizer (P : Set G))
  have hxD : x ∈ D := (point_plane_star_normalizer_iff σ s P hPU hZP hfour w hw hw0 x).mpr
    ⟨hx,hxw⟩
  have hxR : x ∈ star F R := by
    rw [point_plane_residual_star_image h hab P hPU hZP hfour]
    refine ⟨⟨x,hxD⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    rw [←D.orderOf_coe,hx3]
    decide
  let B := R.subgroupOf F.H
  let q := (starMap F).comp B.subtype
  have hxq : x ∈ q.range := by
    obtain ⟨g,hg,he⟩ := hxR
    exact ⟨⟨g,hg⟩,he⟩
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 ((starMap F).ker.subgroupOf B)
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 F.H)).ker.subgroupOf B)
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let x' : q.range := ⟨x,hxq⟩
  have hx' : orderOf x' = 3 := (q.range.orderOf_coe x').symm.trans hx3
  obtain ⟨l,hlodd,hlx⟩ := q.rangeRestrict.exists_pRegular_lift
    q.rangeRestrict_surjective 2 Nat.prime_two x' (by rw [hx']; decide)
  have hl3 : orderOf l = 3 := by
    have hqo := q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk l
      (Nat.prime_two.coprime_iff_not_dvd.mpr hlodd)
    rw [←hqo,show q l = x from congrArg Subtype.val hlx,hx3]
  exact ⟨l,l.property,(F.H.orderOf_coe l.val).trans ((B.orderOf_coe l).trans hl3),
    congrArg Subtype.val hlx⟩

/-- This discharges the source equality and supplies its actual cubic as
soon as the original orthogonal point stabilizer contains a cubic. The
remaining premise is a concrete model fixed-point calculation. -/
theorem point_plane_residual_core_supplement_of_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0)
    (x : HStar F.H) (hx : x ∈ star F (F.Li L 1)) (hxw : σ x w = w)
    (hx3 : orderOf x = 3) :
    let R := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
      (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
    R ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 ∧
      ∃ l : F.H, (l : G) ∈ R ∧ orderOf (l : G) = 3 ∧ starMap F l = x ∧
        zpowers (l : G) ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 := by
  dsimp only
  obtain ⟨l,hl,hl3,hlx⟩ := point_plane_cubic_lift h hab σ s P hPU hZP hfour w hw hw0 x hx hxw hx3
  let A := F.Li L 1
  let R := (pResidual 2 (A ⊓ centralizer (P : Set G) : Subgroup G)).map
    (A ⊓ centralizer (P : Set G)).subtype
  have hRA : R ≤ A := (map_subtype_le _).trans inf_le_left
  let a : A := ⟨l,hRA hl⟩
  have ha3 : orderOf a = 3 := (A.orderOf_coe a).symm.trans hl3
  let q := QuotientGroup.mk' (pCore 2 A)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hq3 : orderOf (q a) = 3 := (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk a
    (by rw [ha3]; decide)).trans ha3
  have hqn : q a ≠ 1 := by intro he; rw [he,orderOf_one] at hq3; omega
  have hgen : zpowers a ⊔ pCore 2 A = ⊤ := by
    have hh := zpowers_eq_top_of_prime_card (pointResidual_core_quotient_card h structural) hqn
    rw [←MonoidHom.map_zpowers] at hh
    have he := congrArg (Subgroup.comap q) hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he
  have hgenG : zpowers (l : G) ⊔ A.pCoreIn 2 = A := by
    have he := congrArg (Subgroup.map A.subtype) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,
      pCoreIn,a,Subgroup.subtype_apply] using he
  refine ⟨le_antisymm (sup_le hRA (pCoreIn_le 2 A)) ?_,l,hl,hl3,hlx,hgenG⟩
  exact hgenG.ge.trans (sup_le_sup (zpowers_le.mpr hl) le_rfl)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
