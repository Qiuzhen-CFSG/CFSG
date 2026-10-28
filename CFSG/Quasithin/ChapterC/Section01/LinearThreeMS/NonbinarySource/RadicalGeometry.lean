module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCommonActors.FullAxis
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CommonActors
public import Theory.Representation.NormalElementaryQuotient.FixedCore
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalCoordinates
public import Theory.SpecificGroups.PSL3.LinearThreeRootFixed
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.FixedCubic
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Common-axis offenders and the Sylow fixed-space core

A full common-axis subgroup in SL₃ has order q² and fixes a hyperplane;
the point radical has the same order and fixes a line. Thus the former
cannot lie in the latter. On a doubled natural module with a fixed
supplement, the point local fixes the vectors fixed by the standard Sylow.
Normality then forces any fixed-space two-core contained in that Sylow
inside the point radical. Simultaneous conjugation of the component and
both module copies gives the same exclusion for any supplied Sylow.

B.5.1 identifies the genuine best offenders as full common-axis groups.
Consequently a radical containing such an offender cannot equal the
Sylow fixed-space core. This applies at field four too and is consumed
on the actual initial action in RadicalInitial.
Source: Aschbacher--Smith C.1.34(2), printed pp.136--137, especially the
common-axis versus common-center argument in its proof; B.5.1, pp.99--101.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.RadicalGeometry
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterK.Linear.Natural ChapterB.NaturalExtensions.LargerFieldThree
open Matrix.PSL3.LinearThree
variable (F : BinaryField)

private theorem fullAxis_card_cost {A : Subgroup SL(3,F.Carrier)}
    (hA : IsFullAxisGroup F 3 A) :
    Nat.card A = 2^(2*F.degree) ∧ fixedCodim (linearNatural F 3) A = F.degree := by
  obtain ⟨g,hg⟩ := AxisFourGeometry.full_axis_conjugate_standard F hA
  have he := hyperplaneCentralizer_elementary F 3 0 (by decide)
  constructor
  · rw [←card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective (K := A),hg,
      he.card_eq_two_pow_rank,hyperplaneCentralizer_rank]
    congr 1
    omega
  · rw [←fixedCodim_map_conj (linearNatural F 3) A g,hg]
    exact subgroup_fixedCodim F 3 0 le_rfl he.1

private theorem pointRadical_fixed_card :
    Nat.card (fixedSpace (linearNatural F 3)
      ((pointRadicalSL F.Carrier).map (pointLocalSL F.Carrier).subtype)) = 2^F.degree := by
  let e : fixedSpace (linearNatural F 3)
      ((pointRadicalSL F.Carrier).map (pointLocalSL F.Carrier).subtype) ≃ F.Carrier := {
    toFun := fun v => v.val 0
    invFun := fun a => ⟨a • (![1,0,0] : Fin 3 → F.Carrier),by
      intro g
      obtain ⟨x,hx,hxg⟩ := g.property
      change linearNatural F 3 g.val _ = _
      rw [←hxg]
      exact (pointRadicalSL_fixed_iff F.Carrier _).mpr ⟨a,rfl⟩ x hx⟩
    left_inv := by
      intro v
      obtain ⟨a,ha⟩ := (pointRadicalSL_fixed_iff F.Carrier v.val).mp (fun x hx =>
        v.property ⟨x,mem_map_of_mem _ hx⟩)
      apply Subtype.ext
      change (v.val 0) • (![1,0,0] : Fin 3 → F.Carrier) = v.val
      rw [ha]
      simp
    right_inv := by intro a; simp }
  exact (Nat.card_congr e).trans F.card_eq

/-- Full common-axis groups never lie in the point radical, including at field four. -/
theorem fullAxis_not_le_pointRadical {A : Subgroup SL(3,F.Carrier)}
    (hA : IsFullAxisGroup F 3 A) :
    ¬ A ≤ (pointRadicalSL F.Carrier).map (pointLocalSL F.Carrier).subtype := by
  intro hle
  have hcard : Nat.card ((pointRadicalSL F.Carrier).map (pointLocalSL F.Carrier).subtype) =
      2^(2*F.degree) := by
    rw [card_map_of_injective (pointLocalSL F.Carrier).subtype_injective,
      Nat.card_congr (pointRadicalCoordinates F.Carrier).toEquiv]
    change Nat.card (Fin 2 → F.Carrier) = _
    rw [Nat.card_fun,Nat.card_fin,F.card_eq,←pow_mul]
    congr 1
    omega
  have he : A = (pointRadicalSL F.Carrier).map (pointLocalSL F.Carrier).subtype :=
    eq_of_le_of_card_ge hle (hcard.trans (fullAxis_card_cost F hA).1.symm).le
  have hfix := pointRadical_fixed_card F
  rw [←he,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hfix
  have hd := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hfix
  have hs := fixedCodim_add_finrank (linearNatural F 3) A
  rw [(fullAxis_card_cost F hA).2,hd] at hs
  have hv : Module.finrank (ZMod 2) (Fin 3 → F.Carrier) = 3*F.degree := by
    simp [Module.finrank_pi_fintype,field_finrank]
  rw [hv] at hs
  have := F.degree_pos
  omega

/-- In coordinates aligned with the actual component Sylow, its point local
fixes the full Sylow-fixed space, including the component-fixed summand. -/
theorem pointLocal_le_fixer
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (q : SL(3,F.Carrier) →* X)
    (f : (Fin 2 → Fin 3 → F.Carrier) →ₗ[ZMod 2] W) (hf : Function.Injective f)
    (he : ∀ g w, ρ (q g) (f w) = f (repeated (linearNatural F 3) 2 g w))
    (hsplit : f.range ⊔ fixedSpace ρ q.range = ⊤)
    (S : Subgroup X) (hS : S.comap q = unipotentSL F.Carrier) :
    (pointLocalSL F.Carrier).map q ≤ NormalElementaryQuotient.fixedSpaceFixer ρ S := by
  rintro _ ⟨g,hg,rfl⟩
  rw [NormalElementaryQuotient.mem_fixedSpaceFixer]
  intro v hv
  obtain ⟨u,⟨w,rfl⟩,c,hc,rfl⟩ := Submodule.mem_sup.mp
    (hsplit.ge (Submodule.mem_top (x := v)))
  have hcq (a : SL(3,F.Carrier)) : ρ (q a) c = c := hc ⟨q a,⟨a,rfl⟩⟩
  have hfix (a : SL(3,F.Carrier)) (ha : a ∈ unipotentSL F.Carrier) :
      repeated (linearNatural F 3) 2 a w = w := by
    apply hf
    have hs : q a ∈ S := by
      change a ∈ S.comap q
      rwa [hS]
    have hh := hv ⟨q a,hs⟩
    change ρ (q a) (f w+c) = f w+c at hh
    rw [map_add,he,hcq a] at hh
    exact add_right_cancel hh
  have hw : repeated (linearNatural F 3) 2 g w = w := by
    funext i
    apply pointLocalSL_fixes_unipotent_fixed_space g hg (w i)
    intro a
    exact congrFun (hfix a a.property) i
  rw [map_add,he,hw,hcq g]

/-- If the whole fixed-space core lies in the specified Sylow, its component
preimage lies in the point radical. This is the literal core comparison. -/
theorem fixer_core_le_pointRadical
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (q : SL(3,F.Carrier) →* X)
    (hq : Function.Injective q)
    (f : (Fin 2 → Fin 3 → F.Carrier) →ₗ[ZMod 2] W) (hf : Function.Injective f)
    (he : ∀ g w, ρ (q g) (f w) = f (repeated (linearNatural F 3) 2 g w))
    (hsplit : f.range ⊔ fixedSpace ρ q.range = ⊤)
    (S : Subgroup X) (hS : S.comap q = unipotentSL F.Carrier)
    (hcore : (NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2 ≤ S) :
    ((NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2).comap q ≤
      (pointRadicalSL F.Carrier).map (pointLocalSL F.Carrier).subtype := by
  let C := NormalElementaryQuotient.fixedSpaceFixer ρ S
  have hP := pointLocal_le_fixer F ρ q f hf he hsplit S hS
  have hCP : (C.pCoreIn 2).comap q ≤ pointLocalSL F.Carrier := by
    apply (comap_mono hcore).trans
    rw [hS]
    intro g hg
    have hg := (mem_unipotentSL_iff F.Carrier g).mp hg
    rw [mem_pointLocalSL_iff]
    rw [hg]
    exact ⟨rfl,rfl,rfl⟩
  have hn : C ≤ normalizer (C.pCoreIn 2 : Set X) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hnorm : pointLocalSL F.Carrier ≤ normalizer ((C.pCoreIn 2).comap q : Set SL(3,F.Carrier)) :=
    ((map_le_iff_le_comap.mp hP).trans (comap_mono hn)).trans (le_normalizer_comap q)
  have hle := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 C).comap_of_injective q hq) hCP hnorm
  simpa only [Subgroup.pCoreIn,pointLocalSL_twoCore_eq] using hle

/-- A doubled natural Sylow-fixed-space core cannot contain a full common-axis
offender in the aligned component. -/
theorem fullAxis_not_le_fixer_core
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (q : SL(3,F.Carrier) →* X)
    (hq : Function.Injective q)
    (f : (Fin 2 → Fin 3 → F.Carrier) →ₗ[ZMod 2] W) (hf : Function.Injective f)
    (he : ∀ g w, ρ (q g) (f w) = f (repeated (linearNatural F 3) 2 g w))
    (hsplit : f.range ⊔ fixedSpace ρ q.range = ⊤)
    (S : Subgroup X) (hS : S.comap q = unipotentSL F.Carrier)
    (hcore : (NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2 ≤ S)
    {A : Subgroup SL(3,F.Carrier)} (hA : IsFullAxisGroup F 3 A) :
    ¬ A.map q ≤ (NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2 := by
  intro hle
  exact fullAxis_not_le_pointRadical F hA
    ((map_le_iff_le_comap.mp hle).trans
      (fixer_core_le_pointRadical F ρ q hq f hf he hsplit S hS hcore))

/-- The same exclusion for an arbitrary supplied component Sylow. Conjugation
aligns the actor and both natural copies simultaneously. -/
theorem fullAxis_not_le_fixer_core_of_sylow
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (q : SL(3,F.Carrier) →* X)
    (hq : Function.Injective q)
    (f : (Fin 2 → Fin 3 → F.Carrier) →ₗ[ZMod 2] W) (hf : Function.Injective f)
    (he : ∀ g w, ρ (q g) (f w) = f (repeated (linearNatural F 3) 2 g w))
    (hsplit : f.range ⊔ fixedSpace ρ q.range = ⊤)
    (S : Subgroup X) (P : Sylow 2 SL(3,F.Carrier)) (hS : S.comap q = P)
    (hcore : (NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2 ≤ S)
    {A : Subgroup SL(3,F.Carrier)} (hA : IsFullAxisGroup F 3 A) :
    ¬ A.map q ≤ (NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2 := by
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F.Carrier F.degree_pos F.card_eq P
  let τ := repeated (linearNatural F 3) 2
  let q' := q.comp (MulAut.conj g).toMonoidHom
  let f' := f.comp (τ g)
  have hi (w) : τ g⁻¹ (τ g w) = w := inv_self_apply τ g w
  have hi' (w) : τ g (τ g⁻¹ w) = w := self_inv_apply τ g w
  have hf' : Function.Injective f' := by
    intro v w hvw
    have hh := congrArg (τ g⁻¹) (hf hvw)
    simpa only [hi] using hh
  have he' (a) (w) : ρ (q' a) (f' w) = f' (τ a w) := by
    change ρ (q (g*a*g⁻¹)) (f (τ g w)) = f (τ g (τ a w))
    rw [he]
    change f (τ (g*a*g⁻¹) (τ g w)) = _
    simp only [map_mul,Module.End.mul_apply,hi]
  have hr : f'.range = f.range := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact ⟨τ g w,rfl⟩
    · rintro _ ⟨w,rfl⟩
      exact ⟨τ g⁻¹ w,congrArg f (hi' w)⟩
  have hqr : q'.range = q.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective,
      ←MonoidHom.range_eq_map]
  have hs' : S.comap q' = unipotentSL F.Carrier := by
    change (S.comap q).comap (MulAut.conj g).toMonoidHom = _
    rw [hS,←hg,comap_map_eq_self_of_injective (MulAut.conj g).injective]
  let A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  have ha' : IsFullAxisGroup F 3 A' :=
    (doubledThree_bestOffender_iff_fullAxis F A').mp
      (((doubledThree_bestOffender_iff_fullAxis F A).mpr hA).map_conj τ g⁻¹)
  have ham : A'.map q' = A.map q := by
    rw [map_map]
    congr 1
    ext x
    change q (g*(g⁻¹*x*(g⁻¹)⁻¹)*g⁻¹) = q x
    simp [mul_assoc]
  have hh := fullAxis_not_le_fixer_core F ρ q' (hq.comp (MulAut.conj g).injective)
    f' hf' he' (by rw [hr,hqr]; exact hsplit) S hs' hcore ha'
  rwa [ham] at hh

/-- A radical containing an actual best offender on a doubled moved module
cannot be the Sylow-fixed-space core. The component is normal, and the supplied
Sylow is retained throughout the conjugacy calculation. -/
theorem radical_ne_fixerCore_of_double
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (O : Subgroup X) [O.Normal]
    (U : Subrepresentation (ρ.comp O.subtype))
    (a : ActionEquiv U.toRepresentation (repeated (linearNatural F 3) 2))
    (hsplit : U.toSubmodule ⊔ Representation.invariants (ρ.comp O.subtype) = ⊤)
    (S : Sylow 2 X) (R : Subgroup X) (hRS : R ≤ S)
    {A : Subgroup X} (hA : IsBestOffender ρ A) (hAR : A ≤ R) (hAO : A ≤ O) :
    R ≠ (NormalElementaryQuotient.fixedSpaceFixer ρ S).pCoreIn 2 := by
  intro hR
  let q := O.subtype.comp a.groupEquiv.symm.toMonoidHom
  let f := U.toSubmodule.subtype.comp a.linearEquiv.symm.toLinearMap
  have hq : Function.Injective q := O.subtype_injective.comp a.groupEquiv.symm.injective
  have hf : Function.Injective f := U.toSubmodule.subtype_injective.comp a.linearEquiv.symm.injective
  have he (g) (w) : ρ (q g) (f w) = f (repeated (linearNatural F 3) 2 g w) := by
    have hh := a.intertwines (a.groupEquiv.symm g) (a.linearEquiv.symm w)
    rw [a.groupEquiv.apply_symm_apply,a.linearEquiv.apply_symm_apply] at hh
    have hz := congrArg (fun v => (a.linearEquiv.symm v : W)) hh
    simp only [a.linearEquiv.symm_apply_apply] at hz
    exact hz
  have hfr : f.range = U.toSubmodule := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact (a.linearEquiv.symm w).property
    · intro w hw
      exact ⟨a.linearEquiv ⟨w,hw⟩,congrArg Subtype.val (a.linearEquiv.symm_apply_apply ⟨w,hw⟩)⟩
  have hqr : q.range = O := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr a.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal O
  let P' := P.mapSurjective (f := a.groupEquiv.toMonoidHom) a.groupEquiv.surjective
  have hp' : (S : Subgroup X).comap q = (P' : Subgroup SL(3,F.Carrier)) := by
    ext g
    change (a.groupEquiv.symm g : X) ∈ (S : Subgroup X) ↔ _
    change _ ↔ g ∈ (P : Subgroup O).map a.groupEquiv.toMonoidHom
    rw [mem_map_equiv, hP]
    rfl
  let A' := (A.subgroupOf O).map a.groupEquiv.toMonoidHom
  have hbest := bestOffender_on_subrepresentation (ρ.comp O.subtype) U (hA.subgroupOf ρ hAO)
  have haxis : IsFullAxisGroup F 3 A' :=
    (doubledThree_bestOffender_iff_fullAxis F A').mp
      (hbest.map_of_fixedCodim U.toRepresentation _ a.groupEquiv.toMonoidHom a.groupEquiv.injective
        (fixedCodim_map_equivariant U.toRepresentation _ a.groupEquiv.toMonoidHom
          a.linearEquiv a.intertwines))
  have ham : A'.map q = A := by
    rw [map_map]
    have heq : q.comp a.groupEquiv.toMonoidHom = O.subtype := by
      ext g
      exact congrArg Subtype.val (a.groupEquiv.symm_apply_apply g)
    rw [heq,map_subgroupOf_eq_of_le hAO]
  apply fullAxis_not_le_fixer_core_of_sylow F ρ q hq f hf he
    (by rw [hfr,hqr]; exact hsplit) S P' hp' (hR ▸ hRS) haxis
  rwa [ham,←hR]

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.RadicalGeometry
