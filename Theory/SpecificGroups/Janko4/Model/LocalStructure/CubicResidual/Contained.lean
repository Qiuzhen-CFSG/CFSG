module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual
public import Theory.GroupTheory.SolvableResidual.PrimeLift

/-!
# The cubic lies in its full simultaneous-centralizer residual

The native simultaneous centralizer projects onto the perfect triple cover
of M₂₂ with two-group kernel. Its marked scalar lift therefore lies in the
perfect residual. The same membership lifts through every specified central
cover with three-free kernel. The resulting M₂₂ covering residual contains
the original cubic, with the central quotient map unchanged.

This supplies a central cubic for the containing component in the full
cubic centralizer. It does not identify that full centralizer residual.
Source: Aschbacher--Smith 4.2.13, printed p.612. The imported native model
retains the ATLAS action matrices and their original attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace Janko4.InvolutionCentralizers.First.CubicResidual
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreLinearModel TwoCoreComparison QuotientExtension Sporadic.Mathieu
attribute [local irreducible] modelGroup matrixA matrixB involutionCentralizer involutionTwoCore
  actionGroup derivedGroup scalarUnit

/-- The scalar lift belongs to the perfect residual of its simultaneous centralizer. -/
theorem scalar_lift_mem_residual (x : centralizer) (ho : orderOf x = 3)
    (hx : centralizerExtension.rightHom x = scalarElement) :
    (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set centralizer)) ∈
      solvableResidual (Subgroup.centralizer ({x} : Set centralizer)) := by
  let C := Subgroup.centralizer ({x} : Set centralizer)
  let f := scalarCentralizerProjection x ho hx
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    let j : f.ker →* pCore 2 centralizer := {
      toFun c := ⟨c.val.val,by
        change c.val.val ∈ Q
        rw [←centralizerProjection_ker]
        change centralizerExtension.rightHom c.val.val = 1
        have hh := congrArg coverInclusion c.property
        exact (scalarCentralizerProjection_inclusion x ho hx c.val).symm.trans
          (hh.trans (map_one _))⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hi : Function.Injective j := by
      intro c d h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 centralizer => (z : centralizer)) h))
    apply Nat.Coprime.of_dvd_right (card_dvd_of_injective j hi)
    rw [centralizer_twoCore_card]
    norm_num
  exact mem_solvableResidual_of_image_of_coprime_order f
    (scalarCentralizerProjection_surjective x ho hx) hker
    ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩
    ((orderOf_coe (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : C)).symm.trans ho) (by rw [solvableResidual_eq_top]; trivial)

private theorem exists_prime_lift {G Y : Type*} [Group G] [Finite G] [Group Y]
    (f : G →* Y) (hf : Function.Surjective f)
    {p : ℕ} [Fact p.Prime] (hk : Nat.Coprime p (Nat.card f.ker))
    (y : Y) (hy : orderOf y = p) : ∃ x : G, orderOf x = p ∧ f x = y := by
  have hp : IsPGroup p (zpowers y) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers, pow_one] using hy)
  obtain ⟨A,hA,⟨e⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime f hf hk
    (zpowers y) hp
  have hAp : IsPGroup p A := hp.of_equiv e.symm
  have hi := injective_comp_subtype_of_coprime_ker f hk A hAp
  obtain ⟨x,hx,hxy⟩ := hA.symm ▸ (mem_zpowers y)
  exact ⟨x,(orderOf_coe (⟨x,hx⟩ : A)).trans
    ((orderOf_injective (f.comp A.subtype) hi ⟨x,hx⟩).symm.trans (hxy ▸ hy)),hxy⟩

private def residualCentralCover {U Y : Type*} [Group U] [Finite U] [Group Y]
    (f : U →* Y) (hf : Function.Surjective f) (hk : f.ker ≤ center U) :
    PerfectCentralCovering.Cover (solvableResidual U) (solvableResidual Y) where
  toMonoidHom := (MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)).toMonoidHom.comp
    (f.subgroupMap (solvableResidual U))
  surjective := (MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)).surjective.comp
    (f.subgroupMap_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    have hfx : f (x : U) = 1 := congrArg (fun y : solvableResidual Y => (y : Y)) hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hk hfx) y))

/-- The same cubic residual is constructed in any full central cover with
three-free kernel, using the inverse image of the literal C_J₄(a). -/
theorem exists_cubic_residual_containing_lift_of_central_cover {U : Type*} [Group U] [Finite U]
    (f : U →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center U)
    (hthree : Nat.Coprime 3 (Nat.card f.ker)) :
    let R := centralizer.comap f
    ∃ x : R, orderOf x = 3 ∧
      orderOf (f (x : U)) = 3 ∧
      (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({x} : Set R)) ∈
          solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
      IsQuasisimple (solvableResidual (Subgroup.centralizer ({x} : Set R))) ∧
      Nonempty (((solvableResidual (Subgroup.centralizer ({x} : Set R))) ⧸
        center (solvableResidual (Subgroup.centralizer ({x} : Set R)))) ≃* M22) := by
  let R := centralizer.comap f
  let q : R →* centralizer := f.subgroupComap centralizer
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have hqker : Nat.Coprime 3 (Nat.card q.ker) := by
    let j : q.ker →* f.ker := {
      toFun x := ⟨x.val.val,congrArg centralizer.subtype x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact hthree.of_dvd_right (card_dvd_of_injective j
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : U)) h))))
  have hqcentral : q.ker ≤ center R := by
    intro x hx
    have hx' : f (x : U) = 1 := congrArg centralizer.subtype hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hk hx') y))
  obtain ⟨t,ht,hts⟩ := exists_scalar_lift
  obtain ⟨x,hx,hxt⟩ := exists_prime_lift q hq hqker t ht
  let C := Subgroup.centralizer ({x} : Set R)
  let D := Subgroup.centralizer ({t} : Set centralizer)
  have hC : C.map q = D := by
    have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
      (by simpa only [Nat.card_zpowers,pow_one] using hx)
    have hh := centralizer_map_of_prime_free_kernel q hq
      (Nat.prime_three.coprime_iff_not_dvd.mp hqker) (zpowers x) hp
    rw [MonoidHom.map_zpowers,hxt,zpowers_eq_closure,centralizer_closure,
      zpowers_eq_closure,centralizer_closure] at hh
    exact hh
  let g : C →* D := (MulEquiv.subgroupCongr hC).toMonoidHom.comp (q.subgroupMap C)
  have hg : Function.Surjective g := (MulEquiv.subgroupCongr hC).surjective.comp
    (q.subgroupMap_surjective _)
  have hgker : g.ker ≤ center C := by
    intro c hc
    have hc' : q (c : R) = 1 := congrArg D.subtype hc
    exact mem_center_iff.mpr (fun d => Subtype.ext (mem_center_iff.mp (hqcentral hc') d))
  obtain ⟨hD,⟨eD⟩⟩ := scalar_lift_residual_quasisimple t ht hts
  let := hD
  let cov := residualCentralCover g hg hgker
  have hgthree : Nat.Coprime 3 (Nat.card g.ker) := by
    let j : g.ker →* q.ker := {
      toFun c := ⟨c.val.val,congrArg D.subtype c.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact hqker.of_dvd_right (card_dvd_of_injective j
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => (z : R)) h))))
  have hgres : g ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ ∈ solvableResidual D := by
    have he : g ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ =
        (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : D) := Subtype.ext hxt
    rw [he]
    exact scalar_lift_mem_residual t ht hts
  have hres := mem_solvableResidual_of_image_of_coprime_order g hg hgthree
    ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ ((orderOf_coe (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : C)).symm.trans hx) hgres
  refine ⟨x,hx,?_,hres,cov.isQuasisimple,⟨cov.quotientCenterEquiv.trans eD⟩⟩
  have he := congrArg centralizer.subtype hxt
  exact he ▸ (orderOf_coe t).trans ht

end Janko4.InvolutionCentralizers.First.CubicResidual
