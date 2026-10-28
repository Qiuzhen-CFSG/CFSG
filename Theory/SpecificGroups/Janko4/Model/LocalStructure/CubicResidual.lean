module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First
public import Theory.GroupAction.PrimeGroupFixedImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.SolvableResidual

/-!
# A cubic M₂₂ residual on the full J₄ covering component

Lift the marked scalar of order three in C_J₄(a)/O₂(C_J₄(a)). Its certified
matrix action has no fixed vector on the extraspecial core modulo its center.
Coprime fixed-point lifting identifies its simultaneous centralizer image
with the actual triple cover of M₂₂; the kernel is central. Consequently
the perfect residual is quasisimple with central quotient the native M₂₂.

The same construction lifts through a specified central cover of J₄ whose
kernel has order prime to three. All centralizers and residuals use that
projection and its full preimages. The result concerns the simultaneous
centralizer inside the preimage of C_J₄(a); it does not identify the entire
cubic centralizer in J₄ or prove the ambient pushing-up uniqueness argument.

Source: the cubic-residual step of Aschbacher--Smith 4.2.13, printed p.612.
The underlying ATLAS action matrices and their attribution are retained in
the imported first-centralizer and triple-cover developments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Matrix IsMulCommutative
namespace Janko4.InvolutionCentralizers.First.CubicResidual
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreLinearModel TwoCoreComparison QuotientExtension Sporadic.Mathieu
attribute [local irreducible] modelGroup matrixA matrixB
  involutionCentralizer involutionTwoCore actionGroup derivedGroup scalarUnit

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

/-- An actual cubic element in C(a), mapping to the marked scalar. -/
theorem exists_scalar_lift : ∃ x : centralizer,
    orderOf x = 3 ∧ centralizerExtension.rightHom x = scalarElement := by
  apply exists_prime_lift centralizerExtension.rightHom
    centralizerExtension.rightHom_surjective _ scalarElement scalarElement_order
  rw [centralizerProjection_ker,centralizer_twoCore_card]
  norm_num

private theorem scalar_fixed_vector (v : Vector)
    (h : (scalarUnit : Matrix12) *ᵥ v = v) : v = 0 := by
  rw [coe_scalarUnit,Matrix.add_mulVec,Matrix.one_mulVec] at h
  have hj : matrixJ *ᵥ v = 0 := add_left_cancel (h.trans (add_zero v).symm)
  have hinv : (1 + matrixJ : Matrix12) * matrixJ = 1 := by decide +kernel
  have hz := congrArg (fun w => (1 + matrixJ : Matrix12) *ᵥ w) hj
  simpa only [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec,Matrix.mulVec_zero] using hz

private theorem vector_zero_mem_center (q : involutionTwoCore)
    (hq : vector actionGenerators.coordinates q = 0) : q ∈ center involutionTwoCore := by
  apply (QuotientGroup.eq_one_iff q).mp
  apply actionGenerators.coordinates.injective
  rw [map_one]
  exact congrArg Multiplicative.ofAdd hq

/-- The marked scalar fixes only the center of the extraspecial two-core. -/
theorem scalar_lift_core_fixed (x : centralizer)
    (hx : centralizerExtension.rightHom x = scalarElement)
    (q : pCore 2 centralizer) (hc : (q : centralizer) * x = x * q) :
    q ∈ center (pCore 2 centralizer) := by
  let x' := centralizerEquiv x
  let q' := twoCoreEquiv q
  have hact : involutionTwoCoreAction x' q' = q' := by
    apply Subtype.ext
    change x' * (q' : involutionCentralizer) * x'⁻¹ = q'
    rw [show (q' : involutionCentralizer) = centralizerEquiv (q : centralizer) from twoCoreEquiv_coe q]
    have hh := congrArg centralizerEquiv hc
    simp only [map_mul] at hh
    rw [←hh,mul_inv_cancel_right]
  have hx' : quotientAction x' = scalarUnit := by
    have he := congrArg (fun a : actionGroup => (a : Matrix12ˣ)) hx
    rw [centralizerExtension_rightHom] at he
    exact (quotientEquiv_mk x).symm.trans he
  have hv := quotientAction_apply x' q'
  rw [hx',hact] at hv
  have hq' := vector_zero_mem_center q' (scalar_fixed_vector _ hv)
  apply mem_center_iff.mpr
  intro r
  apply twoCoreEquiv.injective
  simpa only [map_mul] using mem_center_iff.mp hq' (twoCoreEquiv r)

private theorem scalar_centralizer :
    Subgroup.centralizer ({scalarElement} : Set actionGroup) = coverSubgroup := by
  have hle : coverSubgroup ≤ Subgroup.centralizer ({scalarElement} : Set actionGroup) := by
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change g.val * scalarUnit = scalarUnit * g.val
    let u : M22TripleCover := ⟨g.val,hg⟩
    have hu : u * M22TripleCover.scalar = M22TripleCover.scalar * u :=
      mem_center_iff.mp M22TripleCover.scalar_mem_center u
    exact congrArg M22TripleCover.subtype hu
  apply le_antisymm _ hle
  have hindex : (Subgroup.centralizer ({scalarElement} : Set actionGroup)).index ∣ 2 := by
    simpa only [coverSubgroup_index] using index_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).mp hindex with he | he
  · have ht := index_eq_one.mp he
    have hc := mem_centralizer_singleton_iff.mp (ht ▸ mem_top outerElement)
    exact (outerElement_moves_scalar (by rw [hc,mul_inv_cancel_right])).elim
  · by_contra hn
    have hh := index_strictAnti (lt_of_le_not_ge hle hn)
    rw [he,coverSubgroup_index] at hh
    omega

/-- The literal cubic centralizer maps onto the actual perfect triple cover. -/
theorem scalar_lift_centralizer_image (x : centralizer) (ho : orderOf x = 3)
    (hx : centralizerExtension.rightHom x = scalarElement) :
    (Subgroup.centralizer ({x} : Set centralizer)).map centralizerExtension.rightHom =
      coverSubgroup := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using ho)
  have hk : ¬ 3 ∣ Nat.card centralizerExtension.rightHom.ker := by
    rw [centralizerProjection_ker,centralizer_twoCore_card]
    norm_num
  have hh := centralizer_map_of_prime_free_kernel centralizerExtension.rightHom
    centralizerExtension.rightHom_surjective hk (zpowers x) hp
  rw [MonoidHom.map_zpowers,hx] at hh
  rw [zpowers_eq_closure,centralizer_closure,zpowers_eq_closure,centralizer_closure,
    scalar_centralizer] at hh
  exact hh


private theorem core_center_central (q : pCore 2 centralizer)
    (hq : q ∈ center (pCore 2 centralizer)) : (q : centralizer) ∈ center centralizer := by
  have he : twoCoreEquiv q ∈ center involutionTwoCore := by
    apply mem_center_iff.mpr
    intro r
    obtain ⟨r,rfl⟩ := twoCoreEquiv.surjective r
    simpa only [map_mul] using congrArg twoCoreEquiv (mem_center_iff.mp hq r)
  have hh : (twoCoreEquiv q : involutionCentralizer) ∈ center involutionCentralizer := by
    rw [matrixCentralizer_center,←twoCore_centralizer]
    intro r hr
    let u : involutionTwoCore := ⟨r,hr⟩
    have hu : u * twoCoreEquiv q = twoCoreEquiv q * u := mem_center_iff.mp he u
    have hu' := congrArg involutionTwoCore.subtype hu
    simp only [map_mul] at hu'
    exact hu'
  rw [twoCoreEquiv_coe] at hh
  apply mem_center_iff.mpr
  intro r
  apply centralizerEquiv.injective
  simpa only [map_mul] using mem_center_iff.mp hh (centralizerEquiv r)

/-- The literal scalar-centralizer projection, retaining the full triple cover. -/
def scalarCentralizerProjection (x : centralizer)
    (ho : orderOf x = 3) (hx : centralizerExtension.rightHom x = scalarElement) :
    Subgroup.centralizer ({x} : Set centralizer) →* M22TripleCover :=
  (subgroupOfEquivOfLe derivedGroup_le_actionGroup).toMonoidHom.comp
    ((MulEquiv.subgroupCongr (scalar_lift_centralizer_image x ho hx)).toMonoidHom.comp
      (centralizerExtension.rightHom.subgroupMap (Subgroup.centralizer ({x} : Set centralizer))))

theorem scalarCentralizerProjection_surjective (x : centralizer)
    (ho : orderOf x = 3) (hx : centralizerExtension.rightHom x = scalarElement) :
    Function.Surjective (scalarCentralizerProjection x ho hx) :=
  (subgroupOfEquivOfLe derivedGroup_le_actionGroup).surjective.comp
    ((MulEquiv.subgroupCongr (scalar_lift_centralizer_image x ho hx)).surjective.comp
      (centralizerExtension.rightHom.subgroupMap_surjective _))

@[simp] theorem scalarCentralizerProjection_inclusion (x : centralizer)
    (ho : orderOf x = 3) (hx : centralizerExtension.rightHom x = scalarElement)
    (c : Subgroup.centralizer ({x} : Set centralizer)) :
    coverInclusion (scalarCentralizerProjection x ho hx c) = centralizerExtension.rightHom c := by rfl

theorem scalarCentralizerProjection_central_kernel (x : centralizer)
    (ho : orderOf x = 3) (hx : centralizerExtension.rightHom x = scalarElement) :
    (scalarCentralizerProjection x ho hx).ker ≤
      center (Subgroup.centralizer ({x} : Set centralizer)) := by
  intro c hc
  have hq : (c : centralizer) ∈ pCore 2 centralizer := by
    change (c : centralizer) ∈ Q
    rw [←centralizerProjection_ker]
    have he := congrArg coverInclusion hc
    exact show centralizerExtension.rightHom c = 1 from
      (scalarCentralizerProjection_inclusion x ho hx c).symm.trans
        (he.trans (map_one coverInclusion))
  have hcentral := core_center_central ⟨c,hq⟩
    (scalar_lift_core_fixed x hx ⟨c,hq⟩ (mem_centralizer_singleton_iff.mp c.property))
  exact mem_center_iff.mpr (fun d => Subtype.ext (mem_center_iff.mp hcentral d))

/-- The perfect residual of the simultaneous centralizer is a genuine M₂₂ cover.
Its projection is the restriction of the literal first-centralizer quotient. -/
theorem scalar_lift_residual_quasisimple (x : centralizer)
    (ho : orderOf x = 3) (hx : centralizerExtension.rightHom x = scalarElement) :
    let C := Subgroup.centralizer ({x} : Set centralizer)
    IsQuasisimple (solvableResidual C) ∧
      Nonempty (((solvableResidual C) ⧸ center (solvableResidual C)) ≃* M22) := by
  let C := Subgroup.centralizer ({x} : Set centralizer)
  let f := scalarCentralizerProjection x ho hx
  have hf := scalarCentralizerProjection_surjective x ho hx
  have hm : (solvableResidual C).map f = ⊤ := by
    rw [map_solvableResidual_eq f hf,solvableResidual_eq_top]
  let g := f.comp (solvableResidual C).subtype
  have hg : Function.Surjective g := MonoidHom.range_eq_top.mp (by
    rw [MonoidHom.range_comp,range_subtype,hm])
  have hk : g.ker ≤ center (solvableResidual C) := by
    intro r hr
    have hc := scalarCentralizerProjection_central_kernel x ho hx hr
    exact mem_center_iff.mpr (fun s => Subtype.ext (mem_center_iff.mp hc s))
  let cover : PerfectCentralCovering.Cover (solvableResidual C) M22TripleCover :=
    { toMonoidHom := g, surjective := hg, isPerfect := inferInstance, ker_le_center := hk }
  exact ⟨cover.isQuasisimple,⟨cover.quotientCenterEquiv.trans M22TripleCover.centralQuotientEquiv⟩⟩


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
theorem exists_cubic_residual_of_central_cover {U : Type*} [Group U] [Finite U]
    (f : U →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center U)
    (hthree : Nat.Coprime 3 (Nat.card f.ker)) :
    let R := centralizer.comap f
    ∃ x : R, orderOf x = 3 ∧
      orderOf (f (x : U)) = 3 ∧
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
  refine ⟨x,hx,?_,cov.isQuasisimple,⟨cov.quotientCenterEquiv.trans eD⟩⟩
  have he := congrArg centralizer.subtype hxt
  exact he ▸ (orderOf_coe t).trans ht

end Janko4.InvolutionCentralizers.First.CubicResidual

