module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Perfect
public import Theory.GroupTheory.CentralBinaryInvolutionLift
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent

/-!
# The full parabolic core is its commutator with the parabolic

Modulo [R,P], the elementary two-core is central and the perfect quotient
covers SL₂(4). Its involutions lift to involutions. Central Sylow transfer
then kills that central binary kernel. The actual parabolic supplies all
these inputs, including perfectness, through its original covering map.

Source: Aschbacher--Smith I.2.2(3b), printed pp.409--410.
-/

public section
open Subgroup
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3Four.ElementaryParabolic
variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

theorem affine_core_commutator
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) [IsElementaryAbelian 2 (pCore 2 L)]
    (hlift : ∀x:L, (f x)^2=1 → x^2=1) :
    ⁅pCore 2 L, (⊤ : Subgroup L)⁆ = pCore 2 L := by
  let R := pCore 2 L
  let D := ⁅R,(⊤ : Subgroup L)⁆
  let g : L →* SL(2,F) := SemidirectProduct.rightHom.comp f
  have hg : Function.Surjective g := SemidirectProduct.rightHom_surjective.comp hf
  have hgker : g.ker = R := by
    change (Matrix.SL2.translations F).comap f = R
    rw [← Matrix.SL2.affine_twoCore_eq]
    exact f.comap_pCore_of_ker_isPGroup hf hk
  have hDR : D ≤ R := commutator_le_left _ _
  let q : L ⧸ D →* SL(2,F) := QuotientGroup.lift D g (hDR.trans hgker.ge)
  let π := QuotientGroup.mk' D
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective D g hg _
  have hqker : q.ker = R.map π := by rw [QuotientGroup.ker_lift,hgker]
  have hcentral : q.ker ≤ center (L ⧸ D) := by
    rw [hqker]
    rintro _ ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      change π y * π x = π x * π y
      symm
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (commutator_mem_commutator hx (mem_top y))
  let : IsElementaryAbelian 2 q.ker := hqker.symm ▸ IsElementaryAbelian.map π
  let : Group.IsPerfect (L ⧸ D) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective D)
  have hzero : q.ker = ⊥ := by
    apply CentralBinaryInvolutionLift.kernel_eq_bot q perfect_twoPerfect hcentral
    · intro P x
      let B := (P : Subgroup (L ⧸ D)).map q
      have hh := Matrix.SpecialLinearGroup.twoSubgroup_pow_two B (P.isPGroup'.map q)
        ⟨q x,mem_map_of_mem q x.property⟩
      exact congrArg Subtype.val hh
    · intro a ha
      obtain ⟨x,hx⟩ := hf (SemidirectProduct.inr a)
      have hs : x^2=1 := hlift x (by rw [hx,← map_pow,ha,map_one])
      refine ⟨π x, by rw [← map_pow,hs,map_one], ?_⟩
      change (f x).right = a
      rw [hx]
      rfl
  apply le_antisymm hDR
  intro x hx
  have hh : π x ∈ q.ker := hqker.symm ▸ mem_map_of_mem π hx
  rw [hzero,mem_bot] at hh
  exact (QuotientGroup.eq_one_iff x).mp hh

/-- The source full-parabolic commutator identity, with no local perfectness premise. -/
theorem parabolicCore_commutator
    (f : L →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center L) (hs : ∀z ∈ f.ker, z ^ 2 = 1) (b : Bool) :
    ⁅pCore 2 (liftedParabolic f b), (⊤ : Subgroup (liftedParabolic f b))⁆ =
      pCore 2 (liftedParabolic f b) := by
  have hk : IsPGroup 2 f.ker := fun z => ⟨1, by simpa using Subtype.ext (hs z z.property)⟩
  let := parabolic_isPerfect f hf hc hk b
  let := parabolicCore_elementary f hf hc hs b
  have hpk : IsPGroup 2 (parabolicAffine f b).ker := by
    rw [parabolicAffine_ker]
    exact hk.comap_of_injective _ (liftedParabolic f b).subtype_injective
  apply affine_core_commutator (parabolicAffine f b) (parabolicAffine_surjective f hf b) hpk
  intro x hx
  change (localAffine b ⟨f x.val,_⟩) ^ 2 = 1 at hx
  have hh : (⟨f x.val,_⟩ : Matrix.PSL3.LinearThree.OuterExtensions.localFactor F b) ^ 2 = 1 :=
    (localAffine b).injective (by simpa only [map_pow,map_one] using hx)
  have hq : (f x.val) ^ 2 = 1 := congrArg Subtype.val hh
  exact Subtype.ext
    (ExtendedCentralizer.CoverCentralizers.CentralTwist.square_eq_one_of_elementary_kernel
      f hf hc hs x.val hq)

/-- I.2.2(3b)'s local conclusions for the original central quotient and P. -/
theorem source_parabolic_core
    (e : (L ⧸ center L) ≃* PSL)
    (hz : IsPGroup 2 (center L)) (hphi : frattini (center L) = ⊥) (b : Bool) :
    let P := liftedParabolic (centerProjection e) b
    IsElementaryAbelian 2 (pCore 2 P) ∧ frattini (pCore 2 P) = ⊥ ∧
      ⁅pCore 2 P, (⊤ : Subgroup P)⁆ = pCore 2 P := by
  let : Fact (IsPGroup 2 (center L)) := ⟨hz⟩
  let : IsElementaryAbelian 2 (center L) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  have hc : (centerProjection e).ker ≤ center L := by rw [centerProjection_ker]
  have hs (z : L) (hz : z ∈ (centerProjection e).ker) : z ^ 2 = 1 := by
    rw [centerProjection_ker] at hz
    exact elemPow_eq_one_of_isElementaryAbelian z hz
  exact ⟨parabolicCore_elementary _ (centerProjection_surjective e) hc hs b,
    source_parabolicCore_frattini e hz hphi b,
    parabolicCore_commutator _ (centerProjection_surjective e) hc hs b⟩

end Matrix.PSL3Four.ElementaryParabolic

