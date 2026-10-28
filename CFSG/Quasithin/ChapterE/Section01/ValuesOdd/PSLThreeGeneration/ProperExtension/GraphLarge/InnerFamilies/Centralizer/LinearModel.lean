module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.SL3.InvolutionDerived
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer

/-!
# The projective inner-involution centralizer and its perfect core

The full linear centralizer is GL₂. Its determinant kernel is perfect for
|F| > 3, hence is its solvable residual. The projective scalar kernel has
exponent dividing three; its intersection with this SL₂ is trivial because
Z(SL₂) has order two. Thus the projective residual is the actual SL₂.

The centralizer of this residual is cyclic. Central commutators with a
perfect group vanish, so the centralizer lifts through the scalar quotient.
In GL₂ its elements are scalar, since the residual is noncommutative. These
facts supply the marked model inputs for the full graph-extension calculation.

Source: Aschbacher--Smith A.3.21(a), p.55, used in E.1.14(7), p.214;
Asc82a, Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.CentralizerLinearModel
variable (F : Type*) [Field F] [Finite F]

private theorem two_ne_zero (ho : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  intro hz
  have hc := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
  have he := FiniteField.even_card_iff_char_two.mp hc
  rw [← Nat.card_eq_fintype_card] at he
  have hh := Nat.odd_iff.mp ho
  omega

private noncomputable def glResidualEquiv (hlarge : 3 < Nat.card F) :
    solvableResidual (GL (Fin 2) F) ≃* SL(2,F) := by
  let e := SpecialLinearGroup.determinantKernelEquiv (Fin 2) F
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : Group.IsPerfect (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have he : solvableResidual (GL (Fin 2) F) =
      (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker := by
    apply le_antisymm _ (le_solvableResidual_of_isPerfect _)
    exact (solvableResidual_le_derivedSeries 1).trans
      (Abelianization.commutator_subset_ker _)
  exact (MulEquiv.subgroupCongr he).trans e.symm

private noncomputable def slCentralizerResidualEquiv (hlarge : 3 < Nat.card F)
    (t : SL(3,F)) (ht : orderOf t = 2) (h2 : (2 : F) ≠ 0) :
    solvableResidual (centralizer ({t} : Set SL(3,F))) ≃* SL(2,F) :=
  (SL3.involutionCentralizerEquiv F t ht h2).solvableResidualEquiv.trans
    (glResidualEquiv F hlarge)

private theorem projection_residual_injective
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (t : SL(3,F)) (ht : orderOf t = 2) :
    Function.Injective (PSL3.OddInvolutionFixed.centralizerProjection t).solvableResidualMap := by
  let e := slCentralizerResidualEquiv F hlarge t ht (two_ne_zero F ho)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxZ : (x.val : SL(3,F)) ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun y => (y.val : PSL(3,F))) (MonoidHom.mem_ker.mp hx)
  have heZ : e x ∈ center SL(2,F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (Subtype.ext (mem_center_iff.mp hxZ y.val.val)))
  have hcenter : Nat.card (center SL(2,F)) = 2 := by
    simpa only [GorensteinWalter.sl2ProjectiveProjection_ker] using
      GorensteinWalter.sl2ProjectiveProjection_ker_card F ho
  have hx2 : (e x) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨e x, heZ⟩ : center SL(2,F)))
    rw [hcenter] at hh
    exact congrArg Subtype.val hh
  have hx3 : x ^ 3 = 1 := by
    have hd := (orderOf_dvd_natCard (⟨x.val.val, hxZ⟩ : center SL(3,F))).trans
      (SL3.card_center_dvd_three F)
    have hh : (⟨x.val.val, hxZ⟩ : center SL(3,F)) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hd
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : center SL(3,F) => (y : SL(3,F))) hh
  have he3 : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  rw [pow_succ, hx2, one_mul] at he3
  exact mem_bot.mpr (e.injective (he3.trans e.map_one.symm))

/-- The residual of the full projective centralizer retains the entire SL₂ block. -/
theorem projective_residual_equiv
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    Nonempty (solvableResidual (centralizer ({t} : Set PSL(3,F))) ≃* SL(2,F)) := by
  obtain ⟨x, hx, rfl⟩ := PSL3.OddInvolutionFixed.involution_lift t ht
  let f := (PSL3.OddInvolutionFixed.centralizerProjection x).solvableResidualMap
  have hf : Function.Bijective f := ⟨projection_residual_injective F ho hlarge x hx,
    MonoidHom.solvableResidualMap_surjective _
      (PSL3.OddInvolutionFixed.centralizerProjection_surjective x (hx ▸ pow_orderOf_eq_one x))⟩
  exact ⟨(MulEquiv.ofBijective f hf).symm.trans
    (slCentralizerResidualEquiv F hlarge x hx (two_ne_zero F ho))⟩

private theorem cyclic_centralizer_of_cover
    {U V : Type*} [Group U] [Finite U] [Group V] [Finite V]
    (f : U →* V) (hf : Function.Surjective f) (hk : f.ker ≤ center U)
    (e : U ≃* GL (Fin 2) F) (hlarge : 3 < Nat.card F) :
    IsCyclic (centralizer (solvableResidual V : Set V)) := by
  let D := solvableResidual U
  let J := (centralizer (solvableResidual V : Set V)).comap f
  have hJD : ⁅J, D⁆ ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator, map_solvableResidual_eq f hf]
    exact commutator_eq_bot_iff_le_centralizer.mpr (map_comap_le _ _)
  have hJ : J ≤ centralizer (D : Set U) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    apply le_bot_iff.mp
    exact (commutator_mono (hJD.trans hk) le_top).trans_eq
      (commutator_top_right_eq_bot_iff_le_center.mpr le_rfl)
  let R := solvableResidual (GL (Fin 2) F)
  let : IsQuasisimple R := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    hlarge (glResidualEquiv F hlarge)
  let : IsSimpleGroup (R ⧸ center R) := IsQuasisimple.simple
  let : Nontrivial R := (QuotientGroup.mk'_surjective (center R)).nontrivial
  have hscalar : (centralizer (D : Set U)).map e.toMonoidHom ≤
      (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range := by
    apply le_trans _ (GeneralLinearGroup.centralizer_le_scalar_of_noncommutative R
      (Group.IsPerfect.not_isMulCommutative R))
    have hm := map_centralizer_le_centralizer_image (D : Set U) e.toMonoidHom
    rw [← Subgroup.coe_map, map_solvableResidual_eq e.toMonoidHom e.surjective] at hm
    exact hm
  let : IsCyclic (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range :=
    isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hcyc : IsCyclic ((centralizer (D : Set U)).map e.toMonoidHom) := isCyclic_of_le hscalar
  let : IsCyclic (centralizer (D : Set U)) :=
    (e.subgroupMap (centralizer (D : Set U))).isCyclic.mpr hcyc
  let : IsCyclic J := isCyclic_of_le hJ
  exact isCyclic_of_surjective (f.subgroupComap (centralizer (solvableResidual V : Set V)))
    (f.subgroupComap_surjective_of_surjective _ hf)

/-- Inside the projective centralizer, the centralizer of the residual is cyclic. -/
theorem projective_residual_centralizer_cyclic
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    IsCyclic (centralizer (solvableResidual (centralizer ({t} : Set PSL(3,F))) :
      Set (centralizer ({t} : Set PSL(3,F))))) := by
  obtain ⟨x, hx, rfl⟩ := PSL3.OddInvolutionFixed.involution_lift t ht
  apply cyclic_centralizer_of_cover F (PSL3.OddInvolutionFixed.centralizerProjection x)
    (PSL3.OddInvolutionFixed.centralizerProjection_surjective x (hx ▸ pow_orderOf_eq_one x))
    _ (SL3.involutionCentralizerEquiv F x hx (two_ne_zero F ho)) hlarge
  intro y hy
  have hz : (y : SL(3,F)) ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
  rw [mem_center_iff]
  intro z
  exact Subtype.ext (mem_center_iff.mp hz z.val)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.CentralizerLinearModel
