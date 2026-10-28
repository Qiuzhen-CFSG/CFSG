module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.BinaryFive
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalPermutation

/-!
# Four-dimensional moved sections in the quintic comparison

An inner action on the centerless star component determines the action on the
whole star group. The nontrivial intersection of its radical image with the
actual offender group is consequently normalized by an element whose order is
divisible by five. A faithful four-dimensional moved action embeds this pair
in GL₄(2), contradicting the checked two-local normalizer obstruction.

This applies to the marked A₅ and binary symplectic rows, even when the
radical image is outer. The remaining rows, exchanged module geometry and
p=3 assembly stay with qt-e-14615-quintic-exclusion; earlier 14.6.12--14 stay
with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed p.1035, using B.5.1 and C.2.7.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))


private theorem fixed_on_self_centralizing_normal {D : Type*} [Group D] (C : Subgroup D) [C.Normal]
    (hc : centralizer (C : Set D) = ⊥) (α : MulAut D)
    (ha : ∀ c : C, α c = c) : α = 1 := by
  apply MulEquiv.ext
  intro y
  have hy : y⁻¹ * α y ∈ centralizer (C : Set D) := by
    intro c hC
    have hmem : y * c * y⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem c hC y
    have hh := ha ⟨y * c * y⁻¹,hmem⟩
    simp only [map_mul,map_inv,ha ⟨c,hC⟩] at hh
    calc
      c * (y⁻¹ * α y) = y⁻¹ * (y * c * y⁻¹) * α y := by group
      _ = y⁻¹ * (α y * c * (α y)⁻¹) * α y := by rw [hh]
      _ = (y⁻¹ * α y) * c := by group
  rw [hc,mem_bot] at hy
  exact (inv_mul_eq_one.mp hy).symm

private theorem inner_on_self_centralizing {D : Type*} [Group D]
    (C : Subgroup D) [C.Normal] (hc : centralizer (C : Set D) = ⊥)
    (α : MulAut D) (x : C) (ha : ∀ c : C, α c = (x : D) * c * (x : D)⁻¹) :
    α = MulAut.conj (x : D) := by
  have hb : (MulAut.conj (x : D))⁻¹ * α = 1 := by
    apply fixed_on_self_centralizing_normal C hc
    intro c
    change (x : D)⁻¹ * α c * (x : D) = c
    rw [ha]
    group
  exact (inv_mul_eq_one.mp hb).symm

private theorem four_dimensional_normalizer_obstruction {D : Type*} [Group D] [Finite D]
    (O U : Subgroup D) (hQ : IsPGroup 2 (U.subgroupOf O)) (hne : U.subgroupOf O ≠ ⊥)
    (y : O) (hyN : (y : D) ∈ normalizer (U : Set D)) (h5 : 5 ∣ orderOf y)
    (f : O →* BinaryLinear.OuterCyclic.LinearGroup 4) (hf : Function.Injective f) : False := by
  let Q := U.subgroupOf O
  have hyQ : y ∈ normalizer (Q : Set O) := le_normalizer_comap O.subtype hyN
  have hfy : f y ∈ normalizer (Q.map f : Set _) :=
    Q.le_normalizer_map f (mem_map_of_mem f hyQ)
  apply BinaryLinear.FourTwoLocalFive.five_not_dvd_normalizer (Q.map f) (hQ.map f)
    (fun hh => hne ((Q.map_eq_bot_iff_of_injective hf).mp hh))
  have hd := orderOf_dvd_natCard (⟨f y,hfy⟩ : normalizer (Q.map f : Set _))
  rw [Subgroup.orderOf_mk,orderOf_injective f hf] at hd
  exact h5.trans hd

private theorem centerless_star_centralizer
    (hz : center (starImage j.J (Mc.pCoreIn 2) j.J) = ⊥) :
    centralizer (starImage j.J (Mc.pCoreIn 2) j.J : Set (StarQuotient j.J (Mc.pCoreIn 2))) = ⊥ := by
  have hi := source_component_input s d j
  let : (j.J.subgroupOf (j.J ⊔ Mc.pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le j.J.le_normalizer hi.normalizes)
  have hfit := (star_fitting_quasisimple (source_join_input hi)).1
  apply bot_unique
  intro x hx
  have hC : x ∈ starImage j.J (Mc.pCoreIn 2) j.J := by
    rw [←hfit] at hx ⊢
    exact centralizer_generalizedFitting_le _ hx
  have hc : (⟨x,hC⟩ : starImage j.J (Mc.pCoreIn 2) j.J) ∈ center _ := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  rw [hz,mem_bot] at hc
  exact congrArg Subtype.val hc

/-- A faithful four-dimensional representation of the actual offender group
is incompatible with the original quintic action and a centerless, outer-two
star component. The radical need not lie in the component. -/
theorem source_no_four_dimensional_offender
    (hz : center (starImage j.J (Mc.pCoreIn 2) j.J) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (starImage j.J (Mc.pCoreIn 2) j.J)))
    (f : offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)) →*
      BinaryLinear.OuterCyclic.LinearGroup 4) (hf : Function.Injective f) : False := by
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let O := offenderSubgroup (starRepresentation j.J R)
  let U := starImage j.J R R
  let Q := U.subgroupOf O
  have hi := source_component_input s d j
  let : (j.J.subgroupOf (j.J ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le j.J.le_normalizer hi.normalizes)
  let : C.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hCO : C ≤ O := (star_offender_fitting (source_join_input hi)).1
  have hQ : IsPGroup 2 Q :=
    ((isPGroup_pCoreIn 2 Mc).comap_subtype.map (QuotientGroup.mk' (starKernel j.J R))).comap_subtype
  have hne : Q ≠ ⊥ := by
    intro hbot
    obtain ⟨A,hAU,hA⟩ := (kernel_offender_of_normal_input (source_join_input hi)).2.best
    apply hA.1.1
    apply bot_unique
    intro x hx
    have hmem : (⟨x,hA.le_offenderSubgroup _ hx⟩ : O) ∈ Q := hAU hx
    rw [hbot,mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨k,hk,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
  have hin := source_first_star_inner_of_outer_two s d j ho
  obtain ⟨x,hx⟩ := hin ⟨⟨k,hk⟩,rfl⟩
  change MulAut.conj x = starComponentAction j.J R k at hx
  let α := starNormalizerAut j.J R k k.property.1 k.property.2
  have hα (c : C) : α c = (x : StarQuotient j.J R) * c * (x : StarQuotient j.J R)⁻¹ := by
    have he := starComponentAut_coe j.J R k k.property.1 k.property.2 c
    rw [←starComponentAction_apply,←hx] at he
    exact he.symm
  have he : α = MulAut.conj (x : StarQuotient j.J R) :=
    inner_on_self_centralizing C (centerless_star_centralizer s d j hz) α x hα
  have hU : U.map (MulAut.conj (x : StarQuotient j.J R)).toMonoidHom = U := by
    rw [←he]
    exact starNormalizerAut_image j.J R R k k.property.1 k.property.2 k.property.2
  have hxN : (x : StarQuotient j.J R) ∈ normalizer (U : Set _) :=
    mem_normalizer_iff_map_conj_eq.mpr hU
  let y : O := ⟨x,hCO x.property⟩
  have h5 : 5 ∣ orderOf y := by
    have hd := orderOf_map_dvd (MulAut.conj : C →* MulAut C) x
    rw [hx,ha] at hd
    simpa only [y,Subgroup.orderOf_mk,Subgroup.orderOf_coe] using hd
  exact four_dimensional_normalizer_obstruction O U hQ hne y hxN h5 f hf

/-- Apply the obstruction to the literal moved-section action, retaining its
full offender group rather than replacing it by the component. -/
theorem source_no_four_dimensional_moved
    (hz : center (starImage j.J (Mc.pCoreIn 2) j.J) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (starImage j.J (Mc.pCoreIn 2) j.J)))
    (r : MovedSection ((starRepresentation j.J (Mc.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))))
    (hr : Function.Injective r.action)
    (hd : Module.finrank (ZMod 2) (r.space.toSubmodule ⧸ r.central.toSubmodule) = 4) : False := by
  let W := r.space.toSubmodule ⧸ r.central.toSubmodule
  let e : W ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 4 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let E : (W →ₗ[ZMod 2] W)ˣ ≃* BinaryLinear.OuterCyclic.LinearGroup 4 :=
    (Units.mapEquiv e.conjRingEquiv.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (BinaryLinear.OuterCyclic.Space 4))
  apply source_no_four_dimensional_offender s d j hz ho
    (E.toMonoidHom.comp r.action.asGroupHom)
  exact E.injective.comp (fun _ _ h => hr (congrArg Units.val h))

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
