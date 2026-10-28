module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentKernel
public import Theory.GroupTheory.CharacteristicNormalizerClosure
/-!
# Literal selected-component consumers for C.1.26

The actual reduced action selects the solvable residual of the marked
factor preimage. Its intrinsic quotient is A₅ in the alternating branch;
in every quasisimple branch its action kernel satisfies the intrinsic
Frattini bound. Normalizers are transported through this same preimage
and residual, retaining the original Baumann and Sylow subgroups.

Source: Aschbacher–Smith C.1.26, printed p.132.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB Chapter1.Section02
universe u
variable {G D : Type u} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite G] [Finite D] in
/-- The actual normalizer of the marked factor normalizes its selected lift. -/
theorem selected_component_normalized
    (q : G →* D) (A : Subgroup D) (L B : Subgroup G)
    (hL : (solvableResidual (A.comap q)).map (A.comap q).subtype = L)
    (hB : B.map q ≤ normalizer (A : Set D)) : B ≤ normalizer (L : Set G) := by
  rw [←hL]
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ _)
  intro b hb
  apply mem_normalizer_iff.mpr
  intro a
  change q a ∈ A ↔ q (b*a*b⁻¹) ∈ A
  simpa only [map_mul,map_inv] using (mem_normalizer_iff.mp (hB (mem_map_of_mem q hb)) (q a))

/-- The original A₅ action selects an actual local component, retaining its
intrinsic quotient and every specified factor normalizer. -/
theorem exists_five_component_of_reduced_module
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hs : ¬ Group.IsSolvable G)
    (A : Subgroup D) (hA : IsComponent D A) (eA : A ≃* alternatingGroup (Fin 5)) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = A ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      (solvableResidual (A.comap q)).map (A.comap q).subtype = L ∧
      ∀ B : Subgroup G, B.map q ≤ normalizer (A : Set D) → B ≤ normalizer (L : Set G) := by
  obtain ⟨L,hL,himage,hqs,hcanonical⟩ := exists_component_lift_of_reduced_module
    h36 hG T hP U hU hJ q hq hk hs A hA
  let := hqs
  let f : L →* alternatingGroup (Fin 5) :=
    eA.toMonoidHom.comp ((MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap L))
  have hf : Function.Surjective f := eA.surjective.comp
    ((MulEquiv.subgroupCongr himage).surjective.comp (q.subgroupMap_surjective L))
  obtain ⟨e,he⟩ := five_core_quotient_equiv f hf
  exact ⟨L,hL,himage,⟨e⟩,hcanonical,fun B hB => selected_component_normalized q A L B hcanonical hB⟩

/-- The same component selected from the original reduced action has its
own Frattini kernel, rather than an assumed restriction of the ambient one. -/
theorem exists_component_with_intrinsic_frattini_kernel
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hs : ¬ Group.IsSolvable G)
    (A : Subgroup D) (hA : IsComponent D A) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = A ∧
      IsQuasisimple (L ⧸ pCore 2 L) ∧
      L ⊓ q.ker ≤ BaumannArgument.coreFrattini L ∧
      (solvableResidual (A.comap q)).map (A.comap q).subtype = L := by
  obtain ⟨L,hL,himage,hqs,hcanonical⟩ := exists_component_lift_of_reduced_module
    h36 hG T hP U hU hJ q hq hk hs A hA
  let := hqs
  have hcore : pCore 2 D = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  exact ⟨L,hL,himage,hqs,component_action_kernel q hcore L (himage.symm ▸ hA),hcanonical⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
