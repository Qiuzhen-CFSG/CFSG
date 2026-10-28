module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallQuotientAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallProductCubicFixer

/-!
# Inner action on the original containing quotient

Transport the unchanged quotient K/O₂(K) to its two original PSL₂(p)
factors. The image of the original cubic complement has order nine and
cyclic coordinate projections, so every elementary two-group of quotient
automorphisms fixing it pointwise is inner when p is 11 or 13 modulo 24.
The original module's faithful quotient action therefore has inner range.

This retains the original module and the possible trivial image. Innerness
of its induced quotient action does not assert that its Frattini action
lies in the image of K/O₂(K): that stronger placement requires control of
the centralizer of the latter image.
Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- Pointwise fixation of the actual cubic complement forces any elementary
module quotient action to be inner on the unchanged containing quotient. -/
theorem Data.moduleQuotientAction_inner (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (φ : moduleFrattiniImage D H →* MulAut (XiQuotient (enlargedResidual T L H)))
    (hfix : ∀ a x, x ∈ quotientImage (enlargedResidual T L H) P → φ a x = x) :
    φ.range ≤ MulAut.innerSubgroup (XiQuotient (enlargedResidual T L H)) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := enlargedResidual T L H
  let C := quotientImage K P
  let : IsElementaryAbelian 2 (moduleFrattiniImage D H) :=
    h.moduleFrattiniImage_elementary hfull
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  let : IsElementaryAbelian 3 P := hpc.1
  let : IsElementaryAbelian 3 (P.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 K))
  have hep : Nonempty (P ≃* quotientImage K P) := by
    rw [show K = componentOrbit I (T : Subgroup G) from hK]
    exact ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hC : Nat.card C = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let j := e.trans (eF.prodCongr eF)
  have hr : primeRank 3 (PSL(2,F) × PSL(2,F)) ≤ 2 := by
    rw [←primeRank_congr 3 j,hK]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3
      (by decide) (by decide)
  let C' := C.map j.toMonoidHom
  let : IsElementaryAbelian 3 C' := IsElementaryAbelian.map j.toMonoidHom
  have hthree : IsPGroup 3 C' := IsElementaryAbelian.isPGroup 3 C'
  let : IsCyclic (C'.map (MonoidHom.fst PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  let : IsCyclic (C'.map (MonoidHom.snd PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  let ψ := (MulAut.congr j).toMonoidHom.comp φ
  let : IsElementaryAbelian 2 ψ.range :=
    IsElementaryAbelian.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hinner : ψ.range ≤ MulAut.innerSubgroup (PSL(2,F) × PSL(2,F)) := by
    apply CubicFixer.elementary_product_cubic_fixer_inner ho hF hmod ψ.range C'
    · exact (Nat.card_congr (j.subgroupMap C).toEquiv).symm.trans hC
    · rintro _ ⟨a,rfl⟩ _ ⟨z,hz,rfl⟩
      change j (φ a (j.symm (j z))) = j z
      rw [j.symm_apply_apply,hfix a z hz]
  rintro _ ⟨a,rfl⟩
  have hi : MulAut.congr j (φ a) ∈ MulAut.innerSubgroup (PSL(2,F) × PSL(2,F)) :=
    hinner ⟨a,rfl⟩
  rw [←MulAut.map_innerSubgroup_congr j,mem_map_equiv,MulEquiv.symm_apply_apply] at hi
  exact hi

/-- The faithful marked quotient action from the original module has inner
range. No placement of the module in the containing residual is assumed. -/
theorem Data.exists_faithful_inner_moduleQuotientAction (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ∃ φ : moduleFrattiniImage D H →* MulAut (XiQuotient (enlargedResidual T L H)),
      Function.Injective φ ∧
      φ.range ≤ MulAut.innerSubgroup (XiQuotient (enlargedResidual T L H)) ∧
      (∀ a x, h.coreQuotientFrattiniAction hn (φ a x) =
        (a : MulAut (CoreFrattiniSection T L H)) *
          h.coreQuotientFrattiniAction hn x * (a : MulAut (CoreFrattiniSection T L H))⁻¹) ∧
      ∀ a x, x ∈ quotientImage (enlargedResidual T L H) P → φ a x = x := by
  have hlarge : 11 ≤ p := by have := Nat.mod_le p 24; omega
  obtain ⟨φ,hφ,hmark,hfix⟩ := h.exists_faithful_moduleQuotientAction f hn hs hK hp ho hm
    hlarge hP hc
  exact ⟨φ,hφ,h.moduleQuotientAction_inner s.full_eq_local hn hs hK hp ho hm hmod φ hfix,
    hmark,hfix⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unchanged collapsed source supplies a faithful inner action fixing
its actual cubic image pointwise, retaining the possible trivial image. -/
theorem SourceCubicNormalizerEnlargement.exists_faithful_inner_moduleQuotientAction
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      (moduleFrattiniImage D H = ⊥ ∨ Nat.card (moduleFrattiniImage D H) = 4) ∧
      ∃ φ : moduleFrattiniImage D H →* MulAut (XiQuotient (enlargedResidual T L H)),
        Function.Injective φ ∧
        φ.range ≤ MulAut.innerSubgroup (XiQuotient (enlargedResidual T L H)) ∧
        (∀ a x, h.coreQuotientFrattiniAction hn (φ a x) =
          (a : MulAut (CoreFrattiniSection T L H)) *
            h.coreQuotientFrattiniAction hn x * (a : MulAut (CoreFrattiniSection T L H))⁻¹) ∧
        ∀ a x, x ∈ quotientImage (enlargedResidual T L H) P → φ a x = x := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  exact ⟨H,P,h,hn,hs.toLocalInput,
    h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hcollapse,
    h.exists_faithful_inner_moduleQuotientAction f hn hs hK hp ho hm h24 hP hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
