module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairKernel
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.SylowFrattiniOddSquares
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Inner action of the original pair from small Sylow Frattini quotients

Every nontrivial image of the original fixed residual retains both simple
component quotients. The whole radical-free product survives restriction
from outer automorphisms to a Sylow two-subgroup, by the source S₂ theorem.
Burnside's theorem gives an odd prime other than three dividing a component;
its square cannot divide the automorphism order of a two-group with at most
five Frattini generators. Thus the original residual acts innerly, without
assuming the full Schreier theorem for the recognized component model.

The conclusion retains the actual Hall-kernel normalizer and the complete
center of its normal component. Source: Aschbacher--Smith 4.4.10, p.621.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
  {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The original pair has trivial image in the outer group of a simple group
whose Sylow two-subgroup has at most five Frattini generators. -/
theorem source_nonnormal_oddActorResidual_outer_hom_eq_one_of_smallFrattini
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (P : Sylow 2 S) (hP : Nat.card (P ⧸ frattini P) ≤ 32) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ f : I →* MulAut.Outer S, f.comp (inclusion (show F ≤ I from le_sup_left)) = 1 := by
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
  change ∀ f : I →* MulAut.Outer S,
    f.comp (inclusion (show F ≤ I from le_sup_left)) = 1
  intro f
  let g := f.comp (inclusion (show F ≤ I from le_sup_left))
  by_contra hg
  have hk : IsPGroup 2 g.ker := source_nonnormal_oddActorResidual_hom_kernel D hn hp B hB hBC hperm f hg
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  let R := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (R ⧸ center R) := IsQuasisimple.simple
  let : IsSimpleGroup R := ((QuotientGroup.quotientMulEquivOfEq
    (source_nonnormal_component_core_center D hn)).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨eF⟩ := source_nonnormal_oddActorResidual_product_equiv D hn B hBC hodd
  let q : F →* R × R := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hq : Function.Surjective q := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 F := by
    rw [MonoidHom.ker_comp_of_injective _ _ eF.injective,QuotientGroup.ker_mk']
  have hker : g.ker ≤ q.ker := by
    rw [hqker]
    exact le_sSup ⟨inferInstance,hk⟩
  let a : g.range →* R × R :=
    g.rangeRestrict.liftOfSurjective g.rangeRestrict_surjective ⟨q,by
      simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨g.rangeRestrict y,by simp [a]⟩
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hrad : solvableRadical R = ⊥ :=
    solvableRadical_eq_bot_of_simple_not_solvable (Group.IsPerfect.not_isSolvable R)
  have hdiv := MulAut.radicalFree_outer_section_card_dvd_sylow_aut P
    (solvableRadical_prod_eq_bot hrad hrad) g.range a ha
  obtain ⟨r,hr,hor,hr3,hrd⟩ := Perfect.exists_odd_prime_ne_dvd_card R Nat.prime_three
  have hsq : r^2 ∣ Nat.card (R × R) := by
    rw [Nat.card_prod,pow_two]
    exact Nat.mul_dvd_mul hrd hrd
  exact P.isPGroup'.not_odd_prime_square_dvd_card_mulAut_of_frattini_card_le_thirtytwo
    hP hr hor hr3 (hsq.trans hdiv)

include D in
/-- A small actual Sylow Frattini quotient of K/Z(K) forces the unchanged
fixed residual to act innerly on the normal quasisimple K. -/
theorem source_nonnormal_oddNormalizer_inner_of_smallFrattini
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card (P ⧸ frattini P) ≤ 32) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hIN : I ≤ N := sup_le hFN inf_le_right
  let α : N →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hz := source_nonnormal_oddActorResidual_outer_hom_eq_one_of_smallFrattini
    D hn hp B hB hBC hperm P hP ((j.comp α).comp (inclusion hIN))
  have hker : α.ker = K ⊔ centralizer (K : Set N) := by
    rw [show α = (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (MulAut.conjNormal : N →* MulAut K) from rfl,
      ← MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  intro x hx
  rw [← hker]
  change α x = 1
  apply MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K))
  exact (DFunLike.congr_fun hz (⟨x,hx⟩ : F)).trans j.map_one.symm
end CFSG.Quasithin.Chapter10
