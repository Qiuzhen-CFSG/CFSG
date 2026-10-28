module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallFrattini

/-!
# The residual pair on the fixed local module

A nontrivial action of the fixed residual extending to its original covering
subgroup has a two-group kernel. Thus both odd ranks survive on any nonzero
fully moved local module, even when the odd actor does not fix the full
M-orbit. In particular the local module has order divisible by 64.
The original small Sylow Frattini and soluble outer-action arguments also
place the residual using this local module alone.

Source: Aschbacher--Smith 4.4.10--14 and 10.2.3(2), printed pp.621--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
  (hVX : V = ⁅V,localOrbit T L⁆)
  (hNV : localJoin T L ≤ normalizer (V : Set G))
  {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
  (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hBV : B ≤ centralizer (V : Set G))
  (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
include hn hVV hne hVX hNV hp hB hBC hBV hperm

/-- The literal local action retains twice each odd rank of the original component. -/
theorem source_local_oddPrimeActor_automorphism_rank
    {r : ℕ} [Fact r.Prime] (hr : Odd r) :
    2 * primeRank r (L ⧸ pCore 2 L) ≤ primeRank r (MulAut V) := by
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
  have hIW : I ≤ normalizer (V : Set G) := (sup_le
    (((map_subtype_le _).trans inf_le_left).trans
      (show localOrbit T L ≤ localJoin T L from le_sup_left))
    (inf_le_left.trans (show (T : Subgroup G) ≤ localJoin T L from le_sup_right))).trans hNV
  let a : I →* MulAut V := V.normalizerMonoidHom.comp (inclusion hIW)
  let g := a.comp (inclusion (show F ≤ I from le_sup_left))
  have ho : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hm := (source_local_oddActor_cover D V hVV hVX hNV B hBC ho hBV).2.1
  have hg : g ≠ 1 := by
    intro hz
    apply hne
    apply hm.trans
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv f hf
    have hh := DFunLike.congr_fun hz (⟨f,hf⟩ : F)
    have hh' := congrArg (fun b : MulAut V => (b ⟨v,hv⟩ : G)) hh
    change f*v*f⁻¹ = v at hh'
    exact mul_inv_eq_iff_eq_mul.mp hh'
  have hk := source_nonnormal_oddActorResidual_hom_kernel D hn hp B hB hBC hperm a hg
  have he : primeRank r F = primeRank r g.range := by
    apply primeRank_eq_of_surjective_of_coprime r g.rangeRestrict g.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict]
    obtain ⟨n,he⟩ := hk.exists_card_eq
    rw [he]
    exact (Nat.coprime_two_right.mpr hr).pow_right n
  rw [←source_nonnormal_oddActorResidual_primeRank D hn B hBC ho hr,he]
  exact primeRank_subgroup_le r _

omit hp hB hBC hBV hperm in
/-- Both ranks already survive on any nonzero fully moved local submodule. -/
theorem source_local_automorphism_rank
    {r : ℕ} [Fact r.Prime] (hr : Odd r) :
    2 * primeRank r (L ⧸ pCore 2 L) ≤ primeRank r (MulAut V) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact source_local_oddPrimeActor_automorphism_rank D hn V hVV hne hVX hNV
    (p := 3) (by decide) ⊥ IsPGroup.of_bot bot_le bot_le (by simp) hr

/-- The fixed local module already has order divisible by 64. -/
theorem source_local_oddPrimeActor_sixtyFour_dvd : 2^6 ∣ Nat.card V := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVV
  apply ChapterC.HypothesisC28.elementary_sixtyFour_dvd_of_doubled_odd_ranks S V
  intro r hr hor
  let : Fact r.Prime := ⟨hr⟩
  exact source_local_oddPrimeActor_automorphism_rank D hn V hVV hne hVX hNV
    hp B hB hBC hBV hperm hor

variable (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include hK hout

/-- The original five-generator Sylow bound places the residual with local fixation. -/
theorem source_local_oddPrimeActor_residual_le_of_smallFrattini
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card (P ⧸ frattini P) ≤ 32) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K := by
  let : IsQuasisimple K := hK.2
  exact (source_local_oddPrimeActor_component_closure D hn V hVV hne hVX hNV
    hp B hB hBC hBV hperm K hK hout
    (source_nonnormal_oddNormalizer_inner_of_smallFrattini
      D hn hp B hB hBC hperm K P hP)).2.2

/-- The genuine Theorem C catalogue supplies soluble outer action for local placement. -/
theorem source_local_oddPrimeActor_residual_le_of_theoremC
    (hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC
      (Group.IsPerfect.not_isMulCommutative _) hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact source_local_oddPrimeActor_residual_le_of_solvable_outer D hn V hVV hne hVX hNV
    hp B hB hBC hBV hperm K hK hout

end CFSG.Quasithin.Chapter10
