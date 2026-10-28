module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalAction

/-!
# Doubled odd ranks in the original local-module automizer

The placed solvable residual normalizes the original elementary local module.
The kernel embeds into the action kernel on the local module, which is a
two-group by the original covering pair argument. Thus every odd rank of the original
component occurs twice in this literal automizer.

Source: the nonnormal branch of Aschbacher--Smith 4.4.3, printed p.622,
as used in 10.2.3(2), printed p.745.
-/

public section
open scoped Pointwise
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual residual contributes twice each odd component rank to the local-module automizer. -/
theorem source_nonnormal_oddNormalizer_fullModule_automizer_rank
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {q : ℕ} [Fact q.Prime] (hq : Odd q)
    (B : Subgroup G) (hB : IsPGroup q B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (V : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    let W := (V.subgroupOf (normalizer (B : Set G))).subgroupOf K
    2 * primeRank p (L ⧸ pCore 2 L) ≤ primeRank p W.normalizerMonoidHom.range := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hq.pow
  let N := normalizer (B : Set G)
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let P := (F.subgroupOf N).subgroupOf K
  let W := (V.subgroupOf N).subgroupOf K
  let J := localJoin T L
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFJ : F ≤ J := ((map_subtype_le _).trans inf_le_left).trans le_sup_left
  have hVN : V ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,_,hVF⟩ := source_local_oddActor_cover D V hVV hVX hNV B hBC hodd hBV
  have hVK : V.subgroupOf N ≤ K :=
    (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
  let a : P ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  obtain ⟨_,_,_,_,_,_,hm,_,_⟩ :=
    source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
  have hPW : P ≤ normalizer (W : Set K) :=
    le_normalizer_iff_commutator_le_left.mpr hm.ge
  let α : P →* normalizer (W : Set K) := inclusion hPW
  let f : P →* W.normalizerMonoidHom.range :=
    W.normalizerMonoidHom.rangeRestrict.comp α
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hIW : I ≤ normalizer (V : Set G) := (sup_le
    (hFJ) (inf_le_left.trans (show (T : Subgroup G) ≤ J from le_sup_right))).trans hNV
  let aI : I →* MulAut V := V.normalizerMonoidHom.comp (inclusion hIW)
  let g := aI.comp (inclusion (show F ≤ I from le_sup_left))
  have hmove := (source_local_oddActor_cover D V hVV hVX hNV B hBC hodd hBV).2.1
  have hg : g ≠ 1 := by
    intro hz
    apply hne
    apply hmove.trans
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv x hx
    have hh := DFunLike.congr_fun hz (⟨x,hx⟩ : F)
    have hh' := congrArg (fun b : MulAut V => (b ⟨v,hv⟩ : G)) hh
    change x*v*x⁻¹ = v at hh'
    exact mul_inv_eq_iff_eq_mul.mp hh'
  have hkg := source_nonnormal_oddActorResidual_hom_kernel D hn hq B hB hBC hperm aI hg
  let k : f.ker →* g.ker := {
    toFun := fun x => ⟨a x.val, by
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      let w : W := ⟨⟨⟨v,hVN v.property⟩,hVK v.property⟩,v.property⟩
      have hz := congrArg (fun b : W.normalizerMonoidHom.range =>
        ((b.val w : K) : N).val) x.property
      exact hz⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hk : IsPGroup 2 f.ker := hkg.of_injective k (by
    intro x y he
    exact Subtype.ext (a.injective (congrArg Subtype.val he)))
  have hr : primeRank p P = 2 * primeRank p (L ⧸ pCore 2 L) := by
    rw [primeRank_congr p a]
    exact source_nonnormal_oddActorResidual_primeRank D hn B hBC hodd ho
  have he : primeRank p P = primeRank p f.range := by
    apply primeRank_eq_of_surjective_of_coprime p f.rangeRestrict
      f.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict]
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  change 2 * primeRank p (L ⧸ pCore 2 L) ≤ primeRank p W.normalizerMonoidHom.range
  rw [←hr,he]
  exact primeRank_subgroup_le p _

end CFSG.Quasithin.Chapter10.LocalFixed
