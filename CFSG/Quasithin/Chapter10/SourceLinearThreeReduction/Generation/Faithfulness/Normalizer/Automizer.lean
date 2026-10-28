module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallFrattini

/-!
# Doubled odd ranks in the original full-module automizer

The placed solvable residual normalizes the original elementary full module.
The kernel of its automizer action embeds into the local full-module
centralizer, which is a two-group. Thus every odd rank of the original
component occurs twice in this literal automizer.

Source: the nonnormal branch of Aschbacher--Smith 4.4.3, printed p.622,
as used in 10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual residual contributes twice each odd component rank to the full-module automizer. -/
theorem source_nonnormal_oddNormalizer_fullModule_automizer_rank
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    let W := (D.fullModule.subgroupOf (normalizer (B : Set G))).subgroupOf K
    2 * primeRank p (L ⧸ pCore 2 L) ≤ primeRank p W.normalizerMonoidHom.range := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let P := (F.subgroupOf N).subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let J := localJoin T L
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFJ : F ≤ J := ((map_subtype_le _).trans inf_le_left).trans le_sup_left
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hVK : D.fullModule.subgroupOf N ≤ K :=
    (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
  let a : P ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  obtain ⟨_,_,_,_,_,_,hm,_,_⟩ :=
    source_oddNormalizer_component_local_geometry_of_residual_le D B hBC hodd hBV K hFK
  have hPW : P ≤ normalizer (W : Set K) :=
    le_normalizer_iff_commutator_le_left.mpr hm.ge
  let α : P →* normalizer (W : Set K) := inclusion hPW
  let f : P →* W.normalizerMonoidHom.range :=
    W.normalizerMonoidHom.rangeRestrict.comp α
  let C := centralizer (D.fullModule.subgroupOf J : Set J)
  let k : f.ker →* C := {
    toFun := fun x => ⟨inclusion hFJ (a x.val), by
      intro v hv
      let w : W := ⟨⟨⟨v,hVN hv⟩,hVK hv⟩,hv⟩
      have hz := congrArg (fun b : W.normalizerMonoidHom.range =>
        ((b.val w : K) : N).val) x.property
      change ((a x.val : F) : G) * (v : G) * ((a x.val : F) : G)⁻¹ = v at hz
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hz).symm⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hk : IsPGroup 2 f.ker :=
    (source_nonnormal_full_module_local_kernel_isTwoGroup D hn).of_injective k (by
      intro x y h
      apply Subtype.ext
      apply a.injective
      apply (inclusion_injective hFJ)
      exact congrArg (fun c : C => (c : J)) h)
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

end CFSG.Quasithin.Chapter10
