module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentClosure
public import Theory.GroupAction.ElementaryBinaryFiveRank

/-!
# Rank eight in the actual Hall component quotient

The original nonnormal A5 pair acts on the full binary module with a
two-group kernel. Restriction to the actual odd-centralizer residual
preserves that kernel bound, while the residual has five-rank two. Its
placed copy inside K therefore forces two-rank at least eight. For an
escaping component the source normalizer has trivial two-core; the center
of K is consequently odd, so the bound survives in K/Z(K).

All subgroups are literal restrictions of the original residual and full
module. No ambient strong-quasithin or component-normality premise is used.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3, printed pp.621--622 and745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original pair action forces rank at least eight in the actual central
quotient of every core-free subgroup containing the residual. -/
theorem source_a5_oddNormalizer_centralQuotient_twoRank_ge_eight_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hcore : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    8 ≤ primeRank 2 (K ⧸ center K) := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let F0 := F.subgroupOf N
  let P := F0.subgroupOf K
  let U := D.fullModule.subgroupOf N
  let W := U.subgroupOf K
  let H := localJoin T L
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hUF : U ≤ F0 := subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))
  have hUK : U ≤ K := hUF.trans hFK
  have hFH : F ≤ H := ((map_subtype_le _).trans inf_le_left).trans le_sup_left
  obtain ⟨_,_,_,_,he,_,hm,_,_,_,hr⟩ :=
    source_a5_oddNormalizer_component_local_marking_of_residual_le D e hn B hBC hodd hBV K hFK
  have hk : IsPGroup 2 ((centralizer (W : Set K)).subgroupOf P) := by
    let f : ((centralizer (W : Set K)).subgroupOf P) →*
        centralizer (D.fullModule.subgroupOf H : Set H) := {
      toFun := fun x => ⟨⟨x.val.val.val.val,hFH x.val.property⟩,by
        intro v hv
        apply Subtype.ext
        change v.val * x.val.val.val.val = x.val.val.val.val * v.val
        exact congrArg (fun z : K => z.val.val)
          (x.property ⟨⟨v.val,hVN hv⟩,hUK hv⟩ hv)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y heq
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z => z.val.val) heq
    exact (source_a5_full_module_local_kernel_isTwoGroup D e hn).of_injective f hf
  exact Theory.GroupAction.eight_le_centralQuotient_twoRank_of_elementary_action P W
    he (le_normalizer_iff_commutator_le_left.mpr hm.symm.le) hk hr.ge hcore

/-- The source escaping component supplies its trivial two-core, so the rank
eight obstruction needs no extra local action or core hypothesis. -/
theorem source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    8 ≤ primeRank 2 (K ⧸ center K) := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hcoreN := source_a5_oddPrimeNormalizer_twoCore_eq_bot
    D e hn hp B hB hBC hBV hperm
    (fun h => houtK ((map_subtype_le K).trans h))
  have hcoreK : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,hcoreN,MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff K.subtype).mpr K.subtype_injective
  exact source_a5_oddNormalizer_centralQuotient_twoRank_ge_eight_of_residual_le
    D e hn B hBC hodd hBV K hcoreK hFK
end CFSG.Quasithin.Chapter10
