module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Reduction
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Quotient
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.OddCentralizer
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer
public import Theory.GroupTheory.PerfectNormalizerInner.SimpleSection
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Injective

/-!
# The original exterior module in a selected component

The actual fixed residual has its marked PSL₅(2) quotient with two-group
kernel. Either that simple group is a section of the selected component's
outer automorphism group, or the residual acts inner. In the latter case,
the original uniqueness argument places V and the residual inside K,
proves K normal in N(A), and identifies its centralizer with O(N(A)).
The central quotient still contains the same elementary group of order
1024: O₂(K)=1 makes its central kernel odd. Thus its two-rank is at least ten.

This is a dichotomy, not an assumption of Schreier or residual uniqueness.
The caller supplies uniqueness only in that branch of the source reduction.
Source: Aschbacher--Smith 4.4.10--11, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Inner residual action places the literal exterior module and residual in
one normal component; the quotient has two-rank at least ten. -/
theorem exterior_oddNormalizer_component_placement
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M)
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M)
    (hinner : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G)))) :
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      10 ≤ primeRank 2 (K ⧸ center K) := by
  have hc := s.marking.centralizing_actor_commutator hAM hAV
  have hv := chosen_oddNormalizer_module_le_of_component_inner_action
    h.toHypothesis1221 D A hAM hc hodd hAV hu K houtK hinner
  have ho := chosen_oddNormalizer_component_centralizer_odd
    h.toHypothesis1221 D s.marking.centralizer_eq_core.le
    A hAM hc hodd hAV hu hout K hK houtK hv
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFN).symm.surjective
  have hFK := hK.perfect_actor_le_of_odd_centralizer ho (F.subgroupOf N) hinner
  have hFJ : F ≤ K.map N.subtype := by
    have hh := map_mono (f := N.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  have hVN : V ≤ N := hv.trans (map_subtype_le K)
  have hVK : V.subgroupOf N ≤ K := by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rwa [map_subgroupOf_eq_of_le hVN]
  let W := (V.subgroupOf N).subgroupOf K
  let w : W ≃* V := (subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)
  let := D.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective w.toMonoidHom w.injective
  have hW : Nat.card W = 2 ^ 10 := (Nat.card_congr w.toEquiv).trans s.marking.card_module
  have hcoreK : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,
      (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2, MonoidHom.comap_bot]
    exact K.subtype.ker_eq_bot K.subtype_injective
  have hzc : Nat.Coprime 2 (Nat.card (center K)) := Nat.prime_two.coprime_iff_not_dvd.mpr
    (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcoreK (center K) le_rfl)
  let q := QuotientGroup.mk' (center K)
  have hi : Function.Injective (q.comp W.subtype) :=
    injective_comp_subtype_of_coprime_ker q (by simpa only [q, QuotientGroup.ker_mk'] using hzc)
      W (IsElementaryAbelian.isPGroup 2 W)
  have hr : 10 ≤ primeRank 2 W := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup W) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup W).subtype (⊤ : Subgroup W).subtype_injective
    have hh := IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup W)
      (by simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup W) ≃* W).toEquiv] using hW)
    exact hh
  exact ⟨hK.normal_of_odd_centralizer ho, hv, hFJ,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho,
    hr.trans (_root_.primeRank_le_of_injective 2 (q.comp W.subtype) hi)⟩

/-- The actual residual action either is inner or supplies a literal
PSL₅(2) section of the outer automorphism group. -/
theorem exterior_oddNormalizer_component_inner_or_outer_section
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) ∨
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f := by
  classical
  let S := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup S := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  by_cases ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* S, Function.Surjective f
  · exact Or.inr ho
  apply Or.inl
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let u : F.subgroupOf N ≃* F := subgroupOfEquivOfLe hFN
  obtain ⟨⟨e, _⟩, _⟩ := s.marking.oddActorResidual_quotient h A hAM hodd hAV
  let q : F.subgroupOf N →* S := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 F)).comp u.toMonoidHom)
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp u.surjective)
  have hk : q.ker = (pCore 2 F).comap u.toMonoidHom := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective u.toMonoidHom u.injective
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := u.symm.toMonoidHom) u.symm.surjective
  obtain ⟨_, hFK, _⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A hAM (s.marking.centralizing_actor_commutator hAM hAV) hodd hAV K hK
  exact perfect_le_sup_centralizer_of_no_simple_outer_section K (F.subgroupOf N) q hq
    (fun U f hf => ho ⟨U, f, hf⟩) hFK

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
