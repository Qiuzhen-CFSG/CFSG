module
public import CFSG.Quasithin.ChapterD.Section03.ActorKernel
public import Theory.GroupTheory.PGroup.CoprimeFrattiniCommutator
public import CFSG.Quasithin.ChapterD.Section03.SourceInternal
public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Full actor commutators from a moving two-subgroup

For either D.3.1 actor alternative, a T-normalized two-subgroup J has
[X,J]=X or [X,J]=1. A proper commutator centralizes a component orbit;
in the odd-prime case it lies in the Frattini subgroup and coprime
Frattini detection kills it. If XT is the whole core-free group, the
centralizing alternative makes J a normal two-subgroup and hence trivial.

Apply this dichotomy to the actual faithful internal orbit action.
The original kernel lies in O₂,Φ(X); Frattini nongeneration followed by
two-perfectness lifts full commutator generation back to X. Both original
source actor alternatives are retained throughout.

Source: Aschbacher–Smith, Lemma 3.2.2(6), using D.3.3–4, combined
manuscript of 1 March 2004, printed pp.193–194 and 579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.Section03
variable {G : Type*} [Group G] [Finite G]

theorem ActorCases.commutator_eq_self_or_eq_bot
    {T : Sylow 2 G} {X J : Subgroup G} [X.Normal]
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : ActorCases T X hTX) (hJT : J ≤ (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) :
    ⁅X, J⁆ = X ∨ ⁅X, J⁆ = ⊥ := by
  by_cases he : ⁅X, J⁆ = X
  · exact Or.inl he
  right
  let N := ⁅X, J⁆
  have hNX : N ≤ X := commutator_le_left X J
  have hn : X ⊔ (T : Subgroup G) ≤ normalizer (N : Set G) := by
    refine sup_le (normalizer_commutator_ge_left X J) ?_
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change N.map (MulAut.conj t).toMonoidHom = N
    have hx : X.map (MulAut.conj t).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (hTX ht)
    have hj : J.map (MulAut.conj t).toMonoidHom = J :=
      mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    rw [map_commutator, hx, hj]
  rcases hc with ⟨L, hL, hX⟩ | ⟨p, hp, ho, hpX, hi⟩
  · have hLX : L ≤ X := by rw [hX]; exact le_componentOrbit L T
    let : (N.subgroupOf X).Normal :=
      (normal_subgroupOf_iff_le_normalizer hNX).mpr (le_sup_left.trans hn)
    let : Group.IsPerfect X := by rw [hX]; exact hL.orbit_isPerfect T
    have hLN : ⁅L, N⁆ = ⊥ := by
      rcases (hL.subgroupOf hLX).normal_dichotomy (N.subgroupOf X) with hl | hcomm
      · have hLN : L ≤ N := by
          simpa only [map_subgroupOf_eq_of_le hLX, map_subgroupOf_eq_of_le hNX] using
            map_mono (f := X.subtype) hl
        have hXN : X ≤ N := by
          rw [hX]
          exact iSup_conjugates_le_of_le_normalizer L T N hLN (le_sup_right.trans hn)
        exact (he (le_antisymm hNX hXN)).elim
      · simpa only [map_commutator, map_subgroupOf_eq_of_le hLX,
          map_subgroupOf_eq_of_le hNX, Subgroup.map_bot] using congrArg (map X.subtype) hcomm
    have hXC : X ≤ centralizer (N : Set G) := by
      rw [hX]
      exact iSup_conjugates_le_centralizer L T N (le_sup_right.trans hn) hLN
    have hiter : ⁅⁅J, X⁆, X⁆ = ⊥ := by
      rw [commutator_comm J X, commutator_comm N X]
      exact commutator_eq_bot_iff_le_centralizer.mpr hXC
    rw [commutator_comm X J]
    exact commutator_eq_bot_of_iterated_eq_bot J X hiter
  · let : Fact p.Prime := ⟨hp⟩
    have hpne : p ≠ 2 := by intro heq; subst p; norm_num at ho
    have hphi := ActorCases.proper_normal_le_frattini
      (show ActorCases T X hTX from Or.inr ⟨p, hp, ho, hpX, hi⟩) hNX hn he
    exact commutator_eq_bot_of_le_frattini_of_isPGroup hpne X J hpX
      (T.isPGroup'.to_le hJT) (hJT.trans hTX) hphi

theorem ActorCases.commutator_eq_self_of_core_free
    {T : Sylow 2 G} {X J : Subgroup G} [X.Normal]
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : ActorCases T X hTX) (hgen : X ⊔ (T : Subgroup G) = ⊤)
    (hcore : pCore 2 G = ⊥) (hJT : J ≤ (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) (hJ : J ≠ ⊥) :
    ⁅X, J⁆ = X := by
  refine (hc.commutator_eq_self_or_eq_bot hJT hTJ).resolve_right ?_
  intro he
  have hXJ : X ≤ normalizer (J : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp he).trans (Subgroup.centralizer_le_normalizer _)
  let : J.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le hXJ hTJ))
  have hjcore : J ≤ pCore 2 G := le_sSup ⟨inferInstance, T.isPGroup'.to_le hJT⟩
  exact hJ (bot_unique (hjcore.trans_eq hcore))

end CFSG.Quasithin.ChapterD.Section03



public section
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X J : Subgroup G} {I : Submodule (ZMod 2) V}

theorem InternalModuleHypotheses.actor_eq_commutator_of_moving_twoGroup
    (h : InternalModuleHypotheses K ρ T X I)
    (hgen : X ⊔ (T : Subgroup G) = ⊤) (hJT : J ≤ (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hJ : ¬ J ≤ (invariantActionHom ρ (orbitSpan ρ ⊤ I)
      (orbitSpan_invariant ρ ⊤ I)).ker) : X = ⁅X, J⁆ := by
  let := h.normal
  let W := orbitSpan ρ ⊤ I
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  have hf : Function.Surjective f := invariantActionHom_surjective ρ W _
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := le_normalizer_of_normal
  let N := ⁅X, J⁆
  have hn : (⊤ : Subgroup G) ≤ normalizer (N : Set G) := by
    rw [← hgen]
    refine sup_le (normalizer_commutator_ge_left X J) ?_
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change N.map (MulAut.conj t).toMonoidHom = N
    have hx : X.map (MulAut.conj t).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (hTX ht)
    have hj : J.map (MulAut.conj t).toMonoidHom = J :=
      mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    rw [map_commutator, hx, hj]
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hfb : J.map f ≠ ⊥ := fun hb => hJ ((map_eq_bot_iff J).mp hb)
  have htbar : (T.mapSurjective hf : Subgroup (subspaceActionImage ρ W)) ≤
      normalizer (J.map f : Set _) :=
    (map_mono hTJ).trans (J.le_normalizer_map f)
  have hgenbar : X.map f ⊔ (T.mapSurjective hf : Subgroup _) = ⊤ := by
    change X.map f ⊔ (T : Subgroup G).map f = ⊤
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ hf]
  have hsource := h.faithfulOrbit_source
  let : (X.map f).Normal := Normal.map inferInstance f hf
  have hm : X.map f = restrictedSubgroup ρ W X := invariantActionHom_map ρ W _ X
  have hcases : ActorCases (T.mapSurjective hf) (X.map f)
      (by rw [normalizer_eq_top]; exact le_top) := by
    simpa only [hm] using hsource.cases
  have hcomm : ⁅X.map f, J.map f⁆ = X.map f :=
    hcases.commutator_eq_self_of_core_free hgenbar
      h.faithfulOrbit_twoCore_eq_bot (map_mono hJT) htbar hfb
  have hR : pResidual 2 G = X := pResidual_eq_of_isPPerfect_sup X (T : Subgroup G)
    ((pResidual_eq_top_iff 2 X).mp h.residual) T.isPGroup' hgen
  have hkX : X ⊓ f.ker ≤ (coreFrattiniIn X).map X.subtype := by
    intro x hx
    apply h.orbit_actorKernel_le_coreFrattini
    rw [invariantActionHom_ker] at hx
    exact ⟨hx.1, hx.2.2⟩
  have hk : pResidual 2 G ⊓ f.ker ≤
      (coreFrattiniIn (pResidual 2 G)).map (pResidual 2 G).subtype := by
    rw [hR]
    exact hkX
  have hmap : (pResidual 2 G).map f ≤ N.map f := by
    rw [hR, map_commutator]
    exact hcomm.ge
  have hs := pResidual_le_sup_of_frattini_kernel 2 N f
    (pCore 2 (pResidual 2 G)) hmap hk
  change pResidual 2 G ≤ N ⊔ (pResidual 2 G).pCoreIn 2 at hs
  rw [hR] at hs
  have hle := le_normal_of_isPPerfect_of_le_sup_pGroup X N (X.pCoreIn 2)
    ((pResidual_eq_top_iff 2 X).mp h.residual) (isPGroup_pCoreIn 2 X) hs
  exact le_antisymm hle (commutator_le_left X J)

end CFSG.Quasithin.ChapterD.Section03
