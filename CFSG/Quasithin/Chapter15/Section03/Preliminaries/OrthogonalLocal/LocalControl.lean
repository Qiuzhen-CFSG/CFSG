module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Residual and maximal-overgroup arguments for 15.3.2–6

A maximal Sylow image gives the residual/full-action dichotomy. Full action
lifts to the A.5 factorization and hence to uniqueness; a two-group image
kills the genuine two-residual. The Sylow supplement supplies the corrected
containment `X ≤ C_M(V)T ≤ C_G(Z)` in 15.3.2(3).

The Chapter 14 ordering factorizations then give `M(T)={M,Mc}` and
`Mc=C_G(Z)`. Normalizer control promotes each local Sylow calculation to
its ambient centralizer or normalizer. The concrete Sylow-image maximality
and the Chapter 14 inputs remain explicit; these conditional reductions
alone do not establish all of 15.3.2–6.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122. The first containment corrects the omitted Sylow supplement
in the printed proof of 15.3.2(3).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup Stellmacher
open ChapterA.Section05To06
variable {G : Type*} [Group G]

/-- The Sylow supplement, with the residual embedded in the common ambient group. -/
theorem residual_sup_sylow [Finite G] (T : Sylow 2 G) {X : Subgroup G}
    (hTX : (T : Subgroup G) ≤ X) : twoResidualAmbient X ⊔ (T : Subgroup G) = X := by
  have hres := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup X) X.subtype X
    (by rw [← MonoidHom.range_eq_map, range_subtype])
  have h := congrArg (Subgroup.map X.subtype) (twoResidualAmbient_top_sup_sylow (T.subtype hTX))
  simpa only [Subgroup.map_sup, hres, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX,
    ← MonoidHom.range_eq_map, range_subtype] using h

/-- A two-group action image kills the two-residual, using its defining index condition. -/
theorem NaturalOrthogonalAction.residual_le_centralizer_of_image_isTwoGroup
    {M V X : Subgroup G} (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    (himage : IsPGroup 2 (d.image X)) :
    twoResidualAmbient X ≤ M ⊓ centralizer (V : Set G) := by
  let f : X →* OrthogonalActor := d.actor.comp (inclusion hXM)
  have hrange : f.range = d.image X := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_map.mpr ⟨⟨x, hXM x.property⟩, x.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have htwo : IsPGroup 2 f.range := hrange ▸ himage
  obtain ⟨n, hn⟩ := htwo.exists_card_eq
  have hindex : f.ker.index = 2 ^ n := by rw [index_ker, hn]
  have hR : twoResidualSubgroup X ≤ f.ker := sInf_le ⟨inferInstance, n, hindex⟩
  rintro r ⟨x, hx, rfl⟩
  refine ⟨hXM x.property, ?_⟩
  have hxker : inclusion hXM x ∈ d.actor.ker := hR hx
  rw [d.ker_actor] at hxker
  exact hxker

/-- 15.3.2(4), conditional only on the concrete maximality of the Sylow image
and the A.5 ordering-maximality supplied by 14.1.12. -/
theorem lemma_15_3_2_4_of_sylow_image_maximal
    (T : Sylow 2 G) {M X : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M) (himage : IsCoatom (d.image (T : Subgroup G)))
    (hTX : (T : Subgroup G) ≤ X) (hXM : X ≤ M) :
    twoResidualAmbient X ≤ M ⊓ centralizer (localModule T M : Set G) ∨
      (d.image X = ⊤ ∧ Chapter4.UniqueMaximalOvergroup X M) := by
  have hle : d.image (T : Subgroup G) ≤ d.image X :=
    map_mono (comap_mono hTX)
  rcases himage.le_iff.mp hle with hfull | hsmall
  · right
    refine ⟨hfull, hM.1.1, hXM, ?_⟩
    intro N hN hXN
    exact (lemma_A_5_7_1 hM hTX hXM (d.orderingLE_of_image_eq_top T hfull) N hN).mp hXN
  · left
    apply d.residual_le_centralizer_of_image_isTwoGroup hXM
    rw [hsmall]
    exact (T.isPGroup'.comap_subtype (K := M)).map d.actor

/-- The corrected containment in the small-residual branch of 15.3.2(3).
The Sylow supplement is essential: the source omits `T` in the first bound. -/
theorem le_centralizer_of_residual_le_module_centralizer [Finite G]
    (T : Sylow 2 G) {M X : Subgroup G}
    (hTX : (T : Subgroup G) ≤ X)
    (hres : twoResidualAmbient X ≤ M ⊓ centralizer (localModule T M : Set G)) :
    X ≤ (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) ∧
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) ≤
        centralizer (centralInvolutions T : Set G) := by
  constructor
  · rw [← residual_sup_sylow T hTX]
    exact sup_le_sup_right hres _
  · apply sup_le
    · exact inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _))
    · intro t ht z hz
      exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm

/-- The maximal-local family calculation of 15.3.2(3). The ordering premise
is the exact domination furnished by 14.1.12 once `|Z|=2`. -/
theorem maximalLocals_eq_pair_of_residual_dichotomy [Finite G]
    (T : Sylow 2 G) (M Mc : Subgroup G)
    (hM : M ∈ maximalLocals T) (hMc : Mc ∈ maximalLocals T)
    (hC : centralizer (centralInvolutions T : Set G) ≤ Mc)
    (horder : ∀ N ∈ maximalLocals T, OrderingLE T N M)
    (hdichotomy : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ M ⊓ centralizer (localModule T M : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M) :
    maximalLocals T = {M, Mc} := by
  ext N
  constructor
  · intro hN
    rcases hdichotomy (M ⊓ N) (le_inf hM.2 hN.2) inf_le_left with hsmall | hfull
    · have hXC := (le_centralizer_of_residual_le_module_centralizer T
        (le_inf hM.2 hN.2) hsmall)
      have hNM : N ≤ Mc := by
        intro n hn
        obtain ⟨a, ha, c, hc, rfl⟩ := horder N hN n hn
        exact Mc.mul_mem (hC (hXC.2 (hXC.1 ⟨ha.2, ha.1⟩)))
          (hC (centralizer_le (le_conjugateSpanBy _ _) hc.2))
      have heq : N = Mc := le_antisymm hNM (hN.1.2 hMc.1.1 hNM)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, heq, or_true]
    · have heq := hfull.2.2 N hN.1 inf_le_right
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, heq, true_or]
  · intro hN
    rcases hN with rfl | hN
    · exact hM
    · exact (Set.mem_singleton_iff.mp hN) ▸ hMc

/-- 15.3.4 follows directly from the corrected Sylow supplement and the
ordering factorization. All centralizers here are ambient or explicitly intersected. -/
theorem centralizer_eq_Mc_of_residual_dichotomy [Finite G]
    (T : Sylow 2 G) (M Mc : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hMc : Mc ∈ maximalLocals T)
    (hne : Mc ≠ M) (hC : centralizer (centralInvolutions T : Set G) ≤ Mc)
    (horder : OrderingLE T Mc M)
    (hdichotomy : twoResidualAmbient (M ⊓ Mc) ≤
        M ⊓ centralizer (localModule T M : Set G) ∨
      Chapter4.UniqueMaximalOvergroup (M ⊓ Mc) M) :
    Mc = centralizer (centralInvolutions T : Set G) := by
  rcases hdichotomy with hsmall | hfull
  · apply le_antisymm ?_ hC
    have hXC := le_centralizer_of_residual_le_module_centralizer T
      (le_inf hTM hMc.2) hsmall
    intro m hm
    obtain ⟨a, ha, c, hc, rfl⟩ := horder m hm
    exact mul_mem (hXC.2 (hXC.1 ⟨ha.2, ha.1⟩))
      (centralizer_le (le_conjugateSpanBy _ _) hc.2)
  · exact (hne (hfull.2.2 Mc hMc.1 inf_le_right)).elim

/-- The Sylow-promotion step used twice in 15.3.6. The conclusion keeps the
actual ambient subgroup, not just the order of an abstract Sylow group. -/
theorem exists_sylow_of_local_normalizer_control [Finite G]
    (T : Sylow 2 G) (S M H : Subgroup G)
    (hST : S ≤ (T : Subgroup G)) (hSH : S ≤ H)
    (hindex : ¬ 2 ∣ S.relIndex (M ⊓ H))
    (hcontrol : normalizer (S : Set G) ≤ M) :
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = S := by
  have hp : IsPGroup 2 S := T.isPGroup'.to_le hST
  have hindexH := not_dvd_relIndex_of_normalizer_inf_le S (M ⊓ H) H hp hSH
    hindex (le_inf (inf_le_left.trans hcontrol) inf_le_right)
  let P : Sylow 2 H := (hp.comap_subtype (K := H)).toSylow hindexH
  exact ⟨P, map_subgroupOf_eq_of_le hSH⟩

end CFSG.Quasithin.Chapter15.Section03
end
