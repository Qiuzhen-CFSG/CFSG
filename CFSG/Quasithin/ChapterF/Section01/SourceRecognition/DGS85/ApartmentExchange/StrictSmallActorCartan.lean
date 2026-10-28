module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorQuotient
public import Theory.GroupTheory.CoprimeSupplementNormalizer

/-!
# The original strict six-path actor contains its local Cartan

The actual half-path actor supplements the midpoint core. The prescribed
Cartan fixes the whole supported path and normalizes both half-path radicals.
Its odd order therefore puts its intersection with the intrinsic midpoint
actor inside their join. Injectivity of the original universal covering on
the midpoint stabilizer lifts this same containment to the universal tree.

This supplies DGS (14.3)(b) for the source-selected strict apartment. It does
not assume apartment exchange, naturality of the smaller core, or a model
comparison. Those later coordinate duties remain separate.

Source: DGS, Groups and Graphs (1985), (14.3)(a,b), printed p.212.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The actual local Cartan lies in the two-root actor, downstairs and
upstairs, on every twelve-path in the original strict source apartment. -/
theorem strict_source_small_actor_cartan_le
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length = 12)
    (hT : ∀ z ∈ p.support,
      z ∈ strictSourceApartment h hc hne hb hβu hns hlinear) :
    let D := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
    let J := graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))
    ((cartan (chosenCartans h)).map (bOne_tree_map h) ⊓ J ≤ D.map (bOne_tree_map h)) ∧
      (cartan (chosenCartans h) ⊓ J.comap (bOne_tree_map h) ≤ D) := by
  intro D J
  let c := chosenCartans h
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  have hfix (k) (hk : k ∈ cartan c) (j : ℕ) : k • p.getVert j = p.getVert j :=
    reflectionApartment_fixed c r.t r.normalizes k hk _ (hT _ (p.getVert_mem_support j))
  have hn : cartan c ≤ normalizer (D : Set (reducedAmalgam L S).Universal) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (reducedAmalgam L S).Universal) (p.drop 6) ⊔
      pathRoot (X := (reducedAmalgam L S).Universal) (p.take 6)).map _ = _
    rw [Subgroup.map_sup]
    have hr := pathRoot_map_conj (p.drop 6) (p.drop 6) k rfl
      (fun j _ => by rw [drop_getVert]; exact hfix k hk _)
    have ht := pathRoot_map_conj (p.take 6) (p.take 6) k rfl
      (fun j _ => by rw [take_getVert]; exact hfix k hk _)
    exact congrArg₂ (fun R U : Subgroup (reducedAmalgam L S).Universal => R ⊔ U) hr ht
  obtain ⟨K, fK, finK, chK, hK, e, hactors⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  obtain ⟨_, _, hcover, _⟩ := hactors p hp hl hT
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  let : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hnm : (cartan c).map (bOne_tree_map h) ≤
      normalizer (D.map (bOne_tree_map h) : Set (G₀ L S)) :=
    (map_mono hn).trans (D.le_normalizer_map (bOne_tree_map h))
  have hcov : D.map (bOne_tree_map h) ⊔ J.pCoreIn 2 = J := by
    have hJ : J.pCoreIn 2 = Q (reducedFamily L S)
        ((bOne_tree_cover h).vertex (p.getVert 6)) := sylowGenerated_core _
    rw [hJ]
    exact hcover
  have hle := coprime_normalizer_inf_le_pCore_supplement
    (halfPathActor_map_le_local h p 6 hl) hcov hnm
    ((cartan_odd c).of_dvd_right ((cartan c).card_map_dvd (bOne_tree_map h)))
  refine ⟨hle, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hle ⟨mem_map_of_mem (bOne_tree_map h) hx.1, hx.2⟩
  have hxv : x • p.getVert 6 = p.getVert 6 := hfix x hx.1 6
  have hyv : y • p.getVert 6 = p.getVert 6 := halfPathActor_le_midpoint_stabilizer hl hy
  have he := (bOne_tree_cover h).stabilizerEquiv (p.getVert 6) |>.injective
    (a₁ := ⟨y, hyv⟩) (a₂ := ⟨x, hxv⟩) (Subtype.ext hxy)
  have hyx : y = x := congrArg Subtype.val he
  exact hyx ▸ hy

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
