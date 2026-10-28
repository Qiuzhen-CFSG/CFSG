module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorPerfect
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictAlphaSecondCore
public import Theory.GroupTheory.Commutator.PerfectSylowLiftKernel

/-!
# The strict alpha small actor's whole kernel lies in its natural center

At an alpha midpoint, radius-two fixation places the actual smaller core
in D_alpha. Perfection puts the smaller actor in the intrinsic two-residual,
so its action on its whole core is trivial modulo Z_alpha. Quotient by the
intersection with Z_alpha. The original injective root remains an abelian
Sylow lift; central Sylow transfer eliminates the entire remaining kernel.
The resulting containment is on the actual original subgroup image.

The literal nontrivial Cartan/full-kernel condition is retained. Naturality
of a nonzero kernel is a subsequent consequence, not an input here.
Source: DGS, Groups and Graphs (1985), (14.9), pp.215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S

/-- The whole actual small-actor two-core maps into Z at every alpha
midpoint of the strict apartment, under the literal Cartan-kernel condition. -/
theorem strict_source_small_actor_alpha_core_le_center
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hCU : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥)
    (htype : ((bOne_tree_cover h).vertex (p.getVert 6)).type=false) :
    ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h)≤
      Z F ((bOne_tree_cover h).vertex (p.getVert 6)) := by
  let D := halfPathActor (X := (A).Universal) p 6
  let φ := bOne_tree_map h
  let δ := φ.comp D.subtype
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  let J := graphLocalGroup F v
  let M := D.map φ
  let V := (D.pCoreIn 2).map φ
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  let _ := strict_source_small_actor_perfect h hc hne hb hβu hns hlinear p hp hl hT
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  change g • base F v.type=v at hg
  rw [htype] at hg
  let m := g • base F true
  let w := g • u
  have hcm : IsCriticalPair F v w := by
    simpa only [hg] using criticalPair_translate F hc g
  have hnc : ⁅Z F v,Z F w⁆≠⊥ := by
    rw [←hg,Z_translate,Z_translate,←map_commutator]
    intro he
    exact hne (Subgroup.map_injective (MulAut.conj g).injective
      (he.trans (Subgroup.map_bot _).symm))
  have hvm : (graph F).Adj v m := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj
      (show (graph F).Adj (base F false) (base F true) from
        ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩)
    change (graph F).Adj (g • base F false) m at hh
    simpa only [hg] using hh
  have hmw : (graph F).Adj m w :=
    (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj hβu
  have hval : 3≤Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet v) (by rw [←Nat.card_coe_set_eq]; omega) m
  obtain ⟨hI,_,_,hmove⟩ := source_bTwo_alpha_second_core_at h hcm hnc hb hvm hmw ht htne
  have hVball : V≤ballKernel F v 2 :=
    (strict_source_small_actor_core_radius_two h hc hne hb hβu hns hlinear p hp hl hT hCU).1
  have hVI : V≤NoncommutingProfile.D F m t := by
    rw [←hI]
    apply le_iInf
    intro z
    exact CommutingTrivial.two_subgroup_le_Q F z.val (reduced_kernel_sylow h z.val)
      ((isPGroup_pCoreIn 2 D).map φ)
      (hVball.trans (ballKernel_succ_le F z.property 1))
  have hMR : M≤(pResidual 2 J).map J.subtype := by
    have hres : pResidual 2 D=⊤ :=
      strict_source_small_actor_two_residual h hc hne hb hβu hns hlinear p hp hl hT
    rintro _ ⟨x,hx,rfl⟩
    have hp : (⟨x,hx⟩:D)∈pResidual 2 D :=
      hres.symm ▸ mem_top _
    have hh := map_pResidual_le 2 (halfPathLocalMap h p 6 hl)
      (mem_map_of_mem (halfPathLocalMap h p 6 hl) hp)
    exact ⟨halfPathLocalMap h p 6 hl ⟨x,hx⟩,hh,rfl⟩
  have hVM : ⁅V,M⁆≤Z F v := (commutator_mono hVI hMR).trans hmove
  obtain ⟨K,fK,finK,chK,hK,e,hmarks⟩ :=
    strict_source_small_actor_marked_coordinates h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,hker,hRk,_,z,hR,_⟩ := hmarks p hp hl hT
  let k := K v.type
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e v))
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
  let Q := Matrix.SpecialLinearGroup.upperUnipotentSylow k 2
  let _ : IsMulCommutative Q := inferInstanceAs
    (IsMulCommutative (Matrix.SpecialLinearGroup.upperUnipotentHom k).range)
  let ZJ := (Z F v).subgroupOf J
  let _ : ZJ.Normal := normal_subgroupOf_of_le_normalizer
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Z F v))
  let ZD := ZJ.comap (halfPathLocalMap h p 6 hl)
  let N := f.ker ⊓ ZD
  have hmapker : f.ker.map δ=V := by
    rw [hfk]
    change (pCore 2 D).map (φ.comp D.subtype)=((pCore 2 D).map D.subtype).map φ
    rw [Subgroup.map_map]
  have hmaptop : (⊤ : Subgroup D).map δ=M := by
    rw [←Subgroup.map_map,←MonoidHom.range_eq_map,range_subtype]
  have hcomm : ⁅f.ker,(⊤ : Subgroup D)⁆≤N := by
    refine le_inf (le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal) ?_
    have hm : (⁅f.ker,(⊤ : Subgroup D)⁆).map δ≤Z F v := by
      rw [map_commutator,hmapker,hmaptop]
      exact hVM
    intro x hx
    change δ x∈Z F v
    exact hm (mem_map_of_mem δ hx)
  have hkN := CentralExtension.kernel_le_of_commutator_le_of_abelian_sylow_lift
    f (by rw [hfk]; exact pCore_isPGroup) Q R hR
    (by rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]; exact hRk)
    N inf_le_left hcomm
  change V≤Z F v
  rw [←hmapker]
  rintro _ ⟨x,hx,rfl⟩
  exact (hkN hx).2

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
