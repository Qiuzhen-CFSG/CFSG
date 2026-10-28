module
public import CFSG.Quasithin.Chapter14.Section09.StrictActorKernel.Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedPropagation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SecondKernel

/-!
# The strict actor core fixes the second ball

A nontrivial Cartan factor in the midpoint neighborhood kernel centralizes
the two-root actor. The adjacent full kernels intersect in the two-cores,
so this odd factor acts faithfully at the next vertex. The Cartan-normalized
core therefore lies in that neighbor's core. Supplementation makes the actor
transitive on the midpoint star; its own core is normal in that actor, so
conjugation puts it in every neighboring core and hence in the second ball.

This proves the strict nonbinary instance of DGS (14.5)(c) used in (14.9).
It retains the printed nontrivial Cartan-kernel premise. It does not identify
the second-ball subgroup, or the actor core, with the source Z_i.
Source: DGS, *Groups and Graphs* (1985), pp.213,215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment Assembly.BTwoSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S

private theorem mapped_cartan_complement
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (hCE : (cartan c).map (bOne_tree_map h) ≤ stabilizer F v ⊓ stabilizer F w) :
    Disjoint ((cartan c).map (bOne_tree_map h)) ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2) ∧
    (cartan c).map (bOne_tree_map h) ⊔ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 =
      stabilizer F v ⊓ stabilizer F w := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=Universal.cosetFamily A false ⊓ Universal.cosetFamily A true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E ≤ normalizer (W : Set (G₀ L S)) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hC0 (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false)=F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F (base F true)=F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hbase : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  exact CommutingTrivial.path_cartan_complement_at_edge (reduced_triple h)
    hbase hvw C (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The printed nontrivial Cartan-kernel hypothesis puts the same strict
actor core in the original second-ball kernel, with no naturality premise. -/
theorem strict_source_actor_core_le_second_ball
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hKn : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥) :
    ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h) ≤
      ballKernel F ((bOne_tree_cover h).vertex (p.getVert 6)) 2 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let D := halfPathActor (X := (A).Universal) p 6
  let R := D.map φ
  let E := (D.pCoreIn 2).map φ
  let C := (cartan (chosenCartans h)).map φ
  let v := cov.vertex (p.getVert 6)
  let w := cov.vertex (p.getVert 7)
  let r := cov.vertex (p.getVert 8)
  let T := C ⊓ U F v
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  obtain ⟨K,fK,finK,chK,hK,e,hactors⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,_,hcover,_⟩ := hactors p hp hl hT
  obtain ⟨hCD,_,_,_,_,hbound⟩ :=
    strict_source_actor_kernel_control h hc hne hb hβu hns hlinear p hp hl hT
  have hEQ : E≤Q F v := hbound.trans inf_le_left
  have hTC : T≤centralizer (E : Set (G₀ L S)) :=
    le_centralizer_iff.mp (hbound.trans inf_le_right)
  have hnorm : normalizer (D : Set (A).Universal) ≤ normalizer (D.pCoreIn 2 : Set (A).Universal) :=
    normalizer_le_normalizer_characteristic_image D (pCore 2 D)
  have hCE : C≤normalizer (E : Set (G₀ L S)) :=
    (map_mono (hCD.trans hnorm)).trans ((D.pCoreIn 2).le_normalizer_map φ)
  have hRE : R≤normalizer (E : Set (G₀ L S)) :=
    (map_mono (D.le_normalizer.trans hnorm)).trans ((D.pCoreIn 2).le_normalizer_map φ)
  have h67 := p.adj_getVert_succ (i:=6) (by omega)
  have h78 := p.adj_getVert_succ (i:=7) (by omega)
  have hvw : (graph F).Adj v w := cov.hom.map_adj h67
  have hwr : (graph F).Adj w r := cov.hom.map_adj h78
  have hrv : r≠v := by
    intro he
    have he' := (cov.neighbor_bijective (p.getVert 7)).1
      (a₁:=⟨p.getVert 8,h78⟩) (a₂:=⟨p.getVert 6,h67.symm⟩) (Subtype.ext he)
    have hh := hp.getVert_injOn (by omega : 8≤p.length) (by omega : 6≤p.length)
      (congrArg Subtype.val he')
    omega
  have hfix (j : ℕ) : C≤stabilizer F (cov.vertex (p.getVert j)) := by
    rintro _ ⟨x,hx,rfl⟩
    change φ x • cov.vertex (p.getVert j)=_
    rw [←cov.vertex_smul]
    exact congrArg cov.vertex (reflectionApartment_fixed (chosenCartans h)
      (strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear).reflection
      (strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear).normalizes x hx _
      (hT _ (p.getVert_mem_support j)))
  have hCv : C≤stabilizer F w⊓stabilizer F v := le_inf (hfix 7) (hfix 6)
  obtain ⟨hdisC,hgenC⟩ := mapped_cartan_complement h (chosenCartans h) hvw.symm hCv
  have hkk := CommutingTrivial.nonbinary_adjacent_kernel_intersection (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw (e v) (e w) (hK _) (hK _)
  have hodd : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd (chosenCartans h))).of_dvd_nat
    ((cartan (chosenCartans h)).card_map_dvd φ)
  let _ : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  have hdisQ : Disjoint C (Q F v) := by
    have hpQ : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 (stabilizer F v)
    obtain ⟨m,hm⟩ := hpQ.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact hodd.coprime_two_right.pow_right m)
  have hdisT : Disjoint T (ballKernel F w 1) := by
    apply disjoint_def.mpr
    intro x hx hxw
    exact disjoint_def.mp hdisQ hx.1 ((hkk.le ⟨hx.2,hxw⟩).1)
  have hEw : E≤Q F w := CommutingTrivial.cartan_normalized_centralizing_two_subgroup_le_core
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hvw.symm hwr hrv (e w) C E T hCv hdisC hgenC
    (le_inf (hEQ.trans ((source_Z_Q_U (reduced_triple h) v).2.trans
      ((ballKernel_one_le_edge F hvw).trans inf_le_right))) (hEQ.trans (Q_le_stabilizer F v)))
    ((isPGroup_pCoreIn 2 D).map φ) hCE inf_le_left (inf_le_left.trans (hfix 8)) hTC hKn hdisT
  have hRQ : R≤normalizer (Q F v : Set (G₀ L S)) :=
    (halfPathActor_map_le_local h p 6 hl).trans ((sylowGenerated_le _).trans
      (CommutingNontrivial.stabilizer_normalizes_Q F v))
  have hI : E≤CommutingOneProfile.neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) v ⟨w,hvw⟩ z
    have hgprod : g∈(R : Set (G₀ L S))*(Q F v : Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hRQ,hcover]
      exact hg
    obtain ⟨s,hs,q,hq,hsq⟩ := hgprod
    have hqw : q • w=w := (source_Z_Q_U (reduced_triple h) v).2 hq w
      ((mem_ball_one F v w).mpr (Or.inl hvw))
    have hsz : s • w=z.val := by
      change g • w=z.val at hgz
      rwa [←hsq,mul_smul,hqw] at hgz
    intro x hx
    have hi : s⁻¹*x*s∈E := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (hRE (R.inv_mem hs)) x).mp hx
    have hh := mem_map_of_mem (MulAut.conj s).toMonoidHom (hEw hi)
    rw [←Q_translate,hsz] at hh
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_assoc,
      mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
  exact hI.trans (CommutingOneProfile.source_neighborCoreIntersection_le_second_kernel
    (reduced_triple h) hvw.symm)

/-- The same core fixes the second ball of the actual universal tree; the
covering lift is used only after proving the reduced second-ball placement. -/
theorem strict_source_actor_core_fixes_second_ball
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hKn : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥) :
    (halfPathActor (X := (A).Universal) p 6).pCoreIn 2 ≤
      ballKernel (Universal.cosetFamily A) (p.getVert 6) 2 := by
  intro x hx
  have hfix := halfPathActor_le_midpoint_stabilizer hl (pCoreIn_le 2 _ hx)
  have hdown := strict_source_actor_core_le_second_ball h hc hne hb hβu hns hlinear
    p hp hl hT hKn (mem_map_of_mem (bOne_tree_map h) hx)
  exact (bOne_tree_cover h).ballKernel_lift (p.getVert 6) 2 x hfix hdown

end CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
