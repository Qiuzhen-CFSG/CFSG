module
public import CFSG.Quasithin.Chapter14.Section09.StrictActorKernel.SecondBall
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaIrreducible
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The strict source second-ball kernels and the same actor cores

At the noncommuting critical endpoint, the intrinsic D theorem identifies
all neighboring cores with the literal two-neighbor intersection. At the
opposite endpoint, the full original irreducibility of Q_beta/Z_beta forces
that intersection to be Z_beta: equality with Q_beta contradicts the
adjacent-core nonnormality theorem. Nonbinary local markings also eliminate
the odd part of the full second-ball kernel, so these are identities for the
actual second balls, not just their two-cores.

Apply the identities to the same half-path actor and original covering.
Its beta kernel is central elementary and maps exactly to the actor-image
intersection with the source Z_beta. At alpha its image is the actor-image
intersection with D. The printed nontrivial Cartan-kernel premise is retained.
Identifying D's complementary factor with the middle six-path root R_(i-3)^+
and constructing the natural alpha action and reversing reflection remain
necessary for DGS (14.9)(c) and apartment exchange.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.10)(d), pp.164--165; (14.5)(c), p.213; (14.7), p.214;
(14.9)(c), pp.215--216. The index there is j=i-r/2, hence j=i-3 for r=6.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Reduction Noncommuting NoncommutingProfile OriginalExtension SuzukiContainment Assembly.BTwoSource
open CommutingOneProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The actual second-ball two-core is the two-neighbor core intersection
at a noncommuting critical endpoint. -/
theorem source_second_core_eq_critical_intersection
    (h : HypothesisF11 L S) {v m w t : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F=2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (ht : (graph F).Adj v t) (htne : t≠m) :
    (ballKernel F v 2).pCoreIn 2=D F m t := by
  obtain ⟨k,f,fin,ch,alg,c,_⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  let _ := f
  let _ := fin
  let _ := ch
  let _ := alg
  have hd : D F m t=⨅ x : Vertex F, ⨅ (_ : (graph F).Adj v x), Q F x :=
    c.D_eq_neighbor_core_intersection (reduced_triple h) (reduced_kernel_sylow h) hb ht htne
  rw [←reduced_neighborCoreIntersection_eq_second_core h hvm.symm,hd]
  ext x
  simp only [neighborCoreIntersection,mem_iInf]
  constructor
  · intro hx z hz
    exact hx ⟨z,hz⟩
  · intro hx z
    exact hx z.val z.property

private theorem beta_second_core_eq_of_markings
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    (ballKernel F β 2).pCoreIn 2 = Z F β := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let I := neighborCoreIntersection F β
  have hIZ : I=Z F β := by
    have hIQ : I≤Q F β := source_neighborCoreIntersection_le_core H hab
    have hZI : Z F β≤I := by
      apply le_iInf
      intro z
      exact graph_Z_le_Q_of_short H (reduced_kernel_sylow h) (by
        change (graph F).dist β z < b F
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr z.property,hb]
        decide)
    have hQm : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
    have hIm : I.map ι≤(parabolic L S 1).pCoreIn 2 := hQm ▸ map_mono hIQ
    rcases NoncommutingProfile.Reduction.original_bTwo_nonbinary_beta_interval
        h hc hne hb hβu ht htne K e hK hD (I.map ι) hIm (map_mono hZI)
        (NoncommutingProfile.Reduction.original_second_core_normalized h) with hz | hq
    · exact map_injective (G₀ L S).subtype_injective hz
    · have hIQeq : I=Q F β := map_injective (G₀ L S).subtype_injective (hq.trans hQm.symm)
      have hQa : Q F β≤Q F α := hIQeq ▸ neighborCoreIntersection_le F hab
      exact False.elim ((reduced_graph_core_obstruction h β α hab.symm) (by
        rw [inf_eq_right.mpr hQa]
        exact CommutingNontrivial.stabilizer_normalizes_Q F β))
  rw [←reduced_neighborCoreIntersection_eq_second_core h hab]
  exact hIZ

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

include h hc hne hb hβu hns hlinear in
/-- Full original beta irreducibility and adjacent-core nonnormality
identify the second-ball two-core with the same source center. -/
theorem strict_source_beta_second_core_eq :
    (ballKernel F β 2).pCoreIn 2 = Z F β := by
  have hval : 3 ≤ Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet α) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,m,hm,hright,hpow,hext,hD,_⟩ :=
    original_core_layers h hc hne hb hβu ht htne hns
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hlinear
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := hright
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  let _ : Fintype k₁ := Fintype.ofFinite k₁
  let _ : CharP k₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP k₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let K : Bool → Type := fun i => if i then k₁ else k₀
  let _ : ∀ i, Field (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, Finite (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, CharP (K i) 2 := fun i => by cases i <;> assumption
  let e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  have hK : 2<Nat.card (K true) := by
    change 2<Nat.card k₁
    rw [h₁]
    exact (show 2^1<2^m from Nat.pow_lt_pow_right (by decide) hm)
  exact beta_second_core_eq_of_markings h hc hne hb hβu ht htne K e hK hD

include h hc hne hb hβu hns hlinear in
/-- The beta second-core identity transports along the literal reduced action. -/
theorem strict_source_beta_second_core_eq_at (v : Vertex F) (hv : v.type=true) :
    (ballKernel F v 2).pCoreIn 2=Z F v := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [←hg,ballKernel_translate,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    strict_source_beta_second_core_eq h hc hne hb hβu hns hlinear,Z_translate]

include h hc hne hb hβu in
private theorem beta_center_central_at (v : Vertex F) (hv : v.type=true) :
    Z F v ≤ centerIn (graphLocalGroup F v) := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  have hJ : graphLocalGroup F (g • β)=(graphLocalGroup F β).map (MulAut.conj g).toMonoidHom :=
    graphLocalGroup_conjugate (reduced_triple h) g β
  rw [←hg,Z_translate,hJ,←centerIn_map_equiv]
  exact map_mono hcentral

/-- On the beta orbit the actual strict actor core lies in the same source
center and is exactly the actor-image intersection with that center. -/
theorem strict_source_beta_actor_core_image
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hKn : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 6)).type=true) :
    let D := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
    let φ := bOne_tree_map h
    let v := (bOne_tree_cover h).vertex (p.getVert 6)
    (D.pCoreIn 2).map φ = D.map φ ⊓ Z F v := by
  intro D φ v
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hball := strict_source_actor_core_le_second_ball h hc hne hb hβu hns hlinear
    p hp hl hT hKn
  have hI : (D.pCoreIn 2).map φ ≤ neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    exact CommutingTrivial.two_subgroup_le_Q F z.val (reduced_kernel_sylow h z.val)
      ((isPGroup_pCoreIn 2 D).map φ)
      (hball.trans (ballKernel_succ_le F z.property 1))
  have hadj := (bOne_tree_cover h).hom.map_adj (p.adj_getVert_succ (i:=6) (by omega))
  have hIZ : neighborCoreIntersection F v=Z F v :=
    (reduced_neighborCoreIntersection_eq_second_core h hadj.symm).trans
      (strict_source_beta_second_core_eq_at h hc hne hb hβu hns hlinear v hv)
  have hZQ : Z F v≤Q F v := (source_Z_Q_U (reduced_triple h) v).1.trans (map_subtype_le _)
  have hker := (strict_source_actor_kernel_control h hc hne hb hβu hns hlinear p hp hl hT).2.2.2.2.1
  apply le_antisymm
  · exact le_inf (hker.le.trans inf_le_left) (hI.trans hIZ.le)
  · exact (inf_le_inf_left _ hZQ).trans hker.ge

/-- The same beta actor has central elementary two-core, with no natural
module assumption and no replacement of its quotient kernel. -/
theorem strict_source_beta_actor_core_central
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hKn : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 6)).type=true) :
    let D := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
    pCore 2 D ≤ center D ∧ IsElementaryAbelian 2 (pCore 2 D) := by
  intro D
  let φ := bOne_tree_map h
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  have hVZ : (D.pCoreIn 2).map φ≤Z F v :=
    (strict_source_beta_actor_core_image h hc hne hb hβu hns hlinear p hp hl hT hKn hv).le.trans inf_le_right
  have hZcentral := beta_center_central_at h hc hne hb hβu v hv
  have hcD : pCore 2 D≤center D := by
    intro x hx
    have hxZ := hVZ (mem_map_of_mem φ (mem_map_of_mem D.subtype hx))
    have hxc := (hZcentral hxZ).2
    apply mem_center_iff.mpr
    intro y
    apply halfPathLocalMap_injective h p 6 hl
    apply Subtype.ext
    change φ (y.val*x.val)=φ (x.val*y.val)
    simp only [map_mul]
    exact mem_centralizer_iff.mp hxc _
      (halfPathActor_map_le_local h p 6 hl (mem_map_of_mem φ y.property))
  have hele : IsElementaryAbelian 2 (pCore 2 D) := by
    let _ : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary (reduced_triple h) v
    let f : pCore 2 D →* Z F v :=
      (φ.comp (D.subtype.comp (pCore 2 D).subtype)).codRestrict _ (fun x =>
        hVZ (mem_map_of_mem φ (mem_map_of_mem D.subtype x.property)))
    apply IsElementaryAbelian.of_injective f
    intro x y he
    apply Subtype.ext
    apply halfPathLocalMap_injective h p 6 hl
    apply Subtype.ext
    change φ x.val.val=φ y.val.val
    exact congrArg (fun z : Z F v => (z:G₀ L S)) he
  exact ⟨hcD,hele⟩

/-- At the alpha midpoint the same strict actor kernel is the intersection
with the literal two-neighbor core D. This is the second-ball reduction
preceding the root-times-center factorization in DGS (14.9)(c). -/
theorem strict_source_alpha_actor_core_image
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hKn : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥)
    (hv : (bOne_tree_cover h).vertex (p.getVert 6)=α)
    {t : Vertex F} (ht : (graph F).Adj α t) (htne : t≠β) :
    let R := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
    let φ := bOne_tree_map h
    (R.pCoreIn 2).map φ = R.map φ ⊓ D F β t := by
  intro R φ
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hID : neighborCoreIntersection F α=D F β t :=
    (reduced_neighborCoreIntersection_eq_second_core h hab.symm).trans
      (source_second_core_eq_critical_intersection h hc hne hb hab hβu ht htne)
  have hDQ : D F β t≤Q F α :=
    hID ▸ source_neighborCoreIntersection_le_core (reduced_triple h) hab.symm
  have hball := strict_source_actor_core_le_second_ball h hc hne hb hβu hns hlinear
    p hp hl hT hKn
  rw [hv] at hball
  have hI : (R.pCoreIn 2).map φ≤neighborCoreIntersection F α := by
    apply le_iInf
    intro z
    exact CommutingTrivial.two_subgroup_le_Q F z.val (reduced_kernel_sylow h z.val)
      ((isPGroup_pCoreIn 2 R).map φ)
      (hball.trans (ballKernel_succ_le F z.property 1))
  have hker := (strict_source_actor_kernel_control h hc hne hb hβu hns hlinear p hp hl hT).2.2.2.2.1
  rw [hv] at hker
  apply le_antisymm
  · exact le_inf (hker.le.trans inf_le_left) (hI.trans hID.le)
  · exact (inf_le_inf_left _ hDQ).trans hker.ge

include h hc hne hb hβu hns hlinear in
/-- The strict nonbinary source makes the full second-ball kernel a
two-group. The full first-ball kernels remain distinct from their cores. -/
theorem strict_source_second_ball_eq_core
    {v w : Vertex F} (hvw : (graph F).Adj v w) :
    ballKernel F v 2=(ballKernel F v 2).pCoreIn 2 := by
  obtain ⟨K,fK,finK,chK,hK,e⟩ :=
    original_bTwo_strict_nonbinary_markings h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  have hkk : ballKernel F v 1⊓ballKernel F w 1=Q F v⊓Q F w :=
    CommutingTrivial.nonbinary_adjacent_kernel_intersection (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw
      (Classical.choice (e v)) (Classical.choice (e w)) (hK _) (hK _)
  have hBQ : ballKernel F v 2≤Q F v :=
    ((le_inf (ballKernel_antitone F v (by decide : 1≤2))
      (ballKernel_succ_le F hvw 1)).trans hkk.le).trans inf_le_left
  apply le_antisymm _ (pCoreIn_le 2 _)
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le hBQ)
    le_rfl (ballKernel F v 2).le_normalizer

include h hc hne hb hβu hns hlinear in
/-- The full alpha second-ball kernel is the original two-neighbor core D. -/
theorem strict_source_alpha_second_ball_eq
    {t : Vertex F} (ht : (graph F).Adj α t) (htne : t≠β) :
    ballKernel F α 2=D F β t := by
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  exact (strict_source_second_ball_eq_core h hc hne hb hβu hns hlinear hab).trans
    (source_second_core_eq_critical_intersection h hc hne hb hab hβu ht htne)

include h hc hne hb hβu hns hlinear in
/-- The full beta second-ball kernel is the same source Z, on every
translated beta vertex, with its actual neighboring edge retained. -/
theorem strict_source_beta_second_ball_eq_at
    {v w : Vertex F} (hvw : (graph F).Adj v w) (hv : v.type=true) :
    ballKernel F v 2=Z F v :=
  (strict_source_second_ball_eq_core h hc hne hb hβu hns hlinear hvw).trans
    (strict_source_beta_second_core_eq_at h hc hne hb hβu hns hlinear v hv)

end CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
