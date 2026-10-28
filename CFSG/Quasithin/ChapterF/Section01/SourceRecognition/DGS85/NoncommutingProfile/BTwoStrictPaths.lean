module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoStrictCoreOrders

/-!
# Strict Chapter 10 path parameters in every characteristic-two field

Terminal separation for the actual opposite-center residual constructs a
seven-path with odd fixer. The strict edge two-core order is the number
of nonbacktracking seven-paths through an edge, so its orbit fills that set.
Reversal gives both orientations. Every source path of length at most six
is regular; every longer source path has odd fixer and is nonregular.
Thus the source extrema are r = 6 and s = 7, including closed source paths.

The original quotient markings and reduced-to-original core maps are used
throughout. No nonsolvability assumption or nonbinary field restriction is
needed. The irreducibility clause of (10.10)(d) remains a separate obligation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed pp.159--162, and (10.10)(a)--(c), printed p.164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk SimpleGraph.BasedWalk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Noncommuting
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

private theorem edge_core_card_eq_base {a d : Vertex F} (had : (graph F).Adj a d) :
    Nat.card ((stabilizer F a ⊓ stabilizer F d).pCoreIn 2) =
      Nat.card ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2) := by
  obtain ⟨g,ha,hd⟩ := incident_common_translate F had.2
  have he : (stabilizer F a ⊓ stabilizer F d).pCoreIn 2 =
      ((stabilizer F (base F a.type) ⊓ stabilizer F (base F d.type)).pCoreIn 2).map
        (MulAut.conj g).toMonoidHom := by
    rw [←ha,←hd,stabilizer_translate,stabilizer_translate,
      ←map_inf _ _ _ (MulAut.conj g).injective,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    rfl
  rw [he,card_map_of_injective (MulAut.conj g).injective]
  have hne := had.1
  cases hat : a.type <;> cases hdt : d.type
  · exact False.elim (hne (hat.trans hdt.symm))
  · rfl
  · rw [inf_comm]
  · exact False.elim (hne (hat.trans hdt.symm))

private theorem strict_edge_card
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    {a d : Vertex F} (had : (graph F).Adj a d) :
    Nat.card ((stabilizer F a⊓stabilizer F d).pCoreIn 2)=
      Nat.card (K false)^3*Nat.card (K true)^3 := by
  rw [edge_core_card_eq_base had]
  obtain ⟨_,_,_,_,_,_,_,_,_,hcard,_,_⟩ :=
    original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  have hm : ((stabilizer F α⊓stabilizer F β).pCoreIn 2).map ι=
      (commonBorel L S).pCoreIn 2 := by
    have hi : stabilizer F α⊓stabilizer F β=(B₀ L S).subgroupOf (G₀ L S) := by
      simp only [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
      exact (reduced_triple h).intersection
    rw [hi,map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le (show B₀ L S≤G₀ L S from le_sup_right.trans le_sup_left),B₀_core h]
  rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hm]
  exact hcard

/-- The terminal separation constructs an actual seven-path with odd fixer,
without a nonsolvability or field-size restriction. -/
theorem original_bTwo_terminal_seven_path_odd
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hy : (graph F).Adj u y) (hyne : y≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i)) :
    ∃ g : G₀ L S, g∈graphLocalGroup F α ∧ g • β=t ∧
      ∀ z : Vertex F, (graph F).Adj y z → z≠u →
        ∃ p : BasedWalk (graph F) 7 (g • y),
          p.vertices=[g • y,g • u,t,α,β,u,y,z] ∧
          p.Nonbacktracking ∧ Odd (Nat.card (pathStabilizer F p)) := by
  obtain ⟨g,hg,hgt,hsep⟩ := original_bTwo_terminal_separation h hc hne hb hβu ht htne K e
  change g • β=t at hgt
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  let g' : c.actor := ⟨g,hactor.symm ▸ hg⟩
  have hop : c.quotient g'∉normalizer (c.imageSylow:Set SL(2,k)) := by
    intro he
    exact htne (hgt.symm.trans (c.normalizer_fixes_neighbor H g' he))
  obtain ⟨d,hdactor,_⟩ := c.exists_oppositeGeometry H (reduced_kernel_sylow h) hb g' hgt hop
  let R := bTwoResidual F β t u (g • u)
  have hfour : R=(D F β t⊓Q F u)⊓Q F (g • u) :=
    (d.residual_eq_source H (reduced_kernel_sylow h) hb (hdactor.symm ▸ hω)).symm
  have hzero : R⊓Q F y=⊥ := by
    apply map_injective (G₀ L S).subtype_injective
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,Subgroup.map_bot]
    have hRm : R.map ι=
        ((parabolic L S 1).pCoreIn 2⊓(Q F t).map ι)⊓
          centralizer (((Z F u).map ι⊔(Z F (g • u)).map ι:Subgroup G):Set G) := by
      change (D F β t⊓centralizer ((Z F u⊔Z F (g • u):Subgroup (G₀ L S)):Set (G₀ L S))).map ι=_
      rw [←map_inf_centralizer_of_injective ι (G₀ L S).subtype_injective,Subgroup.map_sup]
      change (Q F β⊓Q F t).map ι⊓_= _
      have hQbm : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 :=
        reduced_base_Q_map h true
      rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
    rw [hRm]
    exact hsep y hy hyne
  refine ⟨g,hg,hgt,?_⟩
  intro z hyz hzu
  have hgygu : (graph F).Adj (g • y) (g • u) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hy.symm
  have hgut : (graph F).Adj (g • u) t := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    rw [hgt] at hh
    exact hh.symm
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let p : BasedWalk (graph F) 7 (g • y) :=
    ⟨⟨g • u,hgygu⟩,⟨⟨t,hgut⟩,⟨⟨α,ht.symm⟩,⟨⟨β,hab⟩,
      ⟨⟨u,hβu⟩,⟨⟨y,hy⟩,⟨⟨z,hyz⟩,PUnit.unit⟩⟩⟩⟩⟩⟩⟩
  have hua : u ≠ α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    omega
  have hgyt : g • y ≠ t := by
    intro he
    apply hyne
    apply MulAction.injective g
    exact he.trans hgt.symm
  have hguα : g • u ≠ α := by
    intro he
    apply hua
    apply MulAction.injective g
    exact he.trans (sylowGenerated_le _ hg).symm
  have hp : p.Nonbacktracking :=
    ⟨hgyt.symm,hguα.symm,htne.symm,hua,hyne,hzu,True.intro⟩
  refine ⟨p,rfl,hp,?_⟩
  apply Assembly.BTwoSource.original_bTwo_seven_path_fixer_odd_of_residual h (t := t) (z := z) hc hne g p hp rfl
  rw [← hfour]
  exact hzero


private theorem nb_ofWalk_iff {V : Type*} {Γ : SimpleGraph V} {a b : V}
    (p : Γ.Walk a b) :
    (ofWalk p).Nonbacktracking ↔ ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2) := by
  induction p with
  | nil =>
    constructor
    · intro _ i hi; simp only [length_nil] at hi; omega
    · intro _; trivial
  | @cons a b c hab p ih =>
    cases p with
    | nil =>
      constructor
      · intro _ i hi; simp only [length_cons,length_nil] at hi; omega
      · intro _; trivial
    | @cons b d c hbd p =>
      change (d ≠ a ∧ (ofWalk (Walk.cons hbd p)).Nonbacktracking) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hne,hp⟩ i hi
        cases i with
        | zero => simpa only [getVert_zero,getVert_cons_succ] using hne.symm
        | succ i => exact hp i (by simp only [length_cons] at *; omega)
      · intro hp
        refine ⟨by simpa only [getVert_zero,getVert_cons_succ] using
          (hp 0 (by simp only [length_cons]; omega)).symm,?_⟩
        intro i hi
        exact hp (i+1) (by simp only [length_cons] at *; omega)

private theorem sourcePath_nonbacktracking {a b : Vertex F}
    (p : (graph F).Walk a b) (hp : IsSourcePath p) (hne : p.length ≠ 2) :
    (ofWalk p).Nonbacktracking := by
  rcases hp with hp | ⟨hab,hp⟩
  · exact nonbacktracking_ofWalk_of_isPath p hp
  · subst b
    rw [nb_ofWalk_iff]
    intro i hi he
    by_cases hlt : i+2 < p.length
    · have h1 : i ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have h2 : i+2 ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have hh := hp.getVert_injOn h1 h2
        (by rwa [getVert_dropLast (by omega : i < p.length), getVert_dropLast hlt])
      omega
    · have hlast : i+2 = p.length := by omega
      have h1 : i ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have hh := hp.getVert_injOn h1 (Nat.zero_le _) (by
        rw [getVert_dropLast (by omega : i < p.length),getVert_zero]
        rwa [hlast,getVert_length] at he)
      omega

/-- DGS (10.10)(a),(c) in every strict characteristic-two branch:
r = 6, s = 7, and all long source paths have odd fixers, with the original
endpoint markings and the source closed-path convention. -/
theorem original_bTwo_strict_source_path_parameters
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    HasSourcePathParameters (P:=fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
      ∀ {a d : Vertex F} (p : (graph F).Walk a d),
        IsSourcePath p → 7≤p.length →
          Odd (Nat.card (pathFixer (X:=G₀ L S) p)) := by
  have hval0 (v : Vertex F) : 3≤Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s:=(graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; have := hval0 u; omega) β
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = Nat.card (K i)+1 := by
    have hadj : (graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩
    have he := source_linear_edge_index_of_quotient H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hadj (eG i)
    rw [show stabilizer F (base F i) = F i from
        Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F (!i)) = F (!i) from
        Subgroup.CosetGeometry.stabilizer_base _ _] at he
    exact he
  have hval := card_neighbors_of_indices F (fun i => Nat.card (K i)+1) hi
  have hval3 (v : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) v.type
  have hvalodd (v : Vertex F) : Odd (Nat.card ((graph F).neighborSet v)) := by
    rw [hval]
    have heven : Even (Nat.card (K v.type)) := by
      let := Fintype.ofFinite (K v.type)
      rw [Nat.card_eq_fintype_card,even_iff_two_dvd]
      exact (CharP.cast_eq_zero_iff (K v.type) 2 _).mp
        (FiniteField.cast_card_eq_zero (K v.type))
    exact heven.add_one
  obtain ⟨z,hyz,hzu⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet y)
    (by rw [←Nat.card_coe_set_eq]; have := hval3 y; omega) u
  obtain ⟨g,_,_,hg⟩ :=
    original_bTwo_terminal_seven_path_odd h hc hne hb hβu ht htne hy hyne K e
  obtain ⟨p,_,hp,ho⟩ := hg z hyz hzu
  obtain ⟨htrans,hodd7⟩ := seven_path_geometry_of_odd_witness F
    (fun i => Nat.card (K i)) (fun _ => Nat.card_pos) hval
    (fun {_ _} had =>
      strict_edge_card h hc hne hb hβu ht htne K e hD had)
    p hp ho
  have hs : 7 ≤ sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) :=
    sourceS_ge_of_root_transitive H (reduced_vertex_sylow h) (fun i => htrans (base F i))
  have hreg {a d : Vertex F} (q : (graph F).Walk a d)
      (hq : IsSourcePath q) (hl : q.length ≤ 6) : PathRegular q := by
    by_contra hbad
    have hmin := (sourceS_spec H (reduced_vertex_sylow h)).2.2
      (show q.length ∈ sourceNonregularLengths
          (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) from
        ⟨a,d,q,hq,rfl,hbad⟩)
    omega
  have hodd {a d : Vertex F} (q : (graph F).Walk a d)
      (hq : IsSourcePath q) (hl : 7 ≤ q.length) :
      Odd (Nat.card (pathFixer (X := G₀ L S) q)) := by
    have hh := long_path_fixer_odd_of_seven F hodd7 (ofWalk q)
      (sourcePath_nonbacktracking q hq (by omega)) hl
    rwa [pathStabilizer_ofWalk] at hh
  exact CommutingOneProfile.OddValenceSourceGeometry.source_path_parameters_six_seven
    (fun i => (P₀ L S i).subgroupOf (G₀ L S)) (fun v => ⟨hval3 v,hvalodd v⟩) hreg hodd

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
