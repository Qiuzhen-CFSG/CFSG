module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSharpSection

/-!
# Intersections of a proper beta section in the equal-field case

For the strict nonbinary-beta branch of DGS (10.10), a proper invariant
section meets the natural alpha center exactly in Z_beta. The source Cartan
at the critical endpoint gives a dichotomy: a larger intersection contains
the whole alpha center. Its beta conjugates then contain V_beta, so the
product Q_beta = V_beta D_alpha contradicts the proper-quotient lower bound.

The residual decomposition D_alpha = Z_alpha R_alpha sharpens this to
N intersect D_alpha = Z_beta. Any residual part has alpha-core commutator
inside the beta-center line. The opposite critical centers normalize that
commutator, so irreducibility of the natural alpha-center action makes it
trivial. The vanishing local central omega then removes the residual part.

The sharp section orders now give |N intersect Q_alpha| = q_beta squared
and N not contained in Q_alpha. All maps are the original reduced-to-original
inclusion, and normalization is under the full original beta stabilizer.
The following source argument must still construct the abelian subgroup
from the two conjugate intersections and use the full radius-two kernel;
this module does not assert the final equal-field irreducibility conclusion.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(d), printed p.165, using (10.4), (10.7), and the natural center action.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The source Cartan forces the center intersection to be a line or the whole center. -/
theorem reduced_bTwo_invariant_center_dichotomy
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (N : Subgroup (G₀ L S)) (hZN : Z F β≤N)
    (hPN : stabilizer F β≤normalizer (N:Set (G₀ L S))) :
    N⊓Z F α=Z F β ∨ Z F α≤N := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hSyl := reduced_vertex_sylow h
  have hS := reduced_kernel_sylow h
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hline := (c.central_critical_intersections H hB hSyl hb hcentral).1
  have hZβα : Z F β≤Z F α := hline ▸ inf_le_left
  by_cases hsmall : N⊓Z F α≤Q F u
  · exact Or.inl (le_antisymm ((le_inf inf_le_right hsmall).trans hline.le) (le_inf hZN hZβα))
  right
  have hval : 3≤Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H hSyl u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s:=(graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨C,hfix,hd,hgen,ho,rest⟩ :=
    Assembly.BTwoSource.original_bTwo_path_cartan_residual h hc hne hb hβu ht htne hy hyne
  have hCE : C≤stabilizer F α⊓stabilizer F β :=
    le_inf (fun a ha => (hfix ha).1.1.1.2) (fun a ha => (hfix ha).1.1.2)
  have hCu : C≤stabilizer F u⊓stabilizer F β :=
    le_inf (fun a ha => (hfix ha).1.2) (hCE.trans inf_le_right)
  obtain ⟨hdu,hgenu⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab hβu.symm C hCE hCu ho hd hgen
  obtain ⟨n,hn,K,fK,finK,hK,⟨eK⟩⟩ := reduced_noncommuting_actor_quotients_linear h hc hne u
  let _ := fK
  let _ := finK
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eu := eK.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).symm
  have hZβ : Z F α≤Q F β := graph_Z_le_Q_of_short H hS (by
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab,hb]; decide)
  have hQuβ : Q F u≤stabilizer F β :=
    (source_Z_Q_U H u).2.trans ((ballKernel_one_le_edge F hβu.symm).trans inf_le_right)
  have hEu : Z F α⊔Q F u=(stabilizer F u⊓stabilizer F β).pCoreIn 2 := by
    obtain ⟨T,hT⟩ := c.critical_product
    have hE : Z F α⊔Q F u≤stabilizer F u⊓stabilizer F β :=
      le_inf (hT ▸ map_subtype_le _) (sup_le (hZβ.trans (Q_le_stabilizer F β)) hQuβ)
    exact hT.symm.trans (sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow H hB hβu.symm) T (hT ▸ hE))
  have hZaN : stabilizer F α≤normalizer (Z F α:Set (G₀ L S)) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F α)).mp (Z_normal F α)
  have hnA : C≤normalizer ((N⊓Z F α:Subgroup (G₀ L S)):Set (G₀ L S)) :=
    (le_inf ((hCE.trans inf_le_right).trans hPN) ((hCE.trans inf_le_left).trans hZaN)).trans
      inf_normalizer_le_normalizer_inf
  have hAS : N⊓Z F α≤(stabilizer F u⊓stabilizer F β).pCoreIn 2 :=
    inf_le_right.trans (le_sup_left.trans hEu.le)
  have hgenA := Assembly.BTwoSource.cartan_normalized_two_subgroup_core_product H hB hSyl hβu.symm
    eu C (N⊓Z F α) hCu hdu hgenu hAS
    ((isPGroup_pCoreIn 2 (stabilizer F u⊓stabilizer F β)).to_le hAS) hnA hsmall
  have hnQ : N⊓Z F α≤normalizer (Q F u:Set (G₀ L S)) :=
    (hAS.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans (CommutingNontrivial.stabilizer_normalizes_Q F u)
  intro z hz
  have hzprod : z∈((N⊓Z F α:Subgroup (G₀ L S)):Set (G₀ L S))*(Q F u:Set (G₀ L S)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hnQ,hgenA]
    exact hEu ▸ mem_sup_left hz
  obtain ⟨a,ha,b,hb',rfl⟩ := hzprod
  have hbZ : b∈Z F α := by
    simpa only [inv_mul_cancel_left] using (Z F α).mul_mem ((Z F α).inv_mem ha.2) hz
  exact N.mul_mem ha.1 (hZN (hline ▸ (show b∈Z F α⊓Q F u from ⟨hbZ,hb'⟩)))


/-- A proper invariant beta section cannot contain the whole alpha center. -/
theorem original_bTwo_nonbinary_beta_proper_excludes_center
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    ¬ (Z F α).map ι≤N := by
  intro hZaN
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hLmap : (graphLocalGroup F β).map ι=enlargedEndpoint L S 1 := reduced_graphLocalGroup_image h true
  have hVN : (V F β 1).map ι≤N := by
    rw [←graph_intrinsic_radius_span H (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab
      (center_le_of_central_neighbor H (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab hcentral),
      map_conjugateSpanBy,hLmap]
    exact conjugateSpanBy_le hZaN ((show enlargedEndpoint L S 1≤parabolic L S 1 from
      sup_le (starredParabolic_le 1) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))).trans hPN)
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁⊓(Q F t).map ι
  let Z₀ := (Z F α).map ι
  have hproduct : Q₁=(V F β 1).map ι⊔D₀ := original_bTwo_beta_core_product h hb c ht htne
  have hDN : N⊔D₀=Q₁ := by
    apply le_antisymm (sup_le hNQ.le inf_le_left)
    change Q₁≤N⊔D₀
    rw [hproduct]
    exact sup_le (hVN.trans le_sup_left) le_sup_right
  obtain ⟨hZD,_,_,hZ,_,hDcard,_⟩ := original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  change Z₀≤D₀ at hZD
  change Nat.card Z₀=Nat.card (K false)^2 at hZ
  change Nat.card D₀=Nat.card (K false)^2*Nat.card (K true) at hDcard
  have hZi : Z₀.relIndex D₀=Nat.card (K true) := by
    have hf := relIndex_mul_card_of_le hZD
    rw [hZ,hDcard,mul_comm (Nat.card (K false)^2)] at hf
    exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos Nat.card_pos) hf
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : (N.subgroupOf Q₁).Normal := normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 _).trans hPN)
  have hindex : N.relIndex Q₁=N.relIndex D₀ := by
    have hh := relIndex_sup_left (D₀.subgroupOf Q₁) (N.subgroupOf Q₁)
    rw [←subgroupOf_sup hNQ.le (show D₀≤Q₁ from inf_le_left),hDN,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show D₀≤Q₁ from inf_le_left)] at hh
    exact hh
  have hbound : N.relIndex Q₁≤Nat.card (K true) := by
    rw [hindex,←hZi]
    exact relIndex_le_of_le_left hZaN (hZi ▸ Nat.ne_of_gt Nat.card_pos)
  have hlower := original_bTwo_nonbinary_beta_proper_quotient_bound h hc hne hb hβu ht htne K e hK hD N hNQ hPN
  change Nat.card (K true)^2≤N.relIndex Q₁ at hlower
  nlinarith only [hK,hlower,hbound]


/-- The proper beta section meets the alpha center in precisely the beta center. -/
theorem original_bTwo_nonbinary_beta_proper_center_intersection
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι≤N)
    (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    N⊓(Z F α).map ι=(Z F β).map ι := by
  have hQmap : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hN0 : N≤G₀ L S := hNQ.le.trans (hQmap.ge.trans (map_subtype_le _))
  let N₀ := N.subgroupOf (G₀ L S)
  have hNm : N₀.map ι=N := map_subgroupOf_eq_of_le hN0
  have hZN₀ : Z F β≤N₀ := map_le_iff_le_comap.mp hZN
  have hn : stabilizer F β≤normalizer (N₀:Set (G₀ L S)) := by
    intro x hx
    have hxP : (x:G)∈P₀ L S 1 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hx
      exact hx
    exact le_normalizer_comap ι (hPN (P₀_le h 1 hxP))
  rcases reduced_bTwo_invariant_center_dichotomy h hc hne hb hβu ht htne N₀ hZN₀ hn with he|he
  · have hh := congrArg (map ι) he
    rwa [map_inf _ _ _ (G₀ L S).subtype_injective,hNm] at hh
  · exact False.elim ((original_bTwo_nonbinary_beta_proper_excludes_center h hc hne hb hβu ht htne
      K e hK hD N hNQ hPN) (by simpa only [hNm] using map_mono (f:=ι) he))


/-- The residual part of a beta-invariant section cannot hide in D_alpha. -/
theorem reduced_bTwo_strict_beta_section_D_intersection
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup (G₀ L S)) (hNQ : N≤Q F β)
    (hPN : stabilizer F β≤normalizer (N:Set (G₀ L S)))
    (hNZa : N⊓Z F α=Z F β) : N⊓D F β t=Z F β := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hSyl := reduced_vertex_sylow h
  have hS := reduced_kernel_sylow h
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hω := c.omega_eq_bot_of_central_neighbor H hB hSyl hactor hcentral
  have hnot := reduced_graph_core_obstruction h α β hab
  obtain ⟨n,hn,K,fK,finK,hK,⟨eK⟩⟩ := reduced_bTwo_middle_quotient_linear h hc hne hb hab hβu
  let _ := fK
  let _ := finK
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eβ := eK.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).symm
  have hDne : D F β t≠Z F α := by
    intro he
    apply hD
    have hh := congrArg (map ι) he
    have hQmap : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
    simpa only [D,map_inf _ _ _ (G₀ L S).subtype_injective,hQmap] using hh
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift H ht htne
  obtain ⟨d,hdactor,hker⟩ := c.exists_oppositeGeometry H hS hb g hg hop
  let W := Z F u⊔Z F ((g:G₀ L S) • u)
  let R := bTwoResidual F β t u ((g:G₀ L S) • u)
  have hdec : D F β t=Z F α⊔R := by
    rw [d.decomposition H hS hb,d.residual_eq_source H hS hb (hdactor.symm ▸ hω)]
  have hZD : Z F α≤D F β t := hdec ▸ le_sup_left
  have hgen : W⊔Q F α=c.actor := d.actor_generators.symm.trans hdactor
  have hRQ : R≤Q F α := inf_le_left.trans d.separated
  have hDel : IsElementaryAbelian 2 (D F β t) :=
    d.elementary H hS hb c.sylow (hdactor.symm ▸ c.sylow_le_actor)
      (disjoint_iff.mpr (bot_unique (hker.trans hω.le)))
  let _ := hDel
  have hRcomm : ⁅R,Q F α⁆=Z F α := c.strict_residual_core_commutator H hB hSyl hb hactor
    hcentral ht htne hcomm hnot eβ hDne (LinearEquiv.refl _ _) g hg
  let M := (N⊔Z F α)⊓R
  let J := ⁅M,Q F α⁆
  have hJZ : J≤Z F α := (commutator_mono inf_le_right le_rfl).trans hRcomm.le
  have hQaβ : Q F α≤stabilizer F β :=
    (source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F hab).trans inf_le_right)
  have hZaβ : Z F α≤stabilizer F β := hZD.trans (inf_le_left.trans (Q_le_stabilizer F β))
  have hNZcomm : ⁅N⊔Z F α,Q F α⁆≤N := by
    apply commutator_sup_le_of_relative_normal (stabilizer F β) N (Z F α) (Q F α) N
      hPN (hNQ.trans (Q_le_stabilizer F β)) hZaβ
    · exact le_normalizer_iff_commutator_le_left.mp (hQaβ.trans hPN)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (graph_Q_centralizes_Z H α))).le.trans bot_le
  have hJN : J≤N := (commutator_mono inf_le_left le_rfl).trans hNZcomm
  have hJβ : J≤Z F β := (le_inf hJN hJZ).trans hNZa.le
  have hMC : M≤centralizer (W:Set (G₀ L S)) := inf_le_right.trans inf_le_right
  have hnQ : c.actor≤normalizer (Q F α:Set (G₀ L S)) :=
    c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F α)
  have hnJ : c.actor≤normalizer (J:Set (G₀ L S)) := by
    rw [←hgen]
    apply sup_le ?_ (normalizer_commutator_ge_right M (Q F α))
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅M,Q F α⁆).map (MulAut.conj a).toMonoidHom=⁅M,Q F α⁆
    have hMm : M.map (MulAut.conj a).toMonoidHom=M :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) ((le_centralizer_iff.mp hMC) ha))
    have hQm : (Q F α).map (MulAut.conj a).toMonoidHom=Q F α :=
      mem_normalizer_iff_map_conj_eq.mp (hnQ (hgen ▸ mem_sup_left ha))
    rw [map_commutator,hMm,hQm]
  obtain ⟨eZ,heZ⟩ := c.center_natural_coordinates (LinearEquiv.refl _ _)
  let : c.representation.IsIrreducible := Representation.RankOne.QuadraticRecognition.irreducible_of_natural_coordinates c.representation eZ heZ
  let : Representation.IsIrreducible (c.representation.comp c.quotient) :=
    (Representation.irreducible_comp_surjective_iff c.quotient c.onto c.representation).mpr inferInstance
  have hJbot : J=⊥ := by
    rcases c.coordinates.eq_kernel_or_section J (hω ▸ bot_le) hJZ hnJ with he|he
    · exact he.trans hω
    · have hZβu := center_le_of_central_neighbor H hB hSyl hβu.symm hcentral
      let _ := graph_Z_elementary H u
      exact False.elim (hne (commutator_eq_bot_iff_le_centralizer.mpr
        ((he ▸ hJβ).trans (hZβu.trans (le_centralizer (Z F u))))))
  have hMbot : M=⊥ := by
    have hMQ : M≤centralizer (Q F α:Set (G₀ L S)) := commutator_eq_bot_iff_le_centralizer.mp hJbot
    apply bot_unique
    intro m hm
    have hLC : c.actor≤centralizer ({m}:Set (G₀ L S)) := by
      rw [←hgen]
      exact sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hMC hm a ha))
        (fun q hq => mem_centralizer_singleton_iff.mpr (hMQ hm q hq))
    exact hω ▸ (mem_omegaCenterIn_iff _ _).mpr
      ⟨c.core_le (hRQ hm.2),fun a ha => mem_centralizer_singleton_iff.mp (hLC ha),
        elemPow_eq_one_of_isElementaryAbelian m hm.2.1⟩
  apply le_antisymm ?_ (by rw [←hNZa]; exact inf_le_inf_left _ hZD)
  intro x hx
  have hZRC : Z F α≤centralizer (R:Set (G₀ L S)) :=
    (le_centralizer_iff.mp (graph_Q_centralizes_Z H α)).trans (centralizer_le hRQ)
  have hxprod : x∈(Z F α:Set (G₀ L S))*(R:Set (G₀ L S)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ (hZRC.trans (Subgroup.centralizer_le_normalizer _)),←hdec]
    exact hx.2
  obtain ⟨z,hz,r,hr,rfl⟩ := hxprod
  have hrM : r∈M := by
    refine ⟨?_,hr⟩
    have hh := (N⊔Z F α).mul_mem ((N⊔Z F α).inv_mem (mem_sup_right hz)) (mem_sup_left hx.1)
    change r∈N⊔Z F α
    simpa only [inv_mul_cancel_left] using hh
  have hr1 : r=1 := mem_bot.mp (hMbot ▸ hrM)
  apply hNZa.le
  refine ⟨hx.1,?_⟩
  change z*r∈Z F α
  rw [hr1,mul_one]
  exact hz


/-- Original-source form of the D intersection, with the actual inclusion maps. -/
theorem original_bTwo_nonbinary_beta_proper_D_intersection
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι≤N)
    (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    N⊓((parabolic L S 1).pCoreIn 2⊓(Q F t).map ι)=(Z F β).map ι := by
  have hQmap : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hN0 : N≤G₀ L S := hNQ.le.trans (hQmap.ge.trans (map_subtype_le _))
  let N₀ := N.subgroupOf (G₀ L S)
  have hNm : N₀.map ι=N := map_subgroupOf_eq_of_le hN0
  have hNQ₀ : N₀≤Q F β := by
    apply (map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp
    rw [hNm,hQmap]
    exact hNQ.le
  have hn : stabilizer F β≤normalizer (N₀:Set (G₀ L S)) := by
    intro x hx
    have hxP : (x:G)∈P₀ L S 1 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hx
      exact hx
    exact le_normalizer_comap ι (hPN (P₀_le h 1 hxP))
  have hNZa : N₀⊓Z F α=Z F β := by
    apply map_injective (G₀ L S).subtype_injective
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hNm]
    exact original_bTwo_nonbinary_beta_proper_center_intersection h hc hne hb hβu ht htne K e hK hD N hNQ hZN hPN
  have hh := congrArg (map ι)
    (reduced_bTwo_strict_beta_section_D_intersection h hc hne hb hβu ht htne hD N₀ hNQ₀ hn hNZa)
  simpa only [D,map_inf _ _ _ (G₀ L S).subtype_injective,hQmap,hNm] using hh

/-- The equal-field intersection and escape step on p.165. Every proper
nonzero invariant beta section meets Q_alpha in order q_beta squared and
therefore escapes Q_alpha. No minimality hypothesis is needed. -/
theorem original_bTwo_nonbinary_beta_proper_core_intersection
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι<N)
    (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    Nat.card (K false)=Nat.card (K true) ∧
      N⊓(Z F α).map ι=(Z F β).map ι ∧
      N⊓((parabolic L S 1).pCoreIn 2⊓(Q F t).map ι)=(Z F β).map ι ∧
      Nat.card (N⊓(parabolic L S 0).pCoreIn 2 : Subgroup G)=Nat.card (K true)^2 ∧
      ¬N≤(parabolic L S 0).pCoreIn 2 := by
  obtain ⟨heq,hsection,_⟩ := original_bTwo_nonbinary_beta_proper_section_sharp h hc hne hb hβu ht htne K e hK hD N hNQ hZN hPN
  have hNZ := original_bTwo_nonbinary_beta_proper_center_intersection h hc hne hb hβu ht htne K e hK hD N hNQ hZN.le hPN
  have hND := original_bTwo_nonbinary_beta_proper_D_intersection h hc hne hb hβu ht htne K e hK hD N hNQ hZN.le hPN
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁⊓(Q F t).map ι
  let Z₁ := (Z F β).map ι
  let I := Q₀⊓Q₁
  let A := N⊓Q₀
  change N⊓D₀=Z₁ at hND
  obtain ⟨_,hDQ,_,_,hZb,hDc,_,hQb,_⟩ := original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  change D₀≤Q₀ at hDQ
  change Nat.card Z₁=Nat.card (K false) at hZb
  change Nat.card D₀=Nat.card (K false)^2*Nat.card (K true) at hDc
  change Nat.card Q₁=Nat.card (K false)^3*Nat.card (K true)^2 at hQb
  rw [heq] at hZb hDc hQb
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite I := Finite.of_injective (inclusion (show I≤Q₁ from inf_le_right)) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hNQ.le) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion (show A≤N from inf_le_left)) (inclusion_injective _)
  have hDI : D₀≤I := le_inf hDQ inf_le_left
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hidx : D₀.relIndex I=Nat.card (K true) :=
    (original_bTwo_linear_seed_and_indices h hb c ht htne (reduced_graph_core_obstruction h α β hab) (e true)).2.2
  have hIc : Nat.card I=Nat.card (K true)^4 := by
    have hh := relIndex_mul_card_of_le hDI
    rw [hidx,hDc] at hh
    calc Nat.card I = Nat.card (K true)*(Nat.card (K true)^2*Nat.card (K true)) := hh.symm
         _ = Nat.card (K true)^4 := by ring
  have hiQ : I.relIndex Q₁=Nat.card (K true) := by
    have hh := relIndex_mul_card_of_le (show I≤Q₁ from inf_le_right)
    rw [hIc,hQb] at hh
    apply Nat.eq_of_mul_eq_mul_right (Nat.pow_pos Nat.card_pos : 0<Nat.card (K true)^4)
    calc I.relIndex Q₁*Nat.card (K true)^4 = Nat.card (K true)^3*Nat.card (K true)^2 := hh
         _ = Nat.card (K true)*Nat.card (K true)^4 := by ring
  have hNc : Nat.card N=Nat.card (K true)^3 := by
    have hh := relIndex_mul_card_of_le hZN.le
    change Z₁.relIndex N*Nat.card Z₁=Nat.card N at hh
    change Z₁.relIndex N=Nat.card (K true)^2 at hsection
    rw [hsection,hZb] at hh
    calc Nat.card N = Nat.card (K true)^2*Nat.card (K true) := hh.symm
         _ = Nat.card (K true)^3 := by ring
  have hAD : A⊓D₀=Z₁ := by
    change (N⊓Q₀)⊓D₀=Z₁
    rw [inf_assoc,inf_eq_right.mpr hDQ,hND]
  have hAI : A≤I := le_inf inf_le_right (inf_le_left.trans hNQ.le)
  have hDA : D₀.relIndex A≤Nat.card (K true) :=
    (relIndex_le_of_le_right hAI (hidx ▸ Nat.ne_of_gt Nat.card_pos)).trans_eq hidx
  have hAc : Nat.card A≤Nat.card (K true)^2 := by
    have hh := relIndex_mul_card_of_le (show A⊓D₀≤A from inf_le_left)
    rw [inf_relIndex_left,hAD,hZb] at hh
    calc Nat.card A = D₀.relIndex A*Nat.card (K true) := hh.symm
         _ ≤ Nat.card (K true)*Nat.card (K true) := Nat.mul_le_mul_right _ hDA
         _ = Nat.card (K true)^2 := by ring
  have hAN : A.relIndex N≤Nat.card (K true) := by
    have he : N⊓I=A := by
      change N⊓(Q₀⊓Q₁)=N⊓Q₀
      rw [←inf_assoc,inf_eq_left.mpr (inf_le_left.trans hNQ.le)]
    rw [←he,inf_relIndex_left]
    exact (relIndex_le_of_le_right hNQ.le (hiQ ▸ Nat.ne_of_gt Nat.card_pos)).trans_eq hiQ
  have hAlower : Nat.card (K true)^2≤Nat.card A := by
    have hh := relIndex_mul_card_of_le (show A≤N from inf_le_left)
    rw [hNc] at hh
    have hmul : Nat.card (K true)*Nat.card (K true)^2≤Nat.card (K true)*Nat.card A := by
      calc Nat.card (K true)*Nat.card (K true)^2 = Nat.card (K true)^3 := by ring
           _ = A.relIndex N*Nat.card A := hh.symm
           _ ≤ Nat.card (K true)*Nat.card A := Nat.mul_le_mul_right _ hAN
    exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos
  have hAexact : Nat.card A=Nat.card (K true)^2 := le_antisymm hAc hAlower
  refine ⟨heq,hNZ,hND,hAexact,?_⟩
  intro hNα
  have hANeq : A=N := inf_eq_left.mpr hNα
  have he : Nat.card (K true)^3=Nat.card (K true)^2 := by rw [←hNc,←hANeq,hAexact]
  have hmul : Nat.card (K true)^2*Nat.card (K true)=Nat.card (K true)^2*1 := by
    calc Nat.card (K true)^2*Nat.card (K true) = Nat.card (K true)^3 := by ring
         _ = Nat.card (K true)^2*1 := by rw [he,mul_one]
  have hone := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos Nat.card_pos : 0<Nat.card (K true)^2) hmul
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
