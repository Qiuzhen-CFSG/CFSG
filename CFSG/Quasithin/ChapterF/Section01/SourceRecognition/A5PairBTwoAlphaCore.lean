module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoAlphaSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanVanishing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidualOrderPath
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Excluding a proper original alpha core supplement

The source Cartan acts irreducibly on its separated residual root. A proper
normal supplement to D therefore meets D in the natural alpha center.
The source natural central-extension calculation makes that supplement
abelian. Its order then forces a noncentral beta second-kernel section,
contradicting the proved beta chief interval.

Source: DGS, Groups and Graphs (1985), (5.17), (10.7)--(10.10),
pp.117,158--165; Aschbacher--Smith F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

omit [Finite G] in
private theorem no_large_abelian_alpha_supplement
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i))
    (hK : ∀ i, Nat.card (K i) = 4)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι)
    (W : Subgroup G) [IsMulCommutative W] (hcard : Nat.card W = 256)
    (hsup : W ⊔ ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) =
      (parabolic L S 0).pCoreIn 2) : False := by
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hlower := original_abelian_supplement_second_core_bound h hc hne hb hβu ht htne
    K e hD ((hK false).trans (hK true).symm) W (by rw [hcard,hK true]; norm_num) hsup
  let I := neighborCoreIntersection F β
  let I₀ := I.map ι
  have hQa : (Q F α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F β).map ι = (parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hIQa : I₀ ≤ (parabolic L S 0).pCoreIn 2 := by
    rw [←hQa]
    exact map_mono (neighborCoreIntersection_le F hab)
  have hIQb : I₀ ≤ (parabolic L S 1).pCoreIn 2 := by
    rw [←hQb]
    exact map_mono (source_neighborCoreIntersection_le_core H hab)
  have hnot : ¬ Q F β ≤ Q F α := by
    intro hh
    apply reduced_graph_core_obstruction h β α hab.symm
    rw [inf_eq_right.mpr hh]
    exact CommutingNontrivial.stabilizer_normalizes_Q F β
  have hIQlt : I₀ < (parabolic L S 1).pCoreIn 2 := lt_of_le_of_ne hIQb (by
    intro he
    apply hnot
    apply (map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp
    rw [hQa,hQb,←he]
    exact hIQa)
  have hZI : Z F β ≤ I := by
    apply le_iInf
    intro z
    exact graph_Z_le_Q_of_short H (reduced_kernel_sylow h) (by
      change (graph F).dist β z < b F
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr z.property,hb]
      decide)
  have hZI₀ : (Z F β).map ι ≤ I₀ := map_mono hZI
  have hZcard : Nat.card ((Z F β).map ι) = 4 := by
    obtain ⟨_,_,_,_,hh,_⟩ := original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
    exact hh.trans (hK false)
  have hIcard : 16 ≤ Nat.card I₀ := by
    rw [←reduced_neighborCoreIntersection_eq_second_core h hab,hK true] at hlower
    rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hlower
  have hZIlt : (Z F β).map ι < I₀ := lt_of_le_of_ne hZI₀ (by
    intro he
    rw [←he,hZcard] at hIcard
    omega)
  exact original_bTwo_nonbinary_beta_no_proper_section h hc hne hb hβu ht htne K e
    (by rw [hK true]; decide) hD I₀ hIQlt hZIlt (original_second_core_normalized h)

private theorem proper_alpha_supplement_intersection
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i))
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    (N : Subgroup G) (hNQ : N < (parabolic L S 0).pCoreIn 2)
    (hZN : (Z F α).map ι ≤ N)
    (hPN : parabolic L S 0 ≤ normalizer (N : Set G))
    (hgenN : N ⊔ ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) =
      (parabolic L S 0).pCoreIn 2) :
    N ⊓ ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι) = (Z F α).map ι := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hval : 3 ≤ Nat.card ((graph F).neighborSet u) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) u.type
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet u) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨C,hfix,hd,hgen,ho,_,_,g,hg,_,hgt,_,_,_,_,
      _,hfour,hdec,_,_,hn,_,_,_,_,hRne,hzero⟩ :=
    Assembly.BTwoSource.original_bTwo_path_cartan_residual_trivial
      h hc hne hb hβu ht htne hy hyne hns
  let R := bTwoResidual F β t u (g • u)
  change R = (D F β t ⊓ Q F u) ⊓ Q F (g • u) at hfour
  change D F β t = Z F α ⊔ R at hdec
  change R ≠ ⊥ at hRne
  change R ⊓ Q F y = ⊥ at hzero
  have hnR : C ≤ normalizer (R : Set (G₀ L S)) := fun _ hc => (hn hc).1.2
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K i)).symm
  let ey := source_linear_quotient_at H K eG y
  have hRc := Assembly.BTwoSource.path_cartan_residual_card h hy hfix hd hgen ho g
    hfour hRne (disjoint_iff.mpr hzero) hnR ey
  have hCE : C ≤ stabilizer F α ⊓ stabilizer F β :=
    le_inf (fun _ hx => (hfix hx).1.1.1.2) (fun _ hx => (hfix hx).1.1.2)
  have hCy : C ≤ stabilizer F y ⊓ stabilizer F u :=
    le_inf (fun _ hx => (hfix hx).2) (fun _ hx => (hfix hx).1.2)
  obtain ⟨hdy,hgy⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab hy.symm
    C hCE hCy ho hd hgen
  have hRu : R ≤ Q F u := by rw [hfour]; exact inf_le_left.trans inf_le_right
  have hRS : R ≤ (stabilizer F y ⊓ stabilizer F u).pCoreIn 2 :=
    hRu.trans (by rw [inf_comm]; exact graph_Q_le_edgeCore H hy)
  have hQa : (Q F α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hDm : (D F β t).map ι = (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  let N₀ := N.subgroupOf (G₀ L S)
  have hNm : N₀.map ι = N := map_subgroupOf_eq_of_le
    (hNQ.le.trans (hQa.ge.trans (map_subtype_le _)))
  have hZN₀ : Z F α ≤ N₀ := map_le_iff_le_comap.mp hZN
  have hnN₀ : stabilizer F α ≤ normalizer (N₀ : Set (G₀ L S)) := by
    intro x hx
    have hxP : (x : G) ∈ P₀ L S 0 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hx
      exact hx
    exact le_normalizer_comap ι (hPN (P₀_le h 0 hxP))
  have hNR : N₀ ⊓ R = ⊥ := by
    by_contra hneNR
    have hnNR : C ≤ normalizer ((N₀ ⊓ R : Subgroup (G₀ L S)) : Set (G₀ L S)) :=
      (le_inf ((hCE.trans inf_le_left).trans hnN₀) hnR).trans inf_normalizer_le_normalizer_inf
    have hNRs : N₀ ⊓ R ≤ (stabilizer F y ⊓ stabilizer F u).pCoreIn 2 :=
      inf_le_right.trans hRS
    have hNRc := (Assembly.BTwoSource.cartan_normalized_disjoint_two_subgroup_card
      H (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hy.symm ey C (N₀ ⊓ R)
      hCy hdy hgy hNRs ((isPGroup_pCoreIn 2 _).to_le hNRs) hnNR hneNR
      ((disjoint_iff.mpr hzero).mono inf_le_right le_rfl)).2
    have he : N₀ ⊓ R = R := eq_of_le_of_card_ge inf_le_right (by rw [hNRc,hRc])
    have hDN : D F β t ≤ N₀ := hdec ▸ sup_le hZN₀ (he ▸ inf_le_left)
    have hDN' := map_mono (f := ι) hDN
    rw [hDm,hNm] at hDN'
    have hNfull : N = (parabolic L S 0).pCoreIn 2 := by
      rw [sup_eq_left.mpr hDN'] at hgenN
      exact hgenN
    exact hNQ.ne hNfull
  have hDQ : D F β t ≤ Q F α := by
    obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
    have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hactor (reduced_bTwo_middle_central h hc hne hb hab hβu)
    obtain ⟨_,_,hDQ,_⟩ := c.central_D_structure H (reduced_kernel_sylow h) hb hω ht htne
    exact hDQ
  have hZR : Z F α ≤ centralizer (R : Set (G₀ L S)) :=
    (le_centralizer_iff.mp (graph_Q_centralizes_Z H α)).trans
      (centralizer_le (inf_le_left.trans hDQ))
  have hND : N₀ ⊓ D F β t = Z F α := by
    apply le_antisymm ?_ (le_inf hZN₀ (hdec ▸ le_sup_left))
    intro x hx
    have hxp : x ∈ (Z F α : Set (G₀ L S)) * (R : Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _
        (hZR.trans (Subgroup.centralizer_le_normalizer _)),←hdec]
      exact hx.2
    obtain ⟨z,hz,r,hr,rfl⟩ := hxp
    have hrN : r ∈ N₀ := by
      simpa only [inv_mul_cancel_left] using N₀.mul_mem (N₀.inv_mem (hZN₀ hz)) hx.1
    have hr1 : r = 1 := mem_bot.mp (hNR ▸ (show r ∈ N₀ ⊓ R from ⟨hrN,hr⟩))
    change z * r ∈ Z F α
    rw [hr1,mul_one]
    exact hz
  have hh := congrArg (map ι) hND
  rwa [map_inf _ _ _ (G₀ L S).subtype_injective,hNm,hDm] at hh

/-- In the actual noncommuting b = 2 A5/A5 source, the entire alpha
parabolic core is already the core of the original factor. -/
theorem HypothesisF11.a5_bTwo_alpha_parabolic_core_eq
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    twoCore (parabolic L S 0) = twoCore (L 0) := by
  let H := reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hval : 3 ≤ Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; omega) β
  have hns := h.a5_parabolic_not_solvable 0 (a 0).some
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,n,hn,hm,hpow,hext,hD,hrest⟩ :=
    Assembly.BTwoSource.original_core_layers h hc hne hb hβu ht htne hns
  clear hrest hext hpow hm hn n
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let K : Bool → Type := fun _ => GaloisField 2 2
  let e (i : Bool) : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i) :=
    by cases i
       · exact (a 0).some.trans e₄.symm
       · exact (a 1).some.trans e₄.symm
  have hK (i : Bool) : Nat.card (K i) = 4 := hfour
  obtain ⟨hZD,hDQ,_,hZcard,_,hDcard,hQcard,_⟩ :=
    original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι
  let Z₀ := (Z F α).map ι
  let N := L 0 ⊓ Q₀
  have hQa : (Q F α).map ι = Q₀ := reduced_base_Q_map h false
  have hDm : (D F β t).map ι = D₀ := by
    change (Q F β ⊓ Q F t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hQG : Q₀ ≤ G₀ L S := hQa.ge.trans (map_subtype_le _)
  have hnL : parabolic L S 0 ≤ normalizer (L 0 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show L 0 ≤ parabolic L S 0 from le_sup_left.trans le_sup_left)).mp
      (h.local_normal_in_parabolic 0)
  have hPN : parabolic L S 0 ≤ normalizer (N : Set G) := by
    change parabolic L S 0 ≤ normalizer ((L 0 ⊓ twoCore (parabolic L S 0) : Subgroup G) : Set G)
    rw [h.local_inf_parabolic_core 0]
    exact hnL.trans (normalizer_le_normalizer_characteristic_image (L 0) (pCore 2 (L 0)))
  have hnD : L 0 ≤ normalizer (D₀ : Set G) := by
    have hnD' := c.D_stabilizer_normalized H (reduced_kernel_sylow h) hb ht htne
    change stabilizer F α ≤ normalizer (D F β t : Set (G₀ L S)) at hnD'
    have hh := (map_mono (f := ι) hnD').trans ((D F β t).le_normalizer_map ι)
    have hPm : (stabilizer F α).map ι = P₀ L S 0 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
      exact map_subgroupOf_eq_of_le le_sup_left
    rw [hPm,hDm] at hh
    exact (show L 0 ≤ P₀ L S 0 from le_sup_right.trans le_sup_left).trans hh
  have hgenN : N ⊔ D₀ = Q₀ := by
    apply le_antisymm (sup_le inf_le_right hDQ)
    intro x hx
    have hxp : x ∈ (L 0 : Set G) * (D₀ : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hnD]
      exact h.a5_bTwo_alpha_core_le_local_sup_D a hc hne hb hβu ht htne hx
    obtain ⟨l,hl,d,hd,hld⟩ := hxp
    change l * d = x at hld
    have hlQ : l ∈ Q₀ := by
      have hldQ : l * d ∈ Q₀ := by rw [hld]; exact hx
      have hh := Q₀.mul_mem hldQ (Q₀.inv_mem (hDQ hd))
      simpa only [mul_inv_cancel_right] using hh
    rw [←hld]
    exact (N ⊔ D₀).mul_mem
      ((show N ≤ N ⊔ D₀ from le_sup_left) ⟨hl,hlQ⟩)
      ((show D₀ ≤ N ⊔ D₀ from le_sup_right) hd)
  have hQL : Q₀ ≤ L 0 := by
    by_contra hnot
    have hNQ : N < Q₀ := lt_of_le_of_ne inf_le_right (by
      intro he
      exact hnot (he ▸ (show N ≤ L 0 from inf_le_left)))
    have hZN : Z₀ ≤ N := le_inf
      (h.a5_bTwo_alpha_center_le_local (a 0).some hc hne hb hβu) (hZD.trans hDQ)
    have hND := proper_alpha_supplement_intersection h hc hne hb hβu ht htne K e hns
      N hNQ hZN hPN hgenN
    let N₀ := N.subgroupOf (G₀ L S)
    have hNm : N₀.map ι = N := map_subgroupOf_eq_of_le (hNQ.le.trans hQG)
    have hNQ₀ : N₀ ≤ Q F α := by
      apply (map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp
      rw [hNm,hQa]
      exact hNQ.le
    have hND₀ : N₀ ⊓ D F β t = Z F α := by
      apply (map_injective (G₀ L S).subtype_injective)
      rw [map_inf _ _ _ (G₀ L S).subtype_injective,hNm,hDm]
      exact hND
    have hgen₀ : N₀ ⊔ D F β t = Q F α := by
      apply (map_injective (G₀ L S).subtype_injective)
      rw [Subgroup.map_sup,hNm,hDm,hQa]
      exact hgenN
    have hnN₀ : c.actor ≤ normalizer (N₀ : Set (G₀ L S)) := by
      intro x hx
      have hxP : (x : G) ∈ P₀ L S 0 := by
        have hh := c.actor_le hx
        rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
        exact hh
      exact le_normalizer_comap ι (hPN (P₀_le h 0 hxP))
    let eβ := (reduced_graphLinearQuotient h true (e true)).trans
      (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K true)).symm
    let : IsMulCommutative N₀ := c.natural_supplement_commutative H
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor
      (reduced_bTwo_middle_central h hc hne hb hab hβu) ht htne
      (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2.le
      (reduced_graph_core_obstruction h α β hab) eβ (LinearEquiv.refl _ _) hk
      N₀ hNQ₀ hND₀ hgen₀ hnN₀
    let : IsMulCommutative N := hNm ▸ inferInstanceAs (IsMulCommutative (N₀.map ι))
    have hcardN : Nat.card N = 256 := by
      have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes N D₀
        (hDQ.trans ((pCoreIn_le 2 _).trans hPN))
      rw [hND,hgenN,hZcard,hDcard,hQcard] at hp
      simp only [hK] at hp
      omega
    exact no_large_abelian_alpha_supplement h hc hne hb hβu ht htne K e hK hD N hcardN hgenN
  rw [←h.local_inf_parabolic_core 0]
  exact (inf_eq_right.mpr hQL).symm

end CFSG.Quasithin.ChapterF.Source
