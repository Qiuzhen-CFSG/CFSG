module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryAlphaCentralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import Theory.SpecificGroups.SL2.HalfRootSubgroups
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryTerminalSeparation

/-!
# Terminal separation outside the beta field of order four

In the binary-alpha branch of DGS (10.8), a nonidentity element of the
tested terminal intersection gives two centralizing root images of size
at least q_beta/2. The full incident-edge Sylows have distinct images in
the literal beta quotient: equality would make the same edge core fix two
different neighbors. The generated image is proper, since surjectivity
would give transitivity of the centralizer on the actual beta neighbors.
The rank-one half-root theorem therefore forces q_beta ≤ 4.

The original-source application keeps the same opposite-center conjugator,
residual, and reduced-to-original core inclusions. Combining the bound
with the proved binary separation and the exceptional residual identity
establishes terminal separation for binary alpha whenever q_beta ≠ 4.
The field-four contradiction, nonbinary-alpha separation, and unrestricted
residual equality remain separate steps.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed pp.160--162, especially the middle paragraph on p.161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem half_roots_field_bound
    (h : HypothesisF11 L S) {v a b : Vertex F}
    (ha : (graph F).Adj v a) (hb : (graph F).Adj v b) (hab : a≠b)
    (e : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,K))
    (A B : Subgroup (G₀ L S)) (hA : A≤Q F a) (hB : B≤Q F b)
    (hAc : Nat.card K≤2*(Q F v).relIndex A)
    (hBc : Nat.card K≤2*(Q F v).relIndex B)
    (hnt : ¬∀ z : Vertex F, (graph F).Adj v z →
      ∃ g∈graphLocalGroup F v, g∈A⊔B ∧ g • a=z) : Nat.card K≤4 := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q : M →* SL(2,K) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=(Q F v).subgroupOf M := by
    have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
    rw [hc]
    ext x
    change e (QuotientGroup.mk' (pCore 2 M) x)=1 ↔ x∈pCore 2 M
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨R,hR⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) d ha
  obtain ⟨T,hT⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) d hb
  change Sylow 2 M at R T
  change (R:Subgroup M).map M.subtype=_ at hR
  change (T:Subgroup M).map M.subtype=_ at hT
  have hAR : A≤(R:Subgroup M).map M.subtype := by
    rw [hR]
    exact hA.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H ha.symm)
  have hBT : B≤(T:Subgroup M).map M.subtype := by
    rw [hT]
    exact hB.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H hb.symm)
  have hAM : A≤M := hAR.trans (map_subtype_le _)
  have hBM : B≤M := hBT.trans (map_subtype_le _)
  have hAi : A.subgroupOf M≤R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hBi : B.subgroupOf M≤T := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hBT hx
    exact (Subtype.ext he : y=x) ▸ hy
  let R' := R.mapSurjective (f:=q) hq
  let T' := T.mapSurjective (f:=q) hq
  have hne : R'≠T' := by
    intro he
    have hh := congrArg (fun U : Sylow 2 SL(2,K) => (U:Subgroup SL(2,K)).comap q) he
    change ((R:Subgroup M).map q).comap q=((T:Subgroup M).map q).comap q at hh
    have hkR : q.ker≤(R:Subgroup M) := by
      rw [hk]
      have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
      rw [hc]
      exact pCore_isPGroup.le_sylow_of_normal R
    have hkT : q.ker≤(T:Subgroup M) := by
      rw [hk]
      have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
      rw [hc]
      exact pCore_isPGroup.le_sylow_of_normal T
    rw [comap_map_eq_self hkR,comap_map_eq_self hkT] at hh
    have hec := congrArg (map M.subtype) hh
    rw [hR,hT] at hec
    exact hab (graph_intrinsic_edgeCore_unique_neighbor H (reduced_borel_core_sylow h)
      ha hb (hec ▸ (pCoreIn_le 2 _).trans inf_le_right))
  let A' := (A.subgroupOf M).map q
  let B' := (B.subgroupOf M).map q
  have hca : Nat.card A'=(Q F v).relIndex A :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) A q hk hAM
  have hcb : Nat.card B'=(Q F v).relIndex B :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) B q hk hBM
  have hproper : A'⊔B'≠⊤ := by
    intro he
    have hmap : ((A⊔B).subgroupOf M).map q=⊤ := by
      rw [subgroupOf_sup hAM hBM,Subgroup.map_sup]
      exact he
    have hcover : (A⊔B).subgroupOf M⊔q.ker=⊤ := by
      have hh := congrArg (comap q) hmap
      simpa only [comap_map_eq,comap_top] using hh
    have hfull : (A⊔B)⊔Q F v=M := by
      have hh := congrArg (map M.subtype) hcover
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (sup_le hAM hBM),hk,
        map_subgroupOf_eq_of_le (show Q F v≤M from pGroup_le_sylowGenerated _ _
          (Q_le_stabilizer F v) (isPGroup_pCoreIn 2 _)),←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    apply hnt
    intro z hz
    obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) v ⟨a,ha⟩ ⟨z,hz⟩
    change g • a=z at hgz
    have hn : A⊔B≤normalizer (Q F v:Set (G₀ L S)) :=
      (sup_le hAM hBM).trans ((sylowGenerated_le _).trans
        (CommutingNontrivial.stabilizer_normalizes_Q F v))
    have hp : g∈((A⊔B:Subgroup (G₀ L S)):Set (G₀ L S))*(Q F v:Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right (A⊔B) (Q F v) hn,hfull]
      exact hg
    obtain ⟨j,hj,r,hr,rfl⟩ := hp
    have hrfix : r • a=a := ((source_Z_Q_U H v).2.trans
      ((ballKernel_one_le_edge F ha).trans inf_le_right)) hr
    exact ⟨j,(sup_le hAM hBM) hj,hj,by simpa only [mul_smul,hrfix] using hgz⟩
  exact Matrix.SpecialLinearGroup.half_roots_field_card_le_four R' T' hne A' B' (A'⊔B')
    (map_mono hAi) (map_mono hBi) le_sup_left le_sup_right
    (by rwa [hca]) (by rwa [hcb]) hproper

/-- In the strict binary-alpha case, a nontrivial terminal intersection
forces the beta field to have at most four elements. The residual, opposite
lift, and both original core maps are retained. -/
theorem original_bTwo_alpha_binary_terminal_field_bound
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t≠base F true)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F (base F false)).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F (base F false), g • base F true=t ∧
      let ι := (G₀ L S).subtype
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧ R₀≠⊥ ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠base F true →
        R₀⊓(Q F y).map ι≠⊥ → Nat.card K≤4 := by
  obtain ⟨g,hg,hgt,hW,hfour,hRne,hroots⟩ :=
    original_bTwo_alpha_binary_terminal_half_roots h hc hne hb hβu ht htne e₀ hK₀ e hD
  refine ⟨g,hg,hgt,hW,hfour,hRne,?_⟩
  intro y hy hyne hJ
  obtain ⟨x,hx,hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hJ
  obtain ⟨hA,hB,_,hnt⟩ := hroots y hy hyne x hx hx1
  let ι := (G₀ L S).subtype
  let α := base F false
  let β := base F true
  let C := (centralizer ({x}:Set G)).comap ι
  let A := (V F t 1⊓Q F α)⊓C
  let B := (V F y 1⊓Q F u)⊓C
  have hmap (T : Subgroup (G₀ L S)) :
      (T⊓C).map ι=T.map ι⊓centralizer ({x}:Set G) := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨mem_map_of_mem ι ha.1,ha.2⟩
    · rintro ⟨⟨a,ha,rfl⟩,hcx⟩
      exact mem_map.mpr ⟨a,⟨ha,hcx⟩,rfl⟩
  have hAm : A.map ι=((V F t 1).map ι⊓(parabolic L S 0).pCoreIn 2)⊓
      centralizer ({x}:Set G) := by
    rw [show A=(V F t 1⊓Q F α)⊓C from rfl,hmap,
      map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h false]
    rfl
  have hBm : B.map ι=((V F y 1).map ι⊓(Q F u).map ι)⊓
      centralizer ({x}:Set G) := by
    rw [show B=(V F y 1⊓Q F u)⊓C from rfl,hmap,
      map_inf _ _ _ (G₀ L S).subtype_injective]
  have hAc : Nat.card K≤2*(Q F β).relIndex A := by
    rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) A (G₀ L S).subtype_injective,
      reduced_base_Q_map h true,hAm]
    exact hA
  have hBc : Nat.card K≤2*(Q F β).relIndex B := by
    rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) B (G₀ L S).subtype_injective,
      reduced_base_Q_map h true,hBm]
    exact hB
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).symm
  have hab : (graph F).Adj β α :=
    (show (graph F).Adj α β from
      ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩).symm
  have hau : α≠u := by
    intro he
    have hd := hc.1
    rw [←he,SimpleGraph.dist_self,hb] at hd
    contradiction
  apply half_roots_field_bound h hab hβu hau eβ A B
    (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right) hAc hBc
  intro hh
  apply hnt
  intro z hz
  obtain ⟨a,ha,haAB,haz⟩ := hh z hz
  refine ⟨a,ha,?_,haz⟩
  have hm := mem_map_of_mem ι haAB
  rwa [Subgroup.map_sup,hAm,hBm] at hm

/-- Binary-alpha terminal separation is reduced to the single beta field
of order four. This includes the exceptional D_alpha = Z_alpha case. -/
theorem original_bTwo_alpha_binary_terminal_separation_unless_four
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t≠base F true)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K≠4) :
    ∃ g∈graphLocalGroup F (base F false), g • base F true=t ∧
      let ι := (G₀ L S).subtype
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      ∀ y : Vertex F, (graph F).Adj u y → y≠base F true →
        R₀⊓(Q F y).map ι=⊥ := by
  classical
  by_cases htwo : Nat.card K=2
  · obtain ⟨g,hg,hgt,_,hs⟩ := original_bTwo_binary_terminal_separation
      h hc hne hb hβu ht htne e htwo
    exact ⟨g,hg,hgt,hs⟩
  by_cases hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype=
      (Z F (base F false)).map (G₀ L S).subtype
  · have hab : (graph F).Adj (base F false) (base F true) :=
      ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
      reduced_bTwo_center_action_exists h hc hne hb hab hβu
    change BTwoCenterActionData F (base F false) (base F true) u k (Fin 2 → k) at c
    change c.actor=graphLocalGroup F (base F false) at hactor
    have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
    subst alg
    let : Algebra (ZMod 2) k := ZMod.algebra k 2
    have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
    obtain ⟨g,hgt,_,_,_,_,_,hiff⟩ := original_bTwo_residual_structure h hb c hactor
      hcentral (LinearEquiv.refl _ _) ht htne
    have hR := hiff.mp hD
    refine ⟨g,hactor ▸ g.property,hgt,?_⟩
    dsimp only
    intro y hy hyne
    rw [hR,bot_inf_eq]
  · obtain ⟨g,hg,hgt,_,_,_,hbound⟩ := original_bTwo_alpha_binary_terminal_field_bound
      h hc hne hb hβu ht htne e₀ hK₀ e hD
    refine ⟨g,hg,hgt,?_⟩
    dsimp only
    intro y hy hyne
    by_contra hJ
    have hh := hbound y hy hyne hJ
    let : Fintype K := Fintype.ofFinite K
    obtain ⟨n,_,hn⟩ := FiniteField.card K 2
    have hn' : Nat.card K=2^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
    have hdeg : (n:ℕ)≤2 := by
      rw [hn'] at hh
      exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hh
    have hn12 : (n:ℕ)=1 ∨ (n:ℕ)=2 := by have := n.pos; omega
    rcases hn12 with hn1|hn2
    · exact htwo (by simpa only [hn1,pow_one] using hn')
    · exact hK (by simpa only [hn2,Nat.reducePow] using hn')

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
