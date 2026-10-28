module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphCatalogue
public import Theory.SpecificGroups.GL2.ThreeSylowNormalElementary

/-!
# The elementary edge quotient removes the exceptional local catalogue row

The edge two-core modulo the endpoint core is an actual Sylow subgroup of
its local actor quotient. If the quotient were the exceptional enlargement
of order 144, its normal elementary nine-group would force every normal
elementary Sylow subgroup into Frattini. An elementary Sylow has trivial
Frattini subgroup and order sixteen, giving a contradiction.

Thus the elementary branch constructs its beta catalogue from the original
F.1.1 hypotheses. The actual source consumer gives S = Z_alpha Q_beta =
Q_alpha Q_beta with neither endpoint catalogue assumed. The final theorem
transports the result to the full original Borel quotient. The unrestricted
alpha catalogue and nonelementary order-144 case remain separate.
Source: DGS, Groups and Graphs (1985), (6.1), pp.118--119,
(11.2)(b), (11.4), (11.7), pp.168,171,174; the exceptional Sylow obstruction
is proved in Theory.SpecificGroups.GL2.ThreeSylowNormalElementary.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

/-- The actual elementary edge quotient excludes the order-144 enlargement. -/
theorem reduced_actor_model_of_elementary_edge (h : HypothesisF11 L S)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (helem : ∃ hN : ((Q F a).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F a).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    IsRankOneModel (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) := by
  rcases reduced_graph_rankOne_or_normal_nine h a with hm | ⟨hcard,N,hN,hE,h9⟩
  · exact hm
  · let ht := reduced_triple h
    let : ∀ i, Finite (F i) := finite_endpoints ht
    let M := graphLocalGroup F a
    let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _))
      (inclusion_injective _)
    dsimp only [reducedFamily] at helem
    obtain ⟨hQN,helem⟩ := helem
    let := hQN
    let := helem
    obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow ht (reduced_borel_core_sylow h)
      (reducedFullEarlierLocalTheorems h) hab
    change Sylow 2 (M ⧸ pCore 2 M) at T
    let : IsElementaryAbelian 2 T := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
    let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
    let := hN
    let := hE
    let : IsElementaryAbelian 2 (⊤ : Subgroup T) := IsElementaryAbelian.of_injective
      (⊤ : Subgroup T).subtype (⊤ : Subgroup T).subtype_injective
    have htop := normal_elementary_le_frattini_of_normal_nine hcard N h9
      (pCore_quotient_pCore_eq_bot (G := M) 2) T (⊤ : Subgroup T)
    have hbot : frattini T = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := 2)
    have htriv : (⊤ : Subgroup T) = ⊥ := bot_unique (hbot ▸ htop)
    have : Subsingleton T := ⟨fun x y => by
      have hx : x = 1 := mem_bot.mp (htriv ▸ mem_top x)
      have hy : y = 1 := mem_bot.mp (htriv ▸ mem_top y)
      exact hx.trans hy.symm⟩
    let : Unique T := uniqueOfSubsingleton 1
    have hcT : Nat.card T = 16 := by
      rw [T.card_eq_multiplicity,hcard]
      decide +kernel
    have hc1 : Nat.card T = 1 := Nat.card_unique
    omega

/-- Source (11.4) in the elementary beta branch, with both catalogue premises discharged. -/
theorem reduced_elementary_center_and_core_products (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (helem : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Z F a ⊔ Q F b ∧
      (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b := by
  have Mb := reduced_actor_model_of_elementary_edge h (source_critical_one_adjacent hc hb).symm
    (by
      rw [inf_comm (stabilizer F b) (stabilizer F a)]
      exact helem)
  let d := reducedFullEarlierLocalTheorems h
  exact ⟨source_elementary_beta_center_supplement (reduced_triple h)
      (reduced_borel_core_sylow h) d hc hb Mb helem,
    source_elementary_beta_core_product (reduced_triple h)
      (reduced_borel_core_sylow h) d hc hb Mb helem⟩

private theorem elementary_of_original_quotient
    (R N : Subgroup G₀) (hNR : N ≤ R) [(N.subgroupOf R).Normal]
    (helem : ∃ hn : ((N.map (G₀).subtype).subgroupOf (R.map (G₀).subtype)).Normal,
      letI := hn
      IsElementaryAbelian 2 (R.map (G₀).subtype ⧸
        (N.map (G₀).subtype).subgroupOf (R.map (G₀).subtype))) :
    IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) := by
  obtain ⟨hn,helem⟩ := helem
  let := hn
  let := helem
  let e := R.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  have hmap : (N.subgroupOf R).map e.toMonoidHom =
      (N.map (G₀).subtype).subgroupOf (R.map (G₀).subtype) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem (G₀).subtype hy
    · intro hx
      obtain ⟨y,hy,heq⟩ := hx
      exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext heq⟩
  let eq := QuotientGroup.congr _ _ e hmap
  exact IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective

/-- The literal full-Borel quotient supplies the original beta actor marking. -/
theorem original_borel_elementary_beta_model (h : HypothesisF11 L S)
    (helem : ∃ hN : (((Q F (base F true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q F (base F true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L S)))) :
    IsRankOneModel ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) := by
  let R := (stabilizer F (base F true) ⊓ stabilizer F (base F false)).pCoreIn 2
  let N := Q F (base F true)
  have htr := reduced_triple h
  have hBG : B₀ L S ≤ G₀ :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L S) ≤ G₀ :=
    (show twoCore (commonBorel L S) ≤ B₀ L S from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L S) := by
    dsimp only [R]
    rw [inf_comm (stabilizer F (base F true)),
      show stabilizer F (base F false) = F false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F false ⊓ F true = (B₀ L S).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  have hab : (graph F).Adj (base F true) (base F false) :=
    ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩
  have hNR : N ≤ R := Noncommuting.graph_Q_le_edgeCore htr hab
  let hN : (N.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ _))
  have he : IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) :=
    elementary_of_original_quotient R N hNR (by rwa [hmap])
  have hm := reduced_actor_model_of_elementary_edge h hab ⟨hN,he⟩
  let e := (graphLocalGroup F (base F true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  exact hm.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
