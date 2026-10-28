module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicPairSplitting

/-!
# The alpha catalogue in the elementary beta branch

The odd-actor splitting descends through the literal adjacent-core kernel
Q_alpha intersect Q_beta. Because Q_alpha Q_beta is the whole edge Sylow,
this further quotient is an actual alpha Sylow. Its opposite-seed image is
a nontrivial elementary direct factor. In the exceptional order-144 quotient,
every normal elementary Sylow subgroup lies in Frattini; a direct factor
there would be trivial. Seed escape gives the contradiction.

Thus both local rank-one catalogues follow from the elementary beta branch.
The original-completion application transports the elementary quotient and
alpha marking through the same inclusion and retains the full Borel core.
FullElementaryMarkedProfile applies these markings to the source numerical,
path and U4 profile conclusions. The nonelementary branch and the primitive
Chapter 14 apartment inputs remain separate obligations.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h), pp.170--171, and (11.7), pp.174--175; the exceptional Sylow
calculation is Theory.SpecificGroups.GL2.ThreeSylowNormalElementary.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "G₀" => Reduction.G₀ L S
/-- Descend the odd-actor splitting to the exact adjacent-core quotient.
Its multiplication marking retains the opposite seed and the fixed factor. -/
theorem reduced_pair_further_split_images_of_core_product {K : Type*} [Group K]
    (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (hprod : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b)
    (Mb : IsRankOneModel (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)))
    (π : Q F b →* K) (hπ : Function.Surjective π)
    (hker : π.ker = (Q F a ⊓ Q F b).subgroupOf (Q F b))
    (y : G₀) (hy : y ∈ Z F a ⊔ Z F c)
    (hsplit : Q F b =
      pairSpan (Z F a) (Z F c) (Q F b) ⊔
        (Q F b ⊓ centralizer (zpowers y : Set G₀)))
    (hint : pairSpan (Z F a) (Z F c) (Q F b) ⊓
      centralizer (zpowers y : Set G₀) = Z F a ⊓ Z F c) :
    let E' := Z F c ⊓ Q F b
    let A := (E'.subgroupOf (Q F b)).map π
    let C := ((Q F b ⊓ centralizer (zpowers y : Set G₀)).subgroupOf (Q F b)).map π
    IsElementaryAbelian 2 A ∧ Disjoint A C ∧
      ∃ e : A × C ≃* K, ∀ x z, e (x,z) = (x : K) * (z : K) := by
  let ht := reduced_triple h
  let hB := reduced_borel_core_sylow h
  let d := reducedFullEarlierLocalTheorems h
  let Q₀ := Q F b
  let E := Z F a ⊓ Q₀
  let E' := Z F c ⊓ Q₀
  let V := pairSpan (Z F a) (Z F c) Q₀
  let D := Q F a ⊓ Q F c
  let I := Q F a ⊓ Q₀
  let C₀ := Q₀ ⊓ centralizer (zpowers y : Set G₀)
  let A₀ := E'.subgroupOf Q₀
  let B₀ := (E ⊔ C₀).subgroupOf Q₀
  have hEQ : E ≤ Q F a := inf_le_left.trans ((source_Z_Q_U ht a).1.trans (map_subtype_le _))
  have hab := source_critical_one_adjacent hc hb
  have hDQ : D ≤ Q₀ := source_rankOne_pair_core_le_beta ht hB d hab hbc hac Mb
  have hDC : D ≤ C₀ := le_inf hDQ
    ((le_centralizer_iff.mp (source_pair_core_normalizers ht hab hbc).1).trans
      (centralizer_le (zpowers_le.mpr hy)))
  have hI : I = E ⊔ D := source_pair_adjacent_core_intersection ht hB d hc hb hbc hac Mb
  have hkerB : π.ker ≤ B₀ := by
    intro x hx
    rw [hker] at hx
    exact (hI.le.trans (sup_le le_sup_left (hDC.trans le_sup_right))) hx
  have hn : C₀ ≤ normalizer (E : Set G₀) := inf_le_left.trans
    ((le_inf (source_adjacent_core_normalizes_center ht hab) Q₀.le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  have hAB : A₀ ⊓ B₀ ≤ π.ker := by
    intro x hx
    have hxprod : x.val ∈ (E : Set G₀) * (C₀ : Set G₀) := by
      rw [←coe_mul_of_right_le_normalizer_left E C₀ hn]
      exact hx.2
    obtain ⟨e,he,z,hz,hxz⟩ := hxprod
    have hzV : z ∈ V := by
      have hh := V.mul_mem (V.inv_mem (mem_sup_left he)) (mem_sup_right hx.1)
      change e⁻¹*x.val ∈ V at hh
      rw [←hxz] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hzJ := hint.le ⟨hzV,hz.2⟩
    have hxQa : x.val ∈ Q F a := by
      rw [←hxz]
      exact (Q F a).mul_mem (hEQ he) (((source_Z_Q_U ht a).1.trans (map_subtype_le _)) hzJ.1)
    rw [hker]
    exact ⟨hxQa,x.property⟩
  have hd : Disjoint (A₀.map π) (B₀.map π) := by
    apply disjoint_def.mpr
    rintro x ⟨v,hv,rfl⟩ ⟨z,hz,he⟩
    have hvz : v*z⁻¹ ∈ π.ker := by
      change π (v*z⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hvB : v ∈ B₀ := by
      have hh := B₀.mul_mem (hkerB hvz) hz
      simpa only [inv_mul_cancel_right] using hh
    exact hAB ⟨hv,hvB⟩
  have hEmap : (E.subgroupOf Q₀).map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hker]
    exact comap_mono (le_inf hEQ inf_le_right)
  have hBmap : B₀.map π = (C₀.subgroupOf Q₀).map π := by
    dsimp only [B₀]
    rw [subgroupOf_sup (show E ≤ Q₀ from inf_le_right) (show C₀ ≤ Q₀ from inf_le_left),
      Subgroup.map_sup,hEmap,bot_sup_eq]
  rw [hBmap] at hd
  have hcomm : A₀.map π ≤ centralizer ((C₀.subgroupOf Q₀).map π : Set K) := by
    rintro x ⟨v,hv,rfl⟩ z ⟨w,hw,rfl⟩
    have hcD : ⁅(w:G₀),(v:G₀)⁆ ∈ D :=
      ((reduced_source_pair_core_action_of_core_product h hc hb hbc hac hprod).trans
      (inf_le_inf ((source_Z_Q_U ht a).1.trans (map_subtype_le _))
        ((source_Z_Q_U ht c).1.trans (map_subtype_le _))))
        (commutator_mem_commutator w.property (mem_sup_right hv))
    have hcπ : π ⁅w,v⁆ = 1 := by
      change ⁅w,v⁆ ∈ π.ker
      rw [hker]
      exact ⟨hcD.1,(⁅w,v⁆ : Q₀).property⟩
    have hc' : ⁅π w,π v⁆ = 1 := by
      rw [←map_commutatorElement]
      exact hcπ
    exact commutatorElement_eq_one_iff_mul_comm.mp hc'
  have hjoin : E' ⊔ (E ⊔ C₀) = Q₀ := by
    rw [←sup_assoc,sup_comm E' E]
    exact hsplit.symm
  have hgen : A₀.map π ⊔ (C₀.subgroupOf Q₀).map π = ⊤ := by
    rw [←hBmap,←Subgroup.map_sup,←subgroupOf_sup (show E' ≤ Q₀ from inf_le_right)
      (show E ⊔ C₀ ≤ Q₀ from sup_le inf_le_right inf_le_left),hjoin,
      subgroupOf_self,map_top_of_surjective π hπ]
  let := source_center_elementary ht c
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf inf_le_right
  let : IsElementaryAbelian 2 (A₀.map π) := IsElementaryAbelian.map π
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcomm
  refine ⟨inferInstance,hd,e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv),?_⟩
  exact he



private theorem no_elementary_direct_factor_of_normal_nine
    {D : Type*} [Group D] [Finite D] (hD : Nat.card D = 144)
    (N : Subgroup D) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hc : pCore 2 D = ⊥)
    (T : Sylow 2 D) (A C : Subgroup T) [IsElementaryAbelian 2 A]
    (e : A × C ≃* T) (he : ∀ x z, e (x,z) = (x : T) * (z : T)) : A = ⊥ := by
  have hgen : A ⊔ C = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨⟨a,c⟩,rfl⟩ := e.surjective x
    rw [he]
    exact mul_mem (mem_sup_left a.property) (mem_sup_right c.property)
  have hcent : C ≤ centralizer (A : Set T) := by
    intro c hc a ha
    have hp : ((⟨a,ha⟩ : A), (1:C)) * (1,⟨c,hc⟩) = (1,⟨c,hc⟩) * ((⟨a,ha⟩ : A),(1:C)) := by
      simp only [Prod.mk_mul_mk,mul_one,one_mul]
    have hh := congrArg e hp
    rw [e.map_mul,e.map_mul,he,he] at hh
    simpa only [Subgroup.coe_one,mul_one,one_mul] using hh
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hgen]
    exact sup_le A.le_normalizer (hcent.trans (Subgroup.centralizer_le_normalizer _))))
  have hphi := Theory.GroupTheory.normal_elementary_le_frattini_of_normal_nine hD N hN hc T A
  have hC : C = ⊤ := frattini_nongenerating (top_unique (by
    rw [←hgen]
    exact sup_le (hphi.trans le_sup_right) le_sup_left))
  apply (eq_bot_iff_forall _).mpr
  intro a ha
  have h1 : e (⟨a,ha⟩,1) = e (1,⟨a,hC.symm ▸ mem_top a⟩) := by
    rw [he,he]
    simp only [Subgroup.coe_one,mul_one,one_mul]
  exact congrArg (fun x : A × C => (x.1 : T)) (e.injective h1)

/-- The elementary beta branch excludes the alpha enlargement of order 144.
Both local catalogues are derived from the original hypotheses. -/
theorem reduced_elementary_alpha_model (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (helem : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    IsRankOneModel (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) := by
  have hs := reduced_graph_rankOne_or_normal_nine h a
  dsimp only [reducedFamily] at hs
  rcases hs with hm | ⟨hcard,N,hN,hE,h9⟩
  · exact hm
  · let ht := reduced_triple h
    let hB := reduced_borel_core_sylow h
    let d := reducedFullEarlierLocalTheorems h
    let := finite_endpoints ht
    let := hN
    let := hE
    have hab := source_critical_one_adjacent hc hb
    have Mb := reduced_actor_model_of_elementary_edge h hab.symm (by
      rw [inf_comm (stabilizer F b) (stabilizer F a)]
      exact helem)
    have hprod := (reduced_elementary_center_and_core_products h hc hb helem).2
    let M := graphLocalGroup F a
    let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
    let q := QuotientGroup.mk' (pCore 2 M)
    obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht hB d hab
    change Sylow 2 M at T
    change (T : Subgroup M).map M.subtype = (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 at hT
    have hQT : Q F b ≤ (T : Subgroup M).map M.subtype := by
      rw [hT,hprod]
      exact le_sup_right
    have hQM : Q F b ≤ M := hQT.trans (map_subtype_le _)
    let Q₀ := (Q F b).subgroupOf M
    have hcore : (pCore 2 M).map M.subtype = Q F a := localGroup_core_eq F d a
    have hTC : (T : Subgroup M) = pCore 2 M ⊔ Q₀ := by
      apply (map_injective (f := M.subtype) M.subtype_injective)
      rw [hT,Subgroup.map_sup,hcore,map_subgroupOf_eq_of_le hQM]
      exact hprod
    let U := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
    have hU : (U : Subgroup (M ⧸ pCore 2 M)) = Q₀.map q := by
      change (T : Subgroup M).map q = _
      rw [hTC,Subgroup.map_sup]
      have hz : (pCore 2 M).map q = ⊥ := by
        rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
      rw [hz,bot_sup_eq]
    let j : Q F b →* M := inclusion hQM
    let f : Q F b →* U := (q.comp j).codRestrict U (fun x => by
      change q (j x) ∈ (U : Subgroup (M ⧸ pCore 2 M))
      rw [hU]
      exact mem_map_of_mem q x.property)
    have hf : Function.Surjective f := by
      rintro ⟨x,hx⟩
      rw [hU] at hx
      obtain ⟨z,hz,rfl⟩ := hx
      exact ⟨⟨z.val,hz⟩,rfl⟩
    have hk : f.ker = (Q F a ⊓ Q F b).subgroupOf (Q F b) := by
      ext x
      change f x = 1 ↔ x.val ∈ Q F a ∧ x.val ∈ Q F b
      have hxq : f x = 1 ↔ q (j x) = 1 := Subtype.ext_iff
      rw [hxq]
      constructor
      · intro hx
        exact ⟨hcore ▸ mem_map_of_mem M.subtype ((QuotientGroup.eq_one_iff (j x)).mp hx),x.property⟩
      · rintro ⟨hx,_⟩
        rw [←hcore] at hx
        obtain ⟨z,hz,he⟩ := hx
        apply (QuotientGroup.eq_one_iff (j x)).mpr
        exact (Subtype.ext he : z = j x) ▸ hz
    obtain ⟨y,hy,_,_,hgen,hint⟩ := reduced_elementary_pair_coprime_splitting h hc hb hbc hac helem
    obtain ⟨hA,hd,e,he⟩ := reduced_pair_further_split_images_of_core_product
      h hc hb hbc hac hprod Mb f hf hk y hy hgen hint
    let A := ((Z F c ⊓ Q F b).subgroupOf (Q F b)).map f
    let C := ((Q F b ⊓ centralizer (zpowers y : Set G₀)).subgroupOf (Q F b)).map f
    let := hA
    have hAz : A = ⊥ := no_elementary_direct_factor_of_normal_nine
      hcard N h9 (pCore_quotient_pCore_eq_bot 2) U A C e he
    have hesc : ¬ Z F c ⊓ Q F b ≤ Q F a :=
      source_seed_not_le_opposite_core ht hbc.symm hab.symm (by
        intro hp
        apply reduced_center_pair_not_isPGroup h hc hb hbc hac
        rwa [sup_comm])
    apply (hesc ?_).elim
    intro x hx
    have hker := (Subgroup.map_eq_bot_iff _).mp hAz
    rw [hk] at hker
    exact (hker (show (⟨x,hx.2⟩ : Q F b) ∈ (Z F c ⊓ Q F b).subgroupOf (Q F b) from hx)).1


/-- Both actual local quotient catalogues follow from the elementary beta
branch; neither is supplied as a premise. -/
theorem reduced_elementary_local_models (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (helem : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    IsRankOneModel (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ∧
      IsRankOneModel (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  have hv := card_neighbors_of_indices F
    (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl) b
  have hcard : 1 < ((graph F).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hv]
    have hh : 3 ≤ ((F (!b.type)).subgroupOf (F b.type)).index :=
      source_valence_ge_three ht (reduced_vertex_sylow h) b.type
    omega
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard hcard a
  exact ⟨reduced_elementary_alpha_model h hc hb hbc hca.symm helem,
    reduced_actor_model_of_elementary_edge h (source_critical_one_adjacent hc hb).symm (by
      rw [inf_comm (stabilizer F b) (stabilizer F a)]
      exact helem)⟩

private theorem elementary_of_original_quotient_intrinsic
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

/-- Alpha's actual original-inclusion quotient is in the rank-one catalogue
from the full-Borel elementary beta branch, with no solvability assumption. -/
theorem original_borel_elementary_alpha_model (h : HypothesisF11 L S)
    (hc : IsCriticalPair F (base F false) (base F true)) (hb : DGS85.b F = 1)
    (helem : ∃ hN : (((Q F (base F true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q F (base F true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L S)))) :
    IsRankOneModel ((graphLocalGroup F (base F false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F (base F false)).map (G₀).subtype)) := by
  let R := (stabilizer F (base F false) ⊓ stabilizer F (base F true)).pCoreIn 2
  let N := Q F (base F true)
  have htr := reduced_triple h
  have hBG : B₀ L S ≤ G₀ :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L S) ≤ G₀ :=
    (show twoCore (commonBorel L S) ≤ B₀ L S from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L S) := by
    dsimp only [R]
    rw [show stabilizer F (base F false) = F false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F false ⊓ F true = (B₀ L S).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  have hab := source_critical_one_adjacent hc hb
  have hNR : N ≤ R := by
    have hh := Noncommuting.graph_Q_le_edgeCore htr hab.symm
    rwa [inf_comm (stabilizer F (base F true))] at hh
  let hN : (N.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ _))
  have he : IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) :=
    elementary_of_original_quotient_intrinsic R N hNR (by rwa [hmap])
  have hm := (reduced_elementary_local_models h hc hb ⟨hN,he⟩).1
  let e := (graphLocalGroup F (base F false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  exact hm.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
