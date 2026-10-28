module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.DGSProfiles
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.DGSProfiles
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoChapter10Consumer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceBound

/-!
# The exact original mixed A₅/S₃ size bound

Reduce the original Sylow to the full Borel two-core. This preserves F.1.1
and both embedded parabolic kernels, and makes the full quintic quotient A₅.
The commuting critical branch has Borel-core order 64. In the noncommuting
branch the source field-power relation selects the cubic starting vertex and
quintic middle vertex. Reorient and translate that edge to the source base.
DGS (10.10) would give an irreducible binary section of order 64 under this
full A₅ quotient, which the checked highest-weight calculation excludes.
Thus D_alpha = Z_alpha, and the original (10.7) core orders give Borel-core
order 128. Restoring the original Borel gives Sylow order 64, 128 or 256.

The internal imports deliberately continue the existing mixed-profile and
pair-reorientation proofs. Their private arithmetic and transport lemmas are
reused only in proof bodies; no private name occurs in the public statements.
No irreducibility restriction from S₅ to A₅ is asserted. The second reduction
is performed before applying the original full-beta irreducibility theorem.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
reduction pp.95--96, (10.7)--(10.10), pp.158--165, (11.7), pp.174--175,
and (15.1), p.226; Aschbacher--Smith F.1.12(I), printed pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open DGS85.Reduction NoncommutingProfile NoncommutingProfile.Reduction
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => reducedFamily ![U,K] S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ ![U,K] S)

omit [Finite G] in
private theorem commonBorel_swap : commonBorel ![U,K] S = commonBorel ![K,U] S := by
  change borel U S ⊔ borel K S ⊔ S = borel K S ⊔ borel U S ⊔ S
  rw [sup_comm (borel U S)]

private abbrev fields (i : Bool) : Type := if i then GaloisField 2 2 else ZMod 2
private instance fields_field (i : Bool) : Field (fields i) := by cases i <;> dsimp [fields] <;> infer_instance
private instance fields_finite (i : Bool) : Finite (fields i) := by cases i <;> dsimp [fields] <;> infer_instance
private instance fields_char (i : Bool) : CharP (fields i) 2 := by cases i <;> dsimp [fields] <;> infer_instance

private def field_markings
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (i : Bool) :
    (family ![U,K] i ⧸ pCore 2 (family ![U,K] i)) ≃* PSL(2,fields i) := by
  cases i
  · exact (eU.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
  · exact eK.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (by norm_num [fields, GaloisField.card 2 2 (by decide)])).some.symm

/-- The strict distance-two branch is impossible when the whole Borel
normalizes the original Sylow of the mixed pair. -/
theorem mixed_strict_base_false
    (h : HypothesisF11 ![U,K] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (hn : commonBorel ![U,K] S ≤ normalizer (S : Set G))
    {u t : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hD : (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι) : False := by
  obtain ⟨hN,hel,ρ,d,hd,hirr,hcard⟩ := original_bTwo_10_10_mixed_beta_irreducible
    h hc hne hb hβu ht htne fields (field_markings eK eU)
    (by exact Nat.card_zmod 2) (by exact GaloisField.card 2 2 (by decide)) hD
  let _ := hN
  let _ := hel
  let _ := hirr
  have hnb : commonBorel ![K,U] S ≤ normalizer (S : Set G) := by
    rwa [←commonBorel_swap]
  obtain ⟨eβ⟩ := h.swap.mixed_first_quotient_of_borel_normalizes eK eU hnb
  change (parabolic ![U,K] S 1 ⧸ pCore 2 (parabolic ![U,K] S 1)) ≃*
    alternatingGroup (Fin 5) at eβ
  let e := eβ.trans Representation.SL2FourNatural.alternatingFiveEquiv.symm
  let σ : Representation (ZMod 2) Representation.SL2FourNatural.SL
      (Additive (((parabolic ![U,K] S 1).pCoreIn 2) ⧸
        ((Z F β).map ι).subgroupOf ((parabolic ![U,K] S 1).pCoreIn 2))) :=
    ρ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hirr
  apply MixedDGS.irreducible_card_ne_sixtyfour σ
    (by simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field)
  exact hcard

/-- The source intersection is the center in the normalized mixed pair;
no exceptional profile is assumed. -/
theorem mixed_base_intersection_eq_center
    (h : HypothesisF11 ![U,K] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (hn : commonBorel ![U,K] S ≤ normalizer (S : Set G))
    {u t : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F t).map ι = (Z F α).map ι := by
  by_contra hD
  exact mixed_strict_base_false h eK eU hn hc hne hb hβu ht htne hD

/-- Exact Borel-core order for the normalized cubic/quintic critical base edge. -/
theorem mixed_base_borel_core_card
    (h : HypothesisF11 ![U,K] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (hn : commonBorel ![U,K] S ≤ normalizer (S : Set G))
    {u t : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    Nat.card (twoCore (commonBorel ![U,K] S)) = 128 := by
  have hD := mixed_base_intersection_eq_center h eK eU hn hc hne hb hβu ht htne
  obtain ⟨k,f,fin,ch,alg,c,hactor,hZD,hDQ,hDel,hZ,hQa,hQb,_,_,_,_,_,_,_,_⟩ :=
    original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne (field_markings eK eU true)
  have hfields := MixedDGS.source_action_field_card h hactor c.quotient c.onto c.kernel
    (Assembly.linear_graph_quotient h false (field_markings eK eU false) α rfl).some
  have hk : Nat.card k = 2 := by simpa only [fields, Bool.false_eq_true, ↓reduceIte, Nat.card_zmod] using hfields
  have hQ : Nat.card ((parabolic ![U,K] S 1).pCoreIn 2) = 32 := by
    rw [hD,hZ,hk] at hQb
    norm_num [fields, GaloisField.card 2 2 (by decide)] at hQb
    exact hQb
  have hcore := h.swap.mixed_borel_core_card eK eU
  change Nat.card (pCore 2 (commonBorel ![K,U] S)) =
    4 * Nat.card (pCore 2 (parabolic ![U,K] S 1)) at hcore
  have hmap : Nat.card ((parabolic ![U,K] S 1).pCoreIn 2) =
      Nat.card (pCore 2 (parabolic ![U,K] S 1)) :=
    card_map_of_injective (parabolic ![U,K] S 1).subtype_injective
  rw [hmap] at hQ
  rw [commonBorel_swap, show Nat.card (twoCore (commonBorel ![K,U] S)) =
      Nat.card (pCore 2 (commonBorel ![K,U] S)) from
      card_map_of_injective (commonBorel ![K,U] S).subtype_injective, hcore,hQ]

end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open Reduction CommutingNontrivial
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}

omit [Finite G] in
/-- Move the actual cubic critical start and its quintic middle to the
reversed base edge, retaining critical escape and noncommutation. -/
theorem mixed_reversed_noncommuting_base
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a a' : Vertex (reducedFamily ![K,U] S)}
    (hc : IsCriticalPair (reducedFamily ![K,U] S) a a')
    (hne : ⁅Z (reducedFamily ![K,U] S) a,Z (reducedFamily ![K,U] S) a'⁆ ≠ ⊥)
    (hb : b (reducedFamily ![K,U] S) = 2) :
    ∃ u : Vertex (reducedFamily ![U,K] S),
      IsCriticalPair (reducedFamily ![U,K] S) (base (reducedFamily ![U,K] S) false) u ∧
      ⁅Z (reducedFamily ![U,K] S) (base (reducedFamily ![U,K] S) false),
        Z (reducedFamily ![U,K] S) u⁆ ≠ ⊥ ∧
      (graph (reducedFamily ![U,K] S)).Adj (base (reducedFamily ![U,K] S) true) u := by
  let F := reducedFamily ![K,U] S
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : ∀ i, Finite (swapFamily F i) := fun i => inferInstanceAs (Finite (F (!i)))
  have hdist : (graph F).dist a a' = 2 := hc.1.trans hb
  obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (by rw [hdist]; decide)
  have hlen : p.length = 2 := hp.trans hdist
  let m := p.getVert 1
  have ham : (graph F).Adj a m := by
    simpa [m] using p.adj_getVert_succ (i := 0) (by omega)
  have hlast : p.getVert 2 = a' := by simpa [hlen] using p.getVert_length
  have hma' : (graph F).Adj m a' := by
    simpa [m,hlast] using p.adj_getVert_succ (i := 1) (by omega)
  obtain ⟨ha,hm⟩ := MixedDGS.noncommuting_two_cubic_orientation h eK eU hc hne hb ham hma'
  have hcs : IsCriticalPair (swapFamily F) (swapVertex F a) (swapVertex F a') := by
    constructor
    · simpa only [DGS85.swap_dist,DGS85.b_swapFamily] using hc.1
    · simpa only [DGS85.swap_Z,DGS85.swap_U] using hc.2
  have hns : ⁅Z (swapFamily F) (swapVertex F a),Z (swapFamily F) (swapVertex F a')⁆ ≠ ⊥ := by
    simpa only [DGS85.swap_Z] using hne
  have has : (graph (swapFamily F)).Adj (swapVertex F a) (swapVertex F m) :=
    (swapGraphIso F).map_adj_iff.mpr ham
  have hms : (graph (swapFamily F)).Adj (swapVertex F m) (swapVertex F a') :=
    (swapGraphIso F).map_adj_iff.mpr hma'
  obtain ⟨g,hga,hgm⟩ := incident_common_translate (swapFamily F) has.2
  rw [swapVertex_type,ha,Bool.not_true] at hga
  rw [swapVertex_type,hm,Bool.not_false] at hgm
  have hct := criticalPair_translate (swapFamily F) hcs g⁻¹
  have hnt : ⁅Z (swapFamily F) (g⁻¹ • swapVertex F a),
      Z (swapFamily F) (g⁻¹ • swapVertex F a')⁆ ≠ ⊥ := by
    rw [commuting_centers_translate]
    exact fun he => hns ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp he)
  have hmt := (Subgroup.CosetGeometry.translationGraphIso (swapFamily F) g⁻¹).map_adj_iff.mpr hms
  change (graph (swapFamily F)).Adj (g⁻¹ • swapVertex F m) (g⁻¹ • swapVertex F a') at hmt
  rw [←hga,inv_smul_smul] at hct hnt
  rw [←hgm,inv_smul_smul] at hmt
  unfold reducedFamily
  rw [pair_G₀_swap K U S]
  have hF : family (fun i => (P₀ ![U,K] S i).subgroupOf (G₀ ![K,U] S)) = swapFamily F := by
    funext i
    cases i
    · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![K,U] S)) (pair_P₀_swap K U S 0)
    · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![K,U] S)) (pair_P₀_swap K U S 1)
  rw [hF]
  exact ⟨g⁻¹ • swapVertex F a',hct,hnt,hmt⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute

namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open Reduction CommutingNontrivial
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}

/-- The complete original mixed pair has Borel core of order 64 or 128.
The strict branch is excluded on the Borel-core reduction, whose full
quintic endpoint quotient is A5. -/
theorem mixed_borel_core_card_cases
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 64 ∨
      Nat.card (twoCore (commonBorel ![K,U] S)) = 128 := by
  let R := twoCore (commonBorel ![K,U] S)
  have hR := h.restrict_to_borel_core
  have hnorm : commonBorel ![K,U] R ≤ normalizer (R : Set G) :=
    (SuzukiContainment.reduced_commonBorel_le h).trans
      ((commonBorel ![K,U] S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hcore : twoCore (commonBorel ![K,U] R) = R := SuzukiContainment.reduced_borel_core h
  obtain ⟨a,a',hc⟩ := source_exists_criticalPair (reduced_triple hR)
  by_cases hcomm : ⁅Z (reducedFamily ![K,U] R) a,Z (reducedFamily ![K,U] R) a'⁆ = ⊥
  · left
    have hh := (MixedDGS.commuting_size hR eK eU hc hcomm).1
    rwa [hcore] at hh
  · have hb := reduced_intrinsic_noncommuting_bound hR hc hcomm
    rcases hb with hb | hb
    · exact (MixedDGS.noncommuting_distance_one_false hR eK eU hc hcomm hb).elim
    · right
      obtain ⟨u,hcu,hnu,hβu⟩ := mixed_reversed_noncommuting_base hR eK eU hc hcomm hb
      let F := reducedFamily ![U,K] R
      have hval : 3 ≤ Nat.card ((graph F).neighborSet (base F false)) := by
        rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
        exact source_valence_ge_three (reduced_triple hR.swap) (reduced_vertex_sylow hR.swap) false
      obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
        (s := (graph F).neighborSet (base F false))
        (by rw [←Nat.card_coe_set_eq]; omega) (base F true)
      have hb' : b F = 2 := (pair_b_swap K U R).trans hb
      have hn' : commonBorel ![U,K] R ≤ normalizer (R : Set G) := by
        rwa [commonBorel_swap]
      have hh := mixed_base_borel_core_card hR.swap eK eU hn' hcu hnu hb' hβu ht htne
      rw [commonBorel_swap,hcore] at hh
      exact hh

/-- Restore the original full Borel: the original Sylow has order 64,
128 or 256, including its possible outer factor of order two. -/
theorem mixed_original_sylow_card_cases
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card S = 64 ∨ Nat.card S = 128 ∨ Nat.card S = 256 := by
  have hc := mixed_borel_core_card_cases h eK eU
  have hm : Nat.card (twoCore (commonBorel ![K,U] S)) =
      Nat.card (pCore 2 (commonBorel ![K,U] S)) :=
    card_map_of_injective (commonBorel ![K,U] S).subtype_injective
  rw [hm] at hc
  have hs := h.mixed_sylow_card_borel_core_cases eK eU
  omega

/-- The exact Chapter 10 mixed-size bound from the literal F.1.1 pair. -/
theorem mixed_original_sylow_card_le
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) : Nat.card S ≤ 256 := by
  have hh := mixed_original_sylow_card_cases h eK eU
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
