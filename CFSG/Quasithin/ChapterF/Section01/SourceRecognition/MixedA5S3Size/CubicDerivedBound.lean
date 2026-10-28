module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceCommutingOne
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceNoncommutingParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalReorientation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoUnequalBetaModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFrattini
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned

/-!
# The derived subgroup of the original cubic parabolic core

In the mixed A₅/S₃ pair the commuting branch gives a cubic core whose
derived subgroup has order at most two. In the noncommuting branch the
critical alpha is cubic. The exceptional seed equality puts its Frattini
subgroup in its natural center of order four. The strict alternative gives
an irreducible binary A₅ section of order 64, excluded by the actual
prime-field highest-weight parameters.

For the last exclusion first replace the source Sylow by the full Borel
two-core. Both literal embedded parabolic cores are unchanged, and the
quintic parabolic quotient is A₅. Thus the bound concerns the full original
cubic core; no recognized amalgam, reduced catalogue, or profile input is
assumed.

Source: DGS, Groups and Graphs (1985), (10.9)--(10.10), pp.163--165,
(11.7), pp.174--175, and the original reduction pp.95--96.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

private theorem irreducible_card_ne_sixtyfour
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2,k) W) [ρ.IsIrreducible]
    (hk : Nat.card k = 4) : Nat.card W ≠ 64 := by
  intro hW
  have hd : Module.finrank (ZMod 2) W = 6 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod,hW] at hh
    exact (Nat.pow_right_injective (by decide : 1 < 2)) (by simpa using hh.symm)
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! ht
    let b := Module.finBasis (ZMod 2) W
    let j : Fin (Module.finrank (ZMod 2) W) := ⟨0,by omega⟩
    let A : Subrepresentation ρ := {
      toSubmodule := Submodule.span (ZMod 2) {b j}
      apply_mem_toSubmodule := by intro g v hv; simpa only [ht,Module.End.one_apply] using hv }
    have hA : A ≠ ⊥ := by
      intro he
      have hv : b j ∈ A := Submodule.subset_span (Set.mem_singleton (b j))
      rw [he] at hv
      exact b.ne_zero j hv
    have he := congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top A).resolve_left hA)
    have hdA : Module.finrank (ZMod 2) A.toSubmodule = 1 := finrank_span_singleton (b.ne_zero j)
    change A.toSubmodule = ⊤ at he
    rw [he,finrank_top,hd] at hdA
    omega
  obtain ⟨hs,n,hn,hsdiv,_,hdeg⟩ :=
    Representation.SL2.Unsigned.exists_primeField_highestWeight_parameters
      2 ρ hnt 2 (by simpa using hk)
  have hnlt : n.val < 4 := by simpa [hk] using n.isLt
  have hsone := (Nat.dvd_prime Nat.prime_two).mp hsdiv
  simp only [Fin.prod_univ_two] at hdeg
  rcases hsone with hsone | hsone <;> rw [hsone,hd] at hdeg <;>
    interval_cases h : n.val <;> norm_num [h] at hdeg

variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => DGS85.Reduction.reducedFamily ![K,U] S

private theorem commuting_cubic_derived_bound
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v w : Vertex F} (hc : IsCriticalPair F v w)
    (hb : b F = 1) (hcomm : ⁅Z F v,Z F w⁆ = ⊥) :
    Nat.card (⁅(parabolic ![K,U] S 1).pCoreIn 2,
      (parabolic ![K,U] S 1).pCoreIn 2⁆ : Subgroup G) ≤ 2 := by
  obtain ⟨hc₀,hm₀⟩ := commuting_one_base_critical h eK eU hc hb hcomm
  have hder := (CommutingOneProfile.mixed_binary_graph_core_structure K U S h eK eU
    hc₀ hb hm₀).2.2.2.2.1
  have hz := CommutingOneProfile.mixed_binary_graph_beta_center_card_two K U S h eK eU
    hc₀ hb hm₀
  have hmap := map_mono (f := (DGS85.Reduction.G₀ ![K,U] S).subtype) hder
  rw [map_commutator,NoncommutingProfile.reduced_base_Q_map h true] at hmap
  exact (card_le_of_le hmap).trans_eq
    ((card_map_of_injective (DGS85.Reduction.G₀ ![K,U] S).subtype_injective).trans hz)

private theorem noncommuting_cubic_based_bound
    (h : HypothesisF11 ![U,K] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (eP : (parabolic ![U,K] S 1 ⧸ pCore 2 (parabolic ![U,K] S 1)) ≃*
      alternatingGroup (Fin 5))
    {w : Vertex (DGS85.Reduction.reducedFamily ![U,K] S)}
    (hc : IsCriticalPair (DGS85.Reduction.reducedFamily ![U,K] S)
      (base (DGS85.Reduction.reducedFamily ![U,K] S) false) w)
    (hne : ⁅Z (DGS85.Reduction.reducedFamily ![U,K] S)
      (base (DGS85.Reduction.reducedFamily ![U,K] S) false),
      Z (DGS85.Reduction.reducedFamily ![U,K] S) w⁆ ≠ ⊥)
    (hb : b (DGS85.Reduction.reducedFamily ![U,K] S) = 2)
    (hmw : (graph (DGS85.Reduction.reducedFamily ![U,K] S)).Adj
      (base (DGS85.Reduction.reducedFamily ![U,K] S) true) w) :
    Nat.card (⁅(parabolic ![U,K] S 0).pCoreIn 2,
      (parabolic ![U,K] S 0).pCoreIn 2⁆ : Subgroup G) ≤ 4 := by
  let F₀ := DGS85.Reduction.reducedFamily ![U,K] S
  let α := base F₀ false
  let β := base F₀ true
  let ι := Subgroup.subtype (DGS85.Reduction.G₀ ![U,K] S)
  let H := DGS85.Reduction.reduced_triple h
  have hab : (graph F₀).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hval : 3 ≤ Nat.card ((graph F₀).neighborSet α) := by
    rw [card_neighbors_of_indices F₀ (fun i => ((F₀ (!i)).subgroupOf (F₀ i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three H (DGS85.Reduction.reduced_vertex_sylow h) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F₀).neighborSet α) (by rw [←Nat.card_coe_set_eq]; omega) β
  let fields : Bool → Type := fun i => if i then GaloisField 2 2 else ZMod 2
  let : ∀ i, Field (fields i) := fun i => by cases i <;> dsimp [fields] <;> infer_instance
  let : ∀ i, Finite (fields i) := fun i => by cases i <;> dsimp [fields] <;> infer_instance
  let : ∀ i, CharP (fields i) 2 := fun i => by cases i <;> dsimp [fields] <;> infer_instance
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let marks (i : Bool) : (family ![U,K] i ⧸ pCore 2 (family ![U,K] i)) ≃* PSL(2,fields i) := by
    cases i
    · exact (eU.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
        (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
    · exact eK.trans e₄.symm
  have hcentral := DGS85.Reduction.reduced_bTwo_middle_central h hc hne hb hab hmw
  have hcomm := (DGS85.Reduction.reduced_bTwo_center_identities h hc hne hb hab hmw).2.2.2
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    DGS85.Reduction.reduced_bTwo_center_action_exists h hc hne hb hab hmw
  let := f
  let := fin
  let := ch
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let eα := (DGS85.Reduction.reduced_graphLinearQuotient h false (marks false)).trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2)).symm
  let eβ := (DGS85.Reduction.reduced_graphLinearQuotient h true (marks true)).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm
  have hk : Nat.card k = 2 := by
    simpa only [Nat.card_zmod] using source_action_field_card h hactor c.quotient c.onto c.kernel eα
  by_cases hD : D F₀ β t = Z F₀ α
  · have hphi := c.exceptional_linear_frattini H (DGS85.Reduction.reduced_borel_core_sylow h)
      (DGS85.Reduction.reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le
      (DGS85.Reduction.reduced_graph_core_obstruction h α β hab) eβ hD (LinearEquiv.refl _ _)
    change (frattini (Q F₀ α)).map (Q F₀ α).subtype = Z F₀ α at hphi
    let : Fact (IsPGroup 2 (Q F₀ α)) := ⟨isPGroup_pCoreIn 2 (stabilizer F₀ α)⟩
    have hder : ⁅Q F₀ α,Q F₀ α⁆ ≤ Z F₀ α := by
      rw [←hphi]
      have hh := map_mono (f := (Q F₀ α).subtype)
        (commutator_le_frattini_of_isPGroup (p := 2) (R := Q F₀ α))
      simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
    have hz : Nat.card (Z F₀ α) = 4 := by
      have hh := c.central_center_card (LinearEquiv.refl _ _)
        (c.omega_eq_bot_of_central_neighbor H (DGS85.Reduction.reduced_borel_core_sylow h)
          (DGS85.Reduction.reduced_vertex_sylow h) hactor hcentral)
      change Nat.card (Z F₀ α) = Nat.card k ^ 2 at hh
      rw [hh,hk]
      norm_num
    have hm := map_mono (f := ι) hder
    rw [map_commutator,NoncommutingProfile.reduced_base_Q_map h false] at hm
    exact (card_le_of_le hm).trans_eq
      ((card_map_of_injective (DGS85.Reduction.G₀ ![U,K] S).subtype_injective).trans hz)
  · have hD₀ : (parabolic ![U,K] S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι ≠ (Z F₀ α).map ι := by
      intro he
      apply hD
      apply map_injective (DGS85.Reduction.G₀ ![U,K] S).subtype_injective
      change (Q F₀ β ⊓ Q F₀ t).map ι = _
      rwa [map_inf _ _ _ (DGS85.Reduction.G₀ ![U,K] S).subtype_injective,
        NoncommutingProfile.reduced_base_Q_map h true]
    obtain ⟨hN,hel,ρ,d,_,hirr,hcard⟩ :=
      NoncommutingProfile.Reduction.original_bTwo_unequal_beta_irreducible
        h hc hne hb hmw ht htne fields marks (by change 2 < Nat.card (GaloisField 2 2); omega)
        hD₀ (by change Nat.card (ZMod 2) ≠ Nat.card (GaloisField 2 2); rw [Nat.card_zmod]; omega)
    let _ := hN
    let _ := hel
    let e := eP.trans (e₄.symm.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm)
    let σ : Representation (ZMod 2) SL(2,GaloisField 2 2) _ :=
      ρ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible σ :=
      (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hirr
    have hc64 : Nat.card (Additive ((parabolic ![U,K] S 1).pCoreIn 2 ⧸
        ((Z F₀ β).map ι).subgroupOf ((parabolic ![U,K] S 1).pCoreIn 2))) = 64 := by
      change Nat.card ((parabolic ![U,K] S 1).pCoreIn 2 ⧸
          ((Z F₀ β).map ι).subgroupOf ((parabolic ![U,K] S 1).pCoreIn 2)) =
        Nat.card (fields false)^2 * Nat.card (fields true)^2 at hcard
      rw [Nat.card_congr Additive.toMul]
      simpa only [fields,Bool.false_eq_true,if_false,if_true,Nat.card_zmod,hfour,
        Nat.reducePow,Nat.reduceMul] using hcard
    exact (irreducible_card_ne_sixtyfour σ hfour hc64).elim

private theorem cubic_bound_of_exact_quintic_quotient
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (eP : (parabolic ![K,U] S 0 ⧸ pCore 2 (parabolic ![K,U] S 0)) ≃*
      alternatingGroup (Fin 5)) :
    Nat.card (⁅(parabolic ![K,U] S 1).pCoreIn 2,
      (parabolic ![K,U] S 1).pCoreIn 2⁆ : Subgroup G) ≤ 4 := by
  let H := DGS85.Reduction.reduced_triple h
  have hpair : ∃ v w : Vertex F, IsCriticalPair F v w := source_exists_criticalPair H
  obtain ⟨v,w,hc⟩ := hpair
  have hpos : 0 < b F := source_b_positive H
  have hwv : w ≠ v := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨m,hvm,hd⟩ := exists_predecessor F H.generate w v hwv
  rw [SimpleGraph.dist_comm (u := w) (v := m),
    SimpleGraph.dist_comm (u := w) (v := v),hc.1] at hd
  by_cases hcomm : ⁅Z F v,Z F w⁆ = ⊥
  · have hb := commuting_distance_one h eK eU hc hvm hd hcomm
    exact (commuting_cubic_derived_bound h eK eU hc hb hcomm).trans (by decide)
  rcases DGS85.Reduction.reduced_intrinsic_noncommuting_bound h hc hcomm with hb | hb
  · exact (noncommuting_distance_one_false h eK eU hc hcomm hb).elim
  change b F = 2 at hb
  have hmw : (graph F).Adj m w := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  obtain ⟨hv,hm⟩ := noncommuting_two_cubic_orientation h eK eU hc hcomm hb hvm hmw
  obtain ⟨g,hgv,hgm⟩ := incident_common_translate F hvm.2
  rw [hv] at hgv
  rw [hm] at hgm
  have hv₀ : g⁻¹ • v = base F true := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hgv.symm
  have hm₀ : g⁻¹ • m = base F false := by
    simpa only [inv_smul_smul] using congrArg (fun z : Vertex F => g⁻¹ • z) hgm.symm
  have hc₀ := CommutingNontrivial.criticalPair_translate F hc g⁻¹
  rw [hv₀] at hc₀
  have hn₀ : ⁅Z F (base F true),Z F (g⁻¹ • w)⁆ ≠ ⊥ := by
    intro he
    have hh := CommutingNontrivial.commuting_centers_translate F v w g⁻¹
    rw [hv₀,he] at hh
    exact hcomm ((Subgroup.map_eq_bot_iff_of_injective _
      (MulAut.conj g⁻¹).injective).mp hh.symm)
  have hm₁ : (graph F).Adj (base F false) (g⁻¹ • w) := by
    apply SimpleGraph.dist_eq_one_iff_adj.mp
    rw [←hm₀,Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hmw
  obtain ⟨w',hc',hn',hm'⟩ :=
    DGS85.Reduction.CriticalReorientation.original_noncommuting_critical_swap K U S hc₀ hn₀ hm₁
  have hb' : b (DGS85.Reduction.reducedFamily ![U,K] S) = 2 :=
    (DGS85.Reduction.pair_b_swap K U S).trans hb
  exact noncommuting_cubic_based_bound h.swap eK eU eP hc' hn' hb' hm'

/-- The full original cubic parabolic core has derived subgroup of order
at most four, using only the genuine F.1.1 hypotheses and the two quotient markings. -/
theorem mixed_cubic_parabolic_core_derived_card_le_four
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card (⁅(parabolic ![K,U] S 1).pCoreIn 2,
      (parabolic ![K,U] S 1).pCoreIn 2⁆ : Subgroup G) ≤ 4 := by
  have hh := cubic_bound_of_exact_quintic_quotient h.restrict_to_borel_core eK eU
    (h.mixed_reduced_first_quotient eK eU).some
  have he := h.borel_core_parabolic_same_core 1
  change (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 1).pCoreIn 2 =
    (parabolic ![K,U] S 1).pCoreIn 2 at he
  rwa [he] at hh

end CFSG.Quasithin.ChapterF.Source.MixedDGS
