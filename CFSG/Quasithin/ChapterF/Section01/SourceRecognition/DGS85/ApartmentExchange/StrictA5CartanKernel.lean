module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanDistinctSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairBTwoAlphaCore

/-!
# The full strict A5 Cartan has a nontrivial local permutation kernel

The actual chosen Cartan contains two disjoint commuting local tori of order
three. Thus its order is divisible by nine. At every vertex of the strict
source apartment it acts on five neighbors. A faithful action would embed
this Cartan in Sym(5), whose order is not divisible by nine. The intersection
with the whole local permutation kernel U is consequently nontrivial.

Source: DGS, Groups and Graphs (1985), (10.7)--(10.10), pp.158--165,
and (14.5), (14.9), pp.213--216. The original pair and full Cartan are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S

private theorem nine_dvd_local_kernel_nontrivial
    {Y : Type*} [Group Y] (Γ : Bool → Subgroup Y)
    [∀ i, Finite (Γ i)] (C : Subgroup Y) (v : Vertex Γ)
    (hCv : C ≤ stabilizer Γ v) (hC : 9 ∣ Nat.card C)
    (hv : Nat.card ((graph Γ).neighborSet v) = 5) :
    C ⊓ U Γ v ≠ ⊥ := by
  intro hzero
  let f := (localAction Γ v).comp (inclusion hCv)
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (by
    apply bot_unique
    intro x hx
    have hxU : (x : Y) ∈ U Γ v := by
      have hh : inclusion hCv x ∈ (localAction Γ v).ker := hx
      rw [localAction_ker] at hh
      exact hh
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hzero ▸ (show (x : Y) ∈ C ⊓ U Γ v from ⟨x.property,hxU⟩)))
  let : Finite ((graph Γ).neighborSet v) := finite_neighbors Γ v
  have hd := hC.trans (card_dvd_of_injective f hf)
  rw [Nat.card_perm,hv] at hd
  norm_num at hd

/-- Nine divides the order of the actual chosen full Cartan downstairs.
Both cubic tori and their disjointness come from the original A5 source. -/
theorem a5_bTwo_chosen_cartan_nine_dvd
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u) :
    9 ∣ Nat.card ((cartan (chosenCartans h)).map (bOne_tree_map h)) := by
  let H := reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints H
  let c := chosenCartans h
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ = E := by
    rw [show originalMiddle A = T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hCE : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hWE : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hnW : E ≤ normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hWE hnW
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg : C ⊔ E.pCoreIn 2 = E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E = stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false) = F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hab : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let e (i : Bool) : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,GaloisField 2 2) := by
    cases i
    · exact (a 0).some.trans e₄.symm
    · exact (a 1).some.trans e₄.symm
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (GaloisField 2 2)).symm
  obtain ⟨⟨eα⟩,_⟩ := CommutingTrivial.edge_complement_local_torus H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab (eG false) C
    (hEbase ▸ hCE) (hEbase ▸ hd) (hEbase ▸ hg)
  obtain ⟨⟨eβ⟩,_⟩ := CommutingTrivial.edge_complement_local_torus H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab.symm (eG true) C
    (by rw [inf_comm]; exact hEbase ▸ hCE)
    (by rw [inf_comm]; exact hEbase ▸ hd)
    (by
      change C ⊔ (stabilizer F (base F true) ⊓ stabilizer F (base F false)).pCoreIn 2 =
        stabilizer F (base F true) ⊓ stabilizer F (base F false)
      rw [inf_comm (stabilizer F (base F true)) (stabilizer F (base F false))]
      exact hEbase ▸ hg)
  have hca : Nat.card (C ⊓ graphLocalGroup F (base F false) : Subgroup G₀) = 3 := by
    have hh : Nat.card (C ⊓ graphLocalGroup F (base F false) : Subgroup G₀) =
        Nat.card (GaloisField 2 2)ˣ := Nat.card_congr eα.toEquiv
    rw [Nat.card_units,hfour] at hh
    exact hh
  have hcb : Nat.card (C ⊓ graphLocalGroup F (base F true) : Subgroup G₀) = 3 := by
    have hh : Nat.card (C ⊓ graphLocalGroup F (base F true) : Subgroup G₀) =
        Nat.card (GaloisField 2 2)ˣ := Nat.card_congr eβ.toEquiv
    rw [Nat.card_units,hfour] at hh
    exact hh
  obtain ⟨k,f,fin,ch,alg,d,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hsep := bTwo_odd_local_tori_disjoint H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) d hactor (reduced_bTwo_middle_central h hc hne hb hab hβu)
    (base_Z_ne_bot H true) C ho
  let : IsMulCommutative (cartan c) := cartan_abelian h c
  let : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hcomm : C ⊓ graphLocalGroup F (base F false) ≤
      centralizer (C ⊓ graphLocalGroup F (base F true) : Set G₀) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact setLike_mul_comm hy.1 hx.1
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (C ⊓ graphLocalGroup F (base F false)) (C ⊓ graphLocalGroup F (base F true)) hsep hcomm
  have hprod : Nat.card ((C ⊓ graphLocalGroup F (base F false)) ⊔
      (C ⊓ graphLocalGroup F (base F true)) : Subgroup G₀) = 9 := by
    rw [←Nat.card_congr ep.toEquiv,Nat.card_prod,hca,hcb]
  rw [←hprod]
  exact card_dvd_of_le (sup_le inf_le_left inf_le_left)

private theorem a5_neighbor_card
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (v : Vertex F) : Nat.card ((graph F).neighborSet v) = 5 := by
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let e (i : Bool) : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,GaloisField 2 2) := by
    cases i
    · exact (a 0).some.trans e₄.symm
    · exact (a 1).some.trans e₄.symm
  apply card_neighbors_of_indices F (fun _ => 5) ?_ v
  intro i
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let eG := (reduced_graphLinearQuotient h i (e i)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (GaloisField 2 2)).symm
  have hi := source_linear_edge_index_of_quotient (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj eG
  change (stabilizer F (base F (!i))).relIndex (stabilizer F (base F i)) =
    Nat.card (GaloisField 2 2) + 1 at hi
  rw [show stabilizer F (base F i) = F i from Subgroup.CosetGeometry.stabilizer_base F i,
    show stabilizer F (base F (!i)) = F (!i) from Subgroup.CosetGeometry.stabilizer_base F (!i),
    hfour] at hi
  exact hi

/-- On every supported twelve-path in the genuine strict A5 source apartment,
the entire chosen Cartan has a nontrivial intersection with the whole midpoint
permutation kernel U. No small-actor or kernel premise is added. -/
theorem strict_a5_source_cartan_kernel_ne_bot
    (h : HypothesisF11 L S)
    (a5 : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b)
    (_hp : p.IsPath) (_hl : p.length = 12)
    (hT : ∀ z ∈ p.support, z ∈ strictSourceApartment h hc hne hb hβu hns hlinear) :
    (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥ := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let c := chosenCartans h
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  apply nine_dvd_local_kernel_nontrivial F _ _ ?_
    (a5_bTwo_chosen_cartan_nine_dvd h a5 hc hne hb hβu)
    (a5_neighbor_card h a5 _)
  rintro _ ⟨k,hk,rfl⟩
  change φ k • cov.vertex (p.getVert 6) = _
  rw [←cov.vertex_smul]
  exact congrArg cov.vertex (reflectionApartment_fixed c r.t r.normalizes k hk _
    (hT _ (p.getVert_mem_support 6)))

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
