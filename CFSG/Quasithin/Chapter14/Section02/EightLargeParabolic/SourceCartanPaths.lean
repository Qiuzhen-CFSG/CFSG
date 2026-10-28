module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartan
public import Theory.GroupTheory.WeakBNPair.RegularTree.SevenCartanPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRootCoordinates

/-!
# Actual six-path radicals before reflection selection

The same full original Cartan fixes arbitrarily long paths by its order seven
and the actual valences three and nine. A six-path fixer factors through its
own two-core and this Cartan. Seven-path transitivity and odd seven-path
fixers make the radical regular on exits, of order two or eight, and disjoint
from its endpoint core. Thus an actual escaping involution is produced.
No selected path, reflection, root, or kernel-identification premise is used.

Source: DGS (14.1)--(14.2), printed pp.210--211.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanPaths
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
/-- The literal six-path radical, retaining the full Cartan, edge two-group,
endpoint two-core, exact order, and an involution outside that core. -/
@[expose] def HasSixPathRadical {G : Type*} [Group G]
    (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool) : Prop :=
    let A := reducedAmalgam L S
    let F := Universal.cosetFamily A
    ∃ d, ∃ p : (sourceGraph A).Walk d (base F i),
      p.IsPath ∧ p.length = 6 ∧ p.penultimate = base F (!i) ∧
      cartan c ≤ pathFixer (X := (A).Universal) p ∧
      Nat.card (pathRoot (X := (A).Universal) p) = (if i then 8 else 2) ∧
      pathRoot (X := (A).Universal) p ≤ twoGroup L S ∧
      Disjoint (pathRoot (X := (A).Universal) p) ((F i).pCoreIn 2) ∧
      ∃ x ∈ pathRoot (X := (A).Universal) p, x*x=1 ∧ x ∉ (F i).pCoreIn 2

private theorem six_path_radical_of_profile
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (hC : Nat.card (cartan c) = 7)
    (hval : ∀ v : SourceVertex (reducedAmalgam L S),
      Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v) = if v.type then 9 else 3)
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length = 7 → Odd (Nat.card
        (pathFixer (X := (reducedAmalgam L S).Universal) p))) (i : Bool) :
    HasSixPathRadical L S c i := by
  let A := reducedAmalgam L S
  let F := Universal.cosetFamily A
  let C := cartan c
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hvals (v : Vertex F) : Nat.card ((graph F).neighborSet v)=3 ∨
      Nat.card ((graph F).neighborSet v)=9 := by
    have hv := hval v
    cases he : v.type
    · exact Or.inl (by simpa only [he, Bool.false_eq_true, if_false] using hv)
    · exact Or.inr (by simpa only [he, if_true] using hv)
  have hCF (j : Bool) : C ≤ F j := by
    apply (cartan_le c).trans
    rw [originalMiddle, ←Universal.overlap_eq A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))]
    cases j
    · exact inf_le_left
    · exact inf_le_right
  have hfix (j : Bool) : ∀ x ∈ C, x • base F j = base F j := by
    intro x hx
    have hh : x ∈ F j := hCF j hx
    rw [←Subgroup.CosetGeometry.stabilizer_base F j] at hh
    exact hh
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨d,q,hq,hql,hqC,hfirst⟩ := seven_fixed_edge_path F C hC hvals htree
    hadj (hfix i) (hfix (!i)) 6 (by decide)
  let p := q.reverse
  have hp : p.IsPath := hq.reverse
  have hpl : p.length=6 := by simpa only [p,Walk.length_reverse] using hql
  have hprev : p.penultimate=base F (!i) := by
    change q.reverse.penultimate = _
    rw [Walk.penultimate_reverse]
    exact hfirst
  have hCp : C ≤ pathFixer (X := (A).Universal) p := by
    intro x hx k _
    apply hqC _ ?_ x hx
    rw [←List.mem_reverse,←Walk.support_reverse]
    exact p.getVert_mem_support k
  obtain ⟨v,hvC,w,hwC,hv,hw,hvw⟩ := seven_fixed_twoNeighbors F C hC hvals
    (base F i) (hfix i)
  have hexit : ∃ z, (graph F).Adj (base F i) z ∧ z≠p.penultimate ∧
      ∀ x∈C, x • z=z := by
    by_cases he : v=p.penultimate
    · exact ⟨w,hw,fun hh => hvw (he.trans hh.symm),hwC⟩
    · exact ⟨v,hv,he,hvC⟩
  obtain ⟨z,hz,hzne,hzC⟩ := hexit
  have hznew : z∉p.support := fun hm => hzne (htree.eq_penultimate_of_adj_end hp hz hm)
  have ho := hodd (p.concat hz) (hp.concat hznew hz) (by rw [Walk.length_concat,hpl])
  have hf := pathFixer_factorization c h p hprev hCp
  let : Finite ((graph F).neighborSet (base F i)) := Nat.finite_of_card_ne_zero (by
    have hv := hval (base F i)
    change Nat.card ((graph F).neighborSet (base F i))=(if i then 9 else 3) at hv
    rw [hv]; cases i <;> decide)
  have hpnil : ¬p.Nil := fun hn => by have := hn.length_eq_zero; omega
  have hr := card_pathRoot_add_one htree (source_action A) p hp hpnil
    (by rw [hpl]; exact htrans) C ⟨z,hz,hzne⟩ hzC hf ho
  have hroot : Nat.card (pathRoot (X := (A).Universal) p)=(if i then 8 else 2) := by
    have hv := hval (base F i)
    change Nat.card ((graph F).neighborSet (base F i))=(if i then 9 else 3) at hv
    rw [hv] at hr
    cases i <;> simp only [Bool.false_eq_true, if_false, if_true] at hr ⊢ <;> omega
  have hd : Disjoint (pathRoot (X := (A).Universal) p) ((F i).pCoreIn 2) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have he := universal_vertex_core_fixes_neighbors h (base F i) z hz
    rw [Subgroup.CosetGeometry.stabilizer_base] at he
    have hh : x∈pathRoot (X := (A).Universal) p ⊓ MulAction.stabilizer (A).Universal z :=
      ⟨hx.1,he hx.2⟩
    rwa [pathRoot_inf_stabilizer_eq_bot p hz ho] at hh
  have hdiv : 2∣Nat.card (pathRoot (X := (A).Universal) p) := by
    rw [hroot]; cases i <;> decide
  let : Finite (pathRoot (X := (A).Universal) p) := Nat.finite_of_card_ne_zero (by
    rw [hroot]; cases i <;> decide)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := pathRoot (X := (A).Universal) p) 2 hdiv
  refine ⟨d,p,hp,hpl,hprev,hCp,hroot,aligned_pathRoot_le_twoGroup h p hprev,hd,x,x.property,?_,?_⟩
  · exact congrArg Subtype.val (by simpa only [hx,pow_two] using pow_orderOf_eq_one x)
  · intro hxcore
    have he := disjoint_def.mp hd x.property hxcore
    have hxe : x=1 := Subtype.ext he
    rw [hxe,orderOf_one] at hx
    contradiction


private theorem six_path_radical_of_full_profile
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (hC : Nat.card (cartan c) = 7)
    (hval : ∀ v : SourceVertex (reducedAmalgam L S),
      Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v) = if v.type then 9 else 3)
    (hp : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)) 7 ∧
      ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) (i : Bool) :
    HasSixPathRadical L S c i :=
  six_path_radical_of_profile h c hC hval hp.2.1 hp.2.2 i


open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

local notation "L" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "A" => reducedAmalgam L (T : Subgroup G)

private theorem source_borel_and_sylow :
    commonBorel L (T : Subgroup G) = H ⊓ M ∧
      reducedSylow L (T : Subgroup G) = (T : Subgroup G) := by
  have hB : commonBorel L (T : Subgroup G) = H ⊓ M := by
    change borel (locals T M Mc H 1) (T : Subgroup G) ⊔
      borel (locals T M Mc H 0) (T : Subgroup G) ⊔ (T : Subgroup G) = _
    rw [sup_comm (borel (locals T M Mc H 1) (T : Subgroup G))
      (borel (locals T M Mc H 0) (T : Subgroup G))]
    exact (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  refine ⟨hB,?_⟩
  change (commonBorel L (T : Subgroup G)).pCoreIn 2 = _
  rw [hB]
  exact source_borel_twoCore hG T hempty hM hu hmany hcard e H hH eR

set_option maxHeartbeats 800000 in
/-- The literal original universal tree has cubic and nine-valent endpoints. -/
theorem source_tree_neighbor_cards (v : SourceVertex A) :
    Nat.card ((sourceGraph A).neighborSet v) = if v.type then 9 else 3 := by
  let h : HypothesisF11 L (T : Subgroup G) := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let F := reducedFamily L (T : Subgroup G)
  let J := G₀ L (T : Subgroup G)
  let cov := bOne_tree_cover h
  have hval (x : Vertex F) : Nat.card ((graph F).neighborSet x)=if x.type then 9 else 3 := by
    obtain ⟨hB,hS⟩ := source_borel_and_sylow hG T hempty hM hu hmany hcard e H hH eR
    have ht := reduced_triple h
    apply card_neighbors_of_indices F (fun i => if i then 9 else 3)
    intro i
    cases i
    · change (F true).relIndex (F false) = 3
      rw [←inf_relIndex_right (F true) (F false),inf_comm,
        show F false ⊓ F true = (B₀ L (T : Subgroup G)).subgroupOf J from ht.intersection]
      change ((B₀ L (T : Subgroup G)).subgroupOf J).relIndex
        ((P₀ L (T : Subgroup G) 0).subgroupOf J) = 3
      rw [relIndex_subgroupOf (show P₀ L (T : Subgroup G) 0 ≤ J from le_sup_left),
        B₀_eq_source h,P₀_eq_source h,hS,hB]
      change (H ⊓ M).relIndex (parabolic (locals T M Mc H) (T : Subgroup G) 1) = 3
      rw [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.1]
      exact (source_local_degrees hG T hempty hM hu hmany hcard e H hH eR).2
    · change (F false).relIndex (F true) = 9
      rw [←inf_relIndex_right (F false) (F true),
        show F false ⊓ F true = (B₀ L (T : Subgroup G)).subgroupOf J from ht.intersection]
      change ((B₀ L (T : Subgroup G)).subgroupOf J).relIndex
        ((P₀ L (T : Subgroup G) 1).subgroupOf J) = 9
      rw [relIndex_subgroupOf (show P₀ L (T : Subgroup G) 1 ≤ J from le_sup_right),
        B₀_eq_source h,P₀_eq_source h,hS,hB]
      change (H ⊓ M).relIndex (parabolic (locals T M Mc H) (T : Subgroup G) 0) = 9
      rw [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1]
      exact (source_local_degrees hG T hempty hM hu hmany hcard e H hH eR).1
  have he := Nat.card_congr (Equiv.ofBijective (cov.hom.mapNeighborSet v)
    (cov.neighbor_bijective v))
  exact he.trans (hval (cov.vertex v))

set_option maxHeartbeats 800000 in
/-- The actual six-path radicals and escaping involutions, before choosing
any full-Cartan reflection. The whole same Cartan and original endpoint core remain literal. -/
theorem source_six_path_radical
    (c : CompatibleCartans L (reducedSylow L (T : Subgroup G))) (i : Bool) :
    HasSixPathRadical L (T : Subgroup G) c i := by
  have h : HypothesisF11 L (T : Subgroup G) := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  exact six_path_radical_of_full_profile h c
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    (source_path_profile hG T hempty hM hu hmany hcard e H hH eR) i

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanPaths
