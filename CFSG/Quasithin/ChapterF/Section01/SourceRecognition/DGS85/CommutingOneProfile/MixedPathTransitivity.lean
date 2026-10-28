module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedPathFixers
public import Theory.GroupTheory.AmalgamGraph.PathSupplement
/-!
# Five-walk transitivity in the mixed commuting branch

For a fixed first edge there are 64 nonbacktracking five-walks. The actual
edge two-core also has order 64. Its action on this set is free because
the pointwise five-walk fixer has odd order. Equality of cardinalities
makes this action transitive; local transitivity aligns the first edge.

Both vertex orientations, repeated vertices, the full reduced Borel and
the original reduced-to-ambient inclusion are retained. No tree or
amalgam recognition assumption is used.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7)(c,f), printed pp.174--175; (3.4)(c), printed p.74.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

private def edgePathsEquiv {V : Type*} (Γ : SimpleGraph V) (n : ℕ)
    (a : V) (b : Γ.neighborSet a) :
    {p : BasedWalk Γ (n+1) a // p.Nonbacktracking ∧ p.1 = b} ≃
      BasedWalk.Forward Γ n a b :=
  (show {p : BasedWalk Γ (n+1) a // p.Nonbacktracking ∧ p.1 = b} ≃
      {p : BasedWalk Γ n b // Avoids Γ a p} from {
    toFun := by
      rintro ⟨⟨c,p⟩,hp,hc⟩
      change c = b at hc
      subst c
      exact ⟨p,by cases n <;> exact hp⟩
    invFun := fun p => ⟨⟨b,p.val⟩,by cases n <;> exact p.property,rfl⟩
    left_inv := by rintro ⟨⟨c,p⟩,hp,hc⟩; change c = b at hc; subst c; rfl
    right_inv := by intro p; rfl }).trans (forwardEquiv Γ n a b).symm

private theorem nb_getVert {V : Type*} {Γ : SimpleGraph V} {n : ℕ} {a : V}
    (p : BasedWalk Γ n a) (hp : p.Nonbacktracking) :
    ∀ i, i+2 ≤ p.toWalk.length → p.toWalk.getVert i ≠ p.toWalk.getVert (i+2) := by
  induction n using Nat.twoStepInduction generalizing a with
  | zero => intro i hi; rw [length_toWalk] at hi; omega
  | one => intro i hi; rw [length_toWalk] at hi; omega
  | more n _ ih =>
    intro i hi
    cases i with
    | zero => simpa only [BasedWalk.toWalk, Walk.getVert_zero, Walk.getVert_cons_succ] using hp.1.symm
    | succ i =>
      exact ih p.2 hp.2 i (by rw [length_toWalk] at *; omega)

private theorem basedFixer_eq {G : Type*} [Group G] (F : Bool → Subgroup G)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a) :
    pathStabilizer F p = pathFixer (X := G) p.toWalk := by
  ext x
  rw [mem_pathFixer_support, support_toWalk]
  rfl

private theorem first_smul {G : Type*} [Group G] (F : Bool → Subgroup G)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (g : stabilizer F a) : ((actPath F g p).1 : Vertex F) = (g : G) • (p.1 : Vertex F) := by
  have hh := congrArg (fun l : List (Vertex F) => l.tail.head?) (vertices_actPath F g p)
  simpa only [BasedWalk.vertices, List.tail_cons, List.map_cons, head_vertices,
    List.head?_map, Option.map_some, Option.some.injEq] using hh

private theorem edge_transitive_of_odd {G : Type*} [Group G] [Finite G]
    (F : Bool → Subgroup G) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5)
    {a : Vertex F} (b : (graph F).neighborSet a)
    (T : Subgroup G) (hT : T ≤ stabilizer F a ⊓ stabilizer F b)
    (hTc : Nat.card T = 64) (hTp : IsPGroup 2 T)
    (hodd : ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F p))) :
    ∀ p q : BasedWalk (graph F) 5 a, p.Nonbacktracking → q.Nonbacktracking →
      p.1 = b → q.1 = b → ∃ g ∈ T, p.vertices.map (g • ·) = q.vertices := by
  classical
  let : MulAction (stabilizer F a) (BasedWalk (graph F) 5 a) := pathAction F 5 a
  intro p q hp hq hpb hqb
  let Y := {p : BasedWalk (graph F) 5 a // p.Nonbacktracking ∧ p.1 = b}
  let : ∀ v : Vertex F, Finite ((graph F).neighborSet v) :=
    fun v => Nat.finite_of_card_ne_zero (by rw [hval]; cases v.type <;> decide)
  have hflip : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w hvw
    have hn := hvw.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hY : Nat.card Y = 64 := by
    rw [Nat.card_congr (edgePathsEquiv (graph F) 4 a b),
      card_forward (graph F) (fun v => v.type) (fun i => if i then 3 else 5) hflip hval 4 a b b.property]
    cases (b : Vertex F).type <;> decide
  let : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  let j : T →* stabilizer F a := inclusion (hT.trans inf_le_left)
  let f : T → Y := fun x => ⟨j x • p,
    (nonbacktracking_smul_path F (j x) p).mpr hp,by
      apply Subtype.ext
      change ((actPath F (j x) p).1 : Vertex F) = b
      rw [first_smul,hpb]
      exact (hT x.property).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hs : j x • p = j y • p := congrArg Subtype.val hxy
    have hz : ((j x)⁻¹ * j y) • p = p := by
      rw [mul_smul,←hs,inv_smul_smul]
    have hfix : ((x : G)⁻¹ * y) ∈ pathStabilizer F p :=
      (mem_pathStabilizer_iff F p ((j x)⁻¹ * j y)).mpr hz
    obtain ⟨k,hk⟩ := hTp (x⁻¹*y)
    have hd : orderOf ((x : G)⁻¹*y) ∣ 2^k := by
      change orderOf ((x⁻¹*y : T) : G) ∣ 2^k
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk
    have ho : orderOf ((x : G)⁻¹*y) ∣ Nat.card (pathStabilizer F p) := by
      simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard
        (⟨_,hfix⟩ : pathStabilizer F p)
    apply Subtype.ext
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes ((hodd p hp).coprime_two_right.pow_right k) ho hd))
  obtain ⟨x,hx⟩ := (hf.bijective_of_nat_card_le (by omega : Nat.card Y ≤ Nat.card T)).surjective ⟨q,hq,hqb⟩
  exact ⟨x,x.property,(vertices_smul_path F (j x) p).symm.trans
    (congrArg BasedWalk.vertices (congrArg Subtype.val hx))⟩

private theorem root_transitive_of_edge_cores {G : Type*} [Group G] [Finite G]
    (F : Bool → Subgroup G) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5)
    (hcard : ∀ {a b : Vertex F}, (graph F).Adj a b →
      Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 64)
    (hodd : ∀ {a : Vertex F} (p : BasedWalk (graph F) 5 a), p.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F p))) (a : Vertex F) :
    RootPathTransitive (graph F) G a 5 := by
  let : MulAction (stabilizer F a) (BasedWalk (graph F) 5 a) := pathAction F 5 a
  intro p q hp hq
  obtain ⟨g,hga,hg⟩ := locally_transitive F p.1.property q.1.property
  let g' : stabilizer F a := ⟨g,hga⟩
  let p' := g' • p
  have hp' : p'.Nonbacktracking := (nonbacktracking_smul_path F g' p).mpr hp
  have hfirst : p'.1 = q.1 := Subtype.ext ((first_smul F p g').trans hg)
  let E := stabilizer F a ⊓ stabilizer F (q.1 : Vertex F)
  obtain ⟨t,ht,htq⟩ := edge_transitive_of_odd F hval q.1 (E.pCoreIn 2)
    (E.pCoreIn_le 2) (hcard q.1.property) (isPGroup_pCoreIn 2 E) hodd
    p' q hp' hq hfirst rfl
  refine ⟨t*g,?_,?_⟩
  · rw [mul_smul,hga]
    exact ((E.pCoreIn_le 2) ht).1
  · rw [show p'.vertices = p.vertices.map (g • ·) from vertices_smul_path F g' p,
      List.map_map] at htq
    simpa only [Function.comp_def,mul_smul] using htq

/-- The counting argument also applies to intrinsically marked reduced
endpoints: the edge two-core acts freely on its 64 five-walk extensions. -/
theorem binary_graph_five_walk_transitive_of_edge_cores
    {G : Type*} [Group G] [Finite G] (F : Bool → Subgroup G)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5)
    (hcard : ∀ {a b : Vertex F}, (graph F).Adj a b →
      Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 64)
    (hodd : ∀ {a : Vertex F} (p : BasedWalk (graph F) 5 a), p.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F p))) (a : Vertex F) :
    RootPathTransitive (graph F) G a 5 :=
  root_transitive_of_edge_cores F hval hcard hodd a

/-- The literal walk fixer and the length-indexed fixer agree. This carries
oddness through the two path representations without a tree assumption. -/
theorem based_fixer_odd_of_walk {G : Type*} [Group G] (F : Bool → Subgroup G)
    (hodd : ∀ {a b : Vertex F} (p : (graph F).Walk a b), 5 ≤ p.length →
      (∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) →
        Odd (Nat.card (pathFixer (X := G) p)))
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a)
    (hp : p.Nonbacktracking) (hn : 5 ≤ n) :
    Odd (Nat.card (pathStabilizer F p)) := by
  rw [basedFixer_eq]
  exact hodd p.toWalk (by rwa [length_toWalk]) (nb_getVert p hp)

variable {G : Type*} [Group G] [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true

/-- The two-core of every actual reduced edge stabilizer has order 64. -/
theorem mixed_binary_graph_edge_core_card (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b : Vertex F} (hab : (graph F).Adj a b) :
    Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 64 := by
  have ht := Reduction.reduced_triple h
  have hBG : Reduction.B₀ ![K,U₀] S ≤ M :=
    (show Reduction.B₀ ![K,U₀] S ≤ Reduction.P₀ ![K,U₀] S 0 from le_sup_right).trans le_sup_left
  have hRM : twoCore (commonBorel ![K,U₀] S) ≤ M :=
    (show twoCore (commonBorel ![K,U₀] S) ≤ Reduction.B₀ ![K,U₀] S from le_sup_right).trans hBG
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F hab
  rw [hg,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
    2 _ (MulAut.conj g).injective,card_map_of_injective (MulAut.conj g).injective,
    show F false ⊓ F true = (Reduction.B₀ ![K,U₀] S).subgroupOf M from ht.intersection,
    pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
  change Nat.card ((twoCore (commonBorel ![K,U₀] S)).subgroupOf M) = 64
  rw [Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv]
  exact (mixed_binary_graph_exact_row_size K U₀ S h eK eU hc hb hcomm).1

/-- The existing odd-fixer theorem on length-indexed nonbacktracking walks,
retaining the literal pointwise stabilizer used by coset coverings. -/
theorem mixed_binary_graph_based_fixer_odd (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a)
    (hp : p.Nonbacktracking) (hn : 5 ≤ n) : Odd (Nat.card (pathStabilizer F p)) := by
  rw [basedFixer_eq]
  exact mixed_binary_graph_long_walk_fixer_odd K U₀ S h eK eU hc hb hcomm p.toWalk
    (by rwa [length_toWalk]) (nb_getVert p hp)

/-- Nonbacktracking five-walks from either vertex orbit are transitive under
its actual stabilizer. The edge two-core supplies the 64-element free action. -/
theorem mixed_binary_graph_five_walk_transitive (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (a : Vertex F) : RootPathTransitive (graph F) M a 5 := by
  apply root_transitive_of_edge_cores F (mixed_reduced_neighbor_cards K U₀ S h eK eU)
    (fun hab => mixed_binary_graph_edge_core_card K U₀ S h eK eU hc hb hcomm hab)
  intro a p hp
  exact mixed_binary_graph_based_fixer_odd K U₀ S h eK eU hc hb hcomm p hp le_rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
