module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.PairOrbitData
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.RootCertificates

/-!
# Transporting the four representative ranks through certified source trees

Simultaneous conjugacy preserves the native displacement-product rank.
Changing basis in a commuting involution four-group preserves the same product
rank. Induction on the certified parent indices therefore transports the four
literal root ranks to all nodes, with square-one and commutativity retained.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/
public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open ElementaryNormalizerCover.PureTwoA.NativePair
open Cardinality.LocalInvolutionCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
attribute [local irreducible] modelGroup matrixA matrixB toMatrix nativeWord pairRank
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
set_option maxRecDepth 2000

private theorem pairRank_swap (x y : Model) (hc : Commute x y) :
    pairRank x y = pairRank y x := by
  have hm : toMatrix x * toMatrix y = toMatrix y * toMatrix x := by
    simpa only [map_mul] using congrArg toMatrix hc.eq
  have he : (toMatrix x - 1) * (toMatrix y - 1) =
      (toMatrix y - 1) * (toMatrix x - 1) := by
    simp only [mul_sub,sub_mul,mul_one,one_mul]
    rw [hm]
    exact sub_sub_sub_comm _ _ _ _
  unfold pairRank
  exact congrArg Matrix.rank he


private theorem matrix_sub_eq_add (A B : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    A - B = A + B := by
  have hn : ∀ z : ZMod 2, -z = z := by decide +kernel
  ext i j
  exact sub_eq_add_neg _ _ |>.trans (congrArg (fun z => A i j + z) (hn (B i j)))

private theorem displacement_product (A B : Matrix (Fin 112) (Fin 112) (ZMod 2))
    (hAA : A*A=1) : (A-1)*(A*B-1) = (A-1)*(B-1) := by
  simp only [matrix_sub_eq_add,add_mul,mul_add,mul_one,one_mul]
  rw [← mul_assoc,hAA,one_mul]
  abel

private theorem pairRank_product (x y : Model) (hx : x ^ 2 = 1) :
    pairRank x (x*y) = pairRank x y := by
  have hxx : toMatrix x * toMatrix x = 1 := by
    rw [← map_mul,← pow_two,hx,map_one]
  unfold pairRank
  rw [map_mul]
  exact congrArg Matrix.rank (displacement_product _ _ hxx)


theorem pairRank_basis (x y u v : Model) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hc : Commute x y)
    (he : (u = x ∧ v = y) ∨ (u = y ∧ v = x) ∨
      (u = x ∧ v = x*y) ∨ (u = x*y ∧ v = x) ∨
      (u = y ∧ v = x*y) ∨ (u = x*y ∧ v = y)) :
    pairRank u v = pairRank x y := by
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    rw [h1,h2]
  · exact (pairRank_swap x y hc).symm
  · exact pairRank_product x y hx
  · rw [pairRank_swap _ _ ((Commute.refl x).mul_left hc.symm),pairRank_product x y hx]
  · rw [hc.eq,pairRank_product y x hy,pairRank_swap y x hc.symm]
  · rw [pairRank_swap _ _ (hc.mul_left (Commute.refl y)),hc.eq,pairRank_product y x hy,
      pairRank_swap y x hc.symm]


private def State (r : ℕ) (x y : Model) : Prop :=
  x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ Commute x y ∧ pairRank x y = r

private theorem state_basis (r : ℕ) (p q : PairOrbitData.Pair)
    (hp : State r (nativeWord p.1) (nativeWord p.2)) (he : PairOrbitData.sameBasis p q) :
    State r (nativeWord q.1) (nativeWord q.2) := by
  let x := nativeWord p.1
  let y := nativeWord p.2
  obtain ⟨hx,hy,hc,hr⟩ := hp
  have hxy : (x*y)^2 = 1 := by rw [hc.mul_pow,hx,hy,mul_one]
  have hcx : Commute (x*y) x := (Commute.refl x).mul_left hc.symm
  have hcy : Commute (x*y) y := hc.mul_left (Commute.refl y)
  have he' : (nativeWord q.1 = x ∧ nativeWord q.2 = y) ∨
      (nativeWord q.1 = y ∧ nativeWord q.2 = x) ∨
      (nativeWord q.1 = x ∧ nativeWord q.2 = x*y) ∨
      (nativeWord q.1 = x*y ∧ nativeWord q.2 = x) ∨
      (nativeWord q.1 = y ∧ nativeWord q.2 = x*y) ∨
      (nativeWord q.1 = x*y ∧ nativeWord q.2 = y) := by
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [nativeWord_mul,x,y] <;> tauto
  have hr' := (pairRank_basis x y _ _ hx hy hc he').trans hr
  refine ⟨?_,?_,?_,hr'⟩ <;>
    rcases he' with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      simp only [h1,h2]
  all_goals first
    | exact hx
    | exact hy
    | exact hxy
    | exact hc
    | exact hc.symm
    | exact hcx
    | exact hcx.symm
    | exact hcy
    | exact hcy.symm


theorem pairRank_sameBasis (p q : PairOrbitData.Pair)
    (hx : nativeWord p.1 ^ 2 = 1) (hy : nativeWord p.2 ^ 2 = 1)
    (hc : Commute (nativeWord p.1) (nativeWord p.2))
    (he : PairOrbitData.sameBasis p q) :
    pairRank (nativeWord q.1) (nativeWord q.2) = pairRank (nativeWord p.1) (nativeWord p.2) :=
  (state_basis _ p q ⟨hx,hy,hc,rfl⟩ he).2.2.2

private theorem nativeWord_action (b : Bool) (m : Fin 8192)
    (hb : fastAction b m.val < 8192) :
    nativeWord (PairOrbitData.act b m) =
      (MulAut.conj (sourceGenerator b : Model)⁻¹) (nativeWord m) := by
  have he := congrArg (fun x : sourceSubgroup => (x : Model)) (source_action_law b m)
  unfold nativeWord PairOrbitData.act
  change ((maskProduct kernelFactor (fastAction b m.val % 8192) : sourceSubgroup) : Model) = _
  rw [Nat.mod_eq_of_lt hb,← action_fast]
  simpa only [MulAut.conj_apply,inv_inv,Subgroup.coe_mul,Subgroup.coe_inv,nativeWord] using he.symm

private theorem state_action (r : ℕ) (b : Bool) (p : PairOrbitData.Pair)
    (h1 : fastAction b p.1.val < 8192) (h2 : fastAction b p.2.val < 8192)
    (hp : State r (nativeWord p.1) (nativeWord p.2)) :
    State r (nativeWord (PairOrbitData.act b p.1)) (nativeWord (PairOrbitData.act b p.2)) := by
  obtain ⟨hx,hy,hc,hr⟩ := hp
  rw [nativeWord_action b _ h1,nativeWord_action b _ h2]
  refine ⟨?_,?_,hc.map _,?_⟩
  · rw [← map_pow,hx,map_one]
  · rw [← map_pow,hy,map_one]
  · rw [pairRank_conj,hr]

private theorem tree_rank {n : ℕ} (hn : 0 < n) (r : ℕ)
    (nodes : Fin n → PairOrbitData.Pair) (parents : Fin n → Fin n)
    (actions : Fin n → Bool)
    (hroot : State r (nativeWord (nodes ⟨0,hn⟩).1) (nativeWord (nodes ⟨0,hn⟩).2))
    (hlt : ∀ i, i.val ≠ 0 → (parents i).val < i.val)
    (hedge : ∀ i, i.val ≠ 0 →
      fastAction (actions i) (nodes (parents i)).1.val < 8192 ∧
      fastAction (actions i) (nodes (parents i)).2.val < 8192 ∧
      PairOrbitData.sameBasis
        (PairOrbitData.act (actions i) (nodes (parents i)).1,
         PairOrbitData.act (actions i) (nodes (parents i)).2) (nodes i)) :
    ∀ i, pairRank (nativeWord (nodes i).1) (nativeWord (nodes i).2) = r := by
  have hs : ∀ i, State r (nativeWord (nodes i).1) (nativeWord (nodes i).2) := by
    intro i
    have hh : ∀ k : ℕ, ∀ i : Fin n, i.val = k → State r (nativeWord (nodes i).1) (nativeWord (nodes i).2) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro i hik
        by_cases hz : i.val = 0
        · have he : i = ⟨0,hn⟩ := Fin.ext hz
          exact he.symm ▸ hroot
        · obtain ⟨h1,h2,he⟩ := hedge i hz
          exact state_basis r _ _ (state_action r _ _ h1 h2
            (ih _ (hik ▸ hlt i hz) _ rfl)) he
    exact hh i.val i rfl
  exact fun i => (hs i).2.2.2

private theorem state_of_marked (r : ℕ) (m n : Fin 8192)
    (hm : nativeWord m ∈ MarkedIntersection.markedIntersection)
    (hn : nativeWord n ∈ MarkedIntersection.markedIntersection)
    (hr : pairRank (nativeWord m) (nativeWord n) = r) :
    State r (nativeWord m) (nativeWord n) := by
  let := MarkedIntersection.markedIntersection_elementary
  refine ⟨elemPow_eq_one_of_isElementaryAbelian _ hm,
    elemPow_eq_one_of_isElementaryAbelian _ hn,?_,hr⟩
  let x : MarkedIntersection.markedIntersection := ⟨nativeWord m,hm⟩
  let y : MarkedIntersection.markedIntersection := ⟨nativeWord n,hn⟩
  exact congrArg (fun z : MarkedIntersection.markedIntersection => (z : Model)) (mul_comm x y)

private theorem root_state_0 : State 16
    (nativeWord (PairOrbitData.nodes0 0).1) (nativeWord (PairOrbitData.nodes0 0).2) := by
  have he : PairOrbitData.nodes0 0 = (1,6) := by decide +kernel
  rw [he]
  apply state_of_marked
  · exact nativeWord_mem_intersection 0 1 (by decide +kernel)
  · exact nativeWord_mem_intersection 14 6 (by decide +kernel)
  · exact RootCertificates.root_rank_0

theorem nodes_rank_0 (j : Fin 245) :
    pairRank (nativeWord (PairOrbitData.nodes0 j).1)
      (nativeWord (PairOrbitData.nodes0 j).2) = 16 := by
  apply tree_rank (by decide) 16 PairOrbitData.nodes0 PairOrbitData.parents0
    PairOrbitData.actions0 root_state_0
    (fun k hk => PairOrbitData.decrease_0 k (fun he => hk (congrArg Fin.val he)))
    (fun k hk => PairOrbitData.edges_0 k (fun he => hk (congrArg Fin.val he)))

private theorem root_state_1 : State 16
    (nativeWord (PairOrbitData.nodes1 0).1) (nativeWord (PairOrbitData.nodes1 0).2) := by
  have he : PairOrbitData.nodes1 0 = (6,6601) := by decide +kernel
  rw [he]
  apply state_of_marked
  · exact nativeWord_mem_intersection 14 6 (by decide +kernel)
  · exact nativeWord_mem_intersection 14 6601 (by decide +kernel)
  · exact RootCertificates.root_rank_1

theorem nodes_rank_1 (j : Fin 2418) :
    pairRank (nativeWord (PairOrbitData.nodes1 j).1)
      (nativeWord (PairOrbitData.nodes1 j).2) = 16 := by
  apply tree_rank (by decide) 16 PairOrbitData.nodes1 PairOrbitData.parents1
    PairOrbitData.actions1 root_state_1
    (fun k hk => PairOrbitData.decrease_1 k (fun he => hk (congrArg Fin.val he)))
    (fun k hk => PairOrbitData.edges_1 k (fun he => hk (congrArg Fin.val he)))

private theorem root_state_2 : State 16
    (nativeWord (PairOrbitData.nodes2 0).1) (nativeWord (PairOrbitData.nodes2 0).2) := by
  have he : PairOrbitData.nodes2 0 = (3400,5254) := by decide +kernel
  rw [he]
  apply state_of_marked
  · exact nativeWord_mem_intersection 5 3400 (by decide +kernel)
  · exact nativeWord_mem_intersection 5 5254 (by decide +kernel)
  · exact RootCertificates.root_rank_2

theorem nodes_rank_2 (j : Fin 44) :
    pairRank (nativeWord (PairOrbitData.nodes2 j).1)
      (nativeWord (PairOrbitData.nodes2 j).2) = 16 := by
  apply tree_rank (by decide) 16 PairOrbitData.nodes2 PairOrbitData.parents2
    PairOrbitData.actions2 root_state_2
    (fun k hk => PairOrbitData.decrease_2 k (fun he => hk (congrArg Fin.val he)))
    (fun k hk => PairOrbitData.edges_2 k (fun he => hk (congrArg Fin.val he)))

private theorem root_state_3 : State 20
    (nativeWord (PairOrbitData.nodes3 0).1) (nativeWord (PairOrbitData.nodes3 0).2) := by
  have he : PairOrbitData.nodes3 0 = (6,2978) := by decide +kernel
  rw [he]
  apply state_of_marked
  · exact nativeWord_mem_intersection 14 6 (by decide +kernel)
  · exact nativeWord_mem_intersection 3 2978 (by decide +kernel)
  · exact RootCertificates.root_rank_3

theorem nodes_rank_3 (j : Fin 124) :
    pairRank (nativeWord (PairOrbitData.nodes3 j).1)
      (nativeWord (PairOrbitData.nodes3 j).2) = 20 := by
  apply tree_rank (by decide) 20 PairOrbitData.nodes3 PairOrbitData.parents3
    PairOrbitData.actions3 root_state_3
    (fun k hk => PairOrbitData.decrease_3 k (fun he => hk (congrArg Fin.val he)))
    (fun k hk => PairOrbitData.edges_3 k (fun he => hk (congrArg Fin.val he)))

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
