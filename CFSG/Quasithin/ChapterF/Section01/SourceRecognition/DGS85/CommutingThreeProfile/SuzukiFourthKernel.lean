module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEightPathBound
public import Theory.GroupTheory.AmalgamGraph.NormalTwoDetection
/-!
# Vanishing of the full linear fourth kernel

An eight-path through a linear orbit has a linear midpoint. The full
fourth kernel there fixes that path, so its order is at most q. Conjugacy
transports the bound back to the original linear vertex. The kernel is a
normal two-subgroup of the full stabilizer. Minimality of its natural
center of order q² forces their intersection to vanish; Sylow-center
span detection then kills the entire fourth kernel.

The original completion inclusion and every larger ball kernel are
retained. This closes the terminal full-kernel step without assuming
that the two-core equals the first local permutation kernel.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7)--(12.9), printed pp.184--189, the linear full-kernel series.
-/
public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The full radius-four kernel at the linear vertex is trivial. -/
theorem source_suzuki_linear_fourth_kernel_trivial
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    : ∀ r : ℕ, 4 ≤ r →
      ballKernel (reducedFamily L S) (base (reducedFamily L S) i) r = ⊥ ∧
      (ballKernel (reducedFamily L S) (base (reducedFamily L S) i) r).map (G₀ L S).subtype = ⊥ := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let N := ballKernel F m 4
  let Zm := Z F m
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite N := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 4)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hNQ : N ≤ Q F m := (ballKernel_antitone F m (by decide : 2 ≤ 4)).trans
    (source_suzuki_second_kernel_le_core h (!i) eSuz (by cases i <;> exact e) hk m)
  have hpN : IsPGroup 2 N := (isPGroup_pCoreIn 2 _).to_le hNQ
  have hQA : Q F m ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hNA : N ≤ A := hNQ.trans hQA
  have hZA : Zm ≤ A := ((source_Z_Q_U (reduced_triple h) m).1.trans (map_subtype_le _)).trans hQA
  have hNcard : Nat.card N ≤ Nat.card k := by
    have hadj : (graph F).Adj m (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
    obtain ⟨p,_,hp,_,_⟩ := source_mixed_odd_fixed_paths h i hn e eSuz Ry hRy
      (⊥ : Subgroup (G₀ L S)) (by simp) 7 hadj bot_le
    have htype : (p.toWalk.getVert 4).type = i := by
      have he := (even_walk_iff F (p.toWalk.take 4)).mp (by
        rw [SimpleGraph.Walk.take_length,BasedWalk.length_toWalk]
        decide)
      exact he.symm
    obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F (p.toWalk.getVert 4)
    rw [htype] at hg
    have hmap : N.map (MulAut.conj g).toMonoidHom = ballKernel F (p.toWalk.getVert 4) 4 := by
      rw [←hg,ballKernel_translate]
    have hi := (source_suzuki_eight_path_two_subgroup_bound h i hb3 T hT e hz hcard hcardy
      hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch
      p hp rfl (N.map (MulAut.conj g).toMonoidHom) (hpN.map _)
      (hmap ▸ midpoint_kernel_le_fixer F p)).1
    rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] at hi
    exact hi
  have hnorm : stabilizer F m ≤ normalizer (N : Set (G₀ L S)) := stabilizer_le_normalizer_ballKernel F m 4
  let I := (N ⊓ Zm).subgroupOf A
  let : I.Normal := normal_subgroupOf_of_le_normalizer
    ((star_le_stabilizer i).trans ((le_inf hnorm (stabilizer_normalizes_Z F m)).trans
      inf_normalizer_le_normalizer_inf))
  have hNZ : N ⊓ Zm = ⊥ := by
    rcases hmin I inferInstance (subgroupOf_mono A inf_le_right) with hi | hi
    · have hm := congrArg (Subgroup.map A.subtype) hi
      change ((N ⊓ Zm).subgroupOf A).map A.subtype = (⊥ : Subgroup A).map A.subtype at hm
      rwa [map_subgroupOf_eq_of_le (inf_le_left.trans hNA),Subgroup.map_bot] at hm
    · have hZN : Zm ≤ N := by
        intro z hzZ
        have hh : (⟨z,hZA hzZ⟩ : A) ∈ I := hi ▸ hzZ
        exact hh.1
      have hle := (Nat.card_le_card_of_injective (inclusion hZN) (inclusion_injective _)).trans hNcard
      change Nat.card (Z F m) ≤ Nat.card k at hle
      rw [hcard] at hle
      nlinarith
  have hbot : N = ⊥ := normal_two_eq_bot_of_disjoint_sylowCenterSpan
    (stabilizer F m) N (ballKernel_le_stabilizer F m 4) hpN hnorm (disjoint_iff.mpr hNZ)
  intro r hr
  have he : ballKernel F m r = ⊥ := bot_unique ((ballKernel_antitone F m hr).trans hbot.le)
  exact ⟨he,by rw [he,Subgroup.map_bot]⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
