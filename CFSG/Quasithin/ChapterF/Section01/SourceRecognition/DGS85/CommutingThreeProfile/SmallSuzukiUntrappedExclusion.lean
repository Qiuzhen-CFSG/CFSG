module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiNinePathTerminal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiPathCenterTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiSecondIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiUntrappedPropagation

/-!
# Excluding the actual zero-parameter untrapped nine-path fixer

The literal nine-path two-subgroup centralizes the middle span by remote
critical-center propagation. An escaping incoming centralizer then gives
the other span centralization through the five-neighbor action. Both
binary second indices come from the moved-center branch and the original
three-path exchange. These source producers discharge every local action
and index in the faithful-tree terminal contradiction.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- Every element in the untrapped branch of the literal small-Suzuki
nine-path two-subgroup is identity. All local actions, span centralizations,
and binary indices are derived from the original source data. -/
theorem source_small_suzuki_nine_path_untrapped_eq_one
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hq : Nat.card k = 2)
    (Tlin : Sylow 2 (star L S (!i)))
    (hTlin : (Tlin : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hca : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hcc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ D)
    (hesc : ¬ V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1 ⊓
      centralizer ({t} : Set (G₀ L S)) ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hbranch : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) : t = 1 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.1
  let C := centralizer ({t} : Set (G₀ L S))
  have hcore := source_mixed_path_two_subgroup_core h (!i) eLin
    (by cases i <;> exact eSuz) p hp D hD hfix
  have htype : w.type = i := by
    have h3 : (p.2.2.1 : Vertex F).type = i := congrArg Subgroup.CosetGeometry.Vertex.type hy
    have h4 : i ≠ z.type := h3 ▸ p.2.2.2.1.property.1
    exact (Bool.eq_not_iff.mpr p.2.2.2.2.1.property.1.symm).trans (Bool.not_eq_iff.mpr h4.symm)
  have hzy : (graph F).Adj z y := by
    have hh : (graph F).Adj z (p.2.2.1 : Vertex F) := p.2.2.2.1.property.symm
    simpa only [hy] using hh
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwc : (graph F).Adj w c := p.2.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hzn : z ≠ m := by simpa only [hm] using hp.2.2.1
  obtain ⟨hlocal,hV⟩ := source_small_suzuki_path_center_transitivity h i hb eSuz T₀ hT₀
    p.2.2.1.property p.2.2.2.1.property p.2.2.2.2.1.property
    p.2.2.2.2.2.1.property p.2.2.2.2.2.2.1.property p.2.2.2.2.2.2.2.1.property
    hp.2.2.2.2.1 htype hca hcc D
    (hcore _ (by simp [BasedWalk.vertices]))
    (hcore _ (by simp [BasedWalk.vertices]))
    (hcore _ (by simp [BasedWalk.vertices]))
    (hcore _ (by simp [BasedWalk.vertices]))
  have hlocalC : ∀ v, (graph F).Adj w v → ∃ a ∈ stabilizer F w ⊓ C, a • z = v := by
    intro v hv
    obtain ⟨a,ha,he⟩ := hlocal v hv
    exact ⟨a,⟨ha.1,mem_centralizer_singleton_iff.mpr (ha.2 t ht).symm⟩,he⟩
  have hVW : V F w 1 ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hV ha t ht).symm
  have hxm : (graph F).Adj (p.1 : Vertex F) m := by
    have hh : (graph F).Adj (p.1 : Vertex F) (p.2.1 : Vertex F) := p.2.1.property
    simpa only [hm] using hh
  obtain ⟨R,hR⟩ := source_common_sylow_neighbors h i T₀ hT₀ z hzy.symm
  have htm : t ∈ Q F m := by
    have hh := hcore (p.2.1 : Vertex F) (by simp [BasedWalk.vertices]) ht
    simpa only [hm] using hh
  have hty : t ∈ Q F y := by
    have hh := hcore (p.2.2.1 : Vertex F) (by simp [BasedWalk.vertices]) ht
    simpa only [hy] using hh
  obtain ⟨htrans,hVY,_⟩ := source_small_suzuki_untrapped_centralizer_propagation
    h i hb hxm hzy.symm hzw.symm hwc hzn hc eSuz T₀ R hT₀ hR t htm hty hVW hesc
  obtain ⟨hiW,hiY⟩ := source_small_suzuki_second_indices h i hb eSuz eLin hq T₀ hT₀
    hzy.symm hzw.symm hwc hzn hwy hp.2.2.2.2.1 hbranch
  exact source_small_suzuki_untrapped_terminal h i hb eSuz eLin p hp hm hy
    Tlin hTlin D hD hfix t ht htrans hlocalC hiY hiW hVW hVY

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
