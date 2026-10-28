module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTrappedCentralizer
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiUntrappedExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiUntrappedExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSylowNeighbors
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NinePathUntrappedCentralizer

/-!
# Odd order of the nonbinary source nine-path stabilizer

In the trapped case of DGS (12.7), put A = C_(V_x)(t) and
D = A intersect Q_w. The previous trapped-centralizer calculation proves
A = V_x intersect Q_y and D is not contained in Q_c. The centralizer of
the path two-element acts transitively at w, so it conjugates D to a
two-subgroup E of Q_w that escapes Q_z.

The incoming intersection A has full linear root image at z. An element
of E must move y, by the proved two-neighbor core theorem. Conjugating A
by that element gives two distinct full root images, whose join acts
transitively at z. Both local actions lie in C(t), so faithful graph
normalizer propagation (3.2)(c) forces t = 1. The already proved
untrapped case completes the element argument. Apply it to the literal
Sylow two-subgroup of the path stabilizer to obtain odd order, also
after the original completion inclusion.

All transitivity, escape, index and center-movement premises used in this
argument are discharged here or by the preceding source lemmas. In
particular the incoming nonzero commutator is transported from the same
nonzero branch on the path; it is not an additional source assumption.
The retained original quotient markings, common Sylows, natural-center
and commutator data, and critical-pair placements are genuine earlier
source inputs. The theorem concerns the normalized nonbinary nine-path
with those inputs. Exhaustive Suzuki selection, binary cases, global
source premise discharge, full kernel equalities and (12.8)--(12.9)/(13.1)
remain with the source-family assembly.

Implementation imports reuse the preceding private neighborhood and
remote-center arguments without widening their public boundaries.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7), printed pp.184--185, using (3.2)(c), (12.3)(a), and (12.6).
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem incoming_second_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hq : Nat.card k = 2^(2*n+1))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (R : Sylow 2 (star L S (!i)))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {x z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) :
    (Q (reducedFamily L S) z).relIndex
      (V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F (!i)
  let y := base F i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hym : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgz⟩ := star_locally_transitive h i hyz hym
  have hgy : g • y = y := star_le_stabilizer i hg
  have hgm : g • m ≠ m := fun he => hzn ((MulAction.injective g) (hgz.trans he.symm))
  have hadj {u v : Vertex F} (huv : (graph F).Adj u v) :
      (graph F).Adj (g • u) (g • v) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr huv
  have hygm : (graph F).Adj y (g • m) := by simpa only [hgy] using hadj hym
  obtain ⟨R',hR'⟩ := source_common_sylow_neighbors h i T hT _ hygm
  have hbranch' : ⁅V F (g • x) 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    have hh := (map_eq_bot_iff_of_injective
      (⁅V F x 1 ⊓ Q F y,V F y 1⁆ : Subgroup (G₀ L S)) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).not.mpr hbranch
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hgy] at hh
  have hmove := source_suzuki_intersection_moves_other_center h i hb hn eSuz T hT
    (hadj hxm) hygm hgm hbranch'
  have hstar : V F (g • x) 1 ⊓ Q F y ≤ star L S (!i) :=
    inf_le_right.trans ((le_sup_left.trans hR.ge).trans (map_subtype_le _))
  obtain ⟨_,hi,_,_⟩ := source_suzuki_second_index h i hb (hadj hxm) hygm hgm
    hn hq eSuz T R' hT hR' eLin hstar hmove
  have hi' : (Q F m).relIndex (V F (g • x) 1 ⊓ Q F y) = Nat.card k := by
    have he : (V F (g • x) 1 ⊓ Q F m).subgroupOf (V F (g • x) 1 ⊓ Q F y) =
        (Q F m).subgroupOf (V F (g • x) 1 ⊓ Q F y) := by
      ext u
      exact and_iff_right u.property.1
    change ((Q F m).subgroupOf (V F (g • x) 1 ⊓ Q F y)).index = Nat.card k
    rw [←he]
    exact hi.trans hq.symm
  have he := relIndex_map_map_of_injective (Q F z) (V F x 1 ⊓ Q F y)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ←V_translate F,←Q_translate F,←Q_translate F,hgy,hgz] at he
  exact he.symm.trans hi'

/-- A full linear root image and an escaping opposite two-subgroup are
transitive on the actual neighborhood. -/
private theorem linear_full_index_escape_transitive_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {n : ℕ}
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {z y w : Vertex (reducedFamily L S)} (hz : z.type = i)
    (hzy : (graph (reducedFamily L S)).Adj z y)
    (hzw : (graph (reducedFamily L S)).Adj z w) (hyw : y ≠ w)
    (A D : Subgroup (G₀ L S)) (hA : A ≤ Q (reducedFamily L S) y)
    (hiA : (Q (reducedFamily L S) z).relIndex A = Nat.card k)
    (hD : D ≤ Q (reducedFamily L S) w) (hp : IsPGroup 2 D)
    (hesc : ¬ D ≤ Q (reducedFamily L S) z) :
    ∀ v, (graph (reducedFamily L S)).Adj z v → ∃ g ∈ A ⊔ D, g • y = v := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hDz : D ≤ stabilizer F z := hD.trans
    (((source_Z_Q_U (reduced_triple h) w).2.trans (ballKernel_one_le_edge F hzw.symm)).trans inf_le_right)
  have hDy : ¬ D ≤ stabilizer F y := by
    intro hfix
    exact hesc (source_mixed_two_neighbor_core h i e eSuz hzy hzw hyw D hp
      hDz hfix (hD.trans (Q_le_stabilizer F w)))
  obtain ⟨d,hd,hdy⟩ := SetLike.not_le_iff_exists.mp hDy
  have hdz : d • z = z := hDz hd
  have hdy' : d • y ≠ y := hdy
  let c := (MulAut.conj d).toMonoidHom
  have hAc : A.map c ≤ Q F (d • y) := by
    have hh := map_mono (f := c) hA
    change A.map c ≤ (Q F y).map (MulAut.conj d).toMonoidHom at hh
    rwa [←Q_translate F] at hh
  have hic : (Q F z).relIndex (A.map c) = Nat.card k := by
    have hh := relIndex_map_map_of_injective (Q F z) A (f := c) (MulAut.conj d).injective
    change ((Q F z).map (MulAut.conj d).toMonoidHom).relIndex (A.map c) = _ at hh
    rw [←Q_translate F,hdz] at hh
    exact hh.trans hiA
  have hadj : (graph F).Adj z (d • y) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F d).map_adj_iff.mpr hzy
    change (graph F).Adj (d • z) (d • y) at hh
    rwa [hdz] at hh
  have hAcJ : A.map c ≤ A ⊔ D := by
    rintro u ⟨a,ha,rfl⟩
    exact (A ⊔ D).mul_mem ((A ⊔ D).mul_mem ((show D ≤ A ⊔ D from le_sup_right) hd) ((show A ≤ A ⊔ D from le_sup_left) ha))
      ((A ⊔ D).inv_mem ((show D ≤ A ⊔ D from le_sup_right) hd))
  intro v hv
  obtain ⟨g,hg,he⟩ := linear_full_index_pair_transitive_at h i e T hT hz hzy hadj hdy'
    A (A.map c) hA hAc hiA hic v hv
  exact ⟨g,(sup_le le_sup_left hAcJ) hg,he⟩

set_option backward.isDefEq.respectTransparency false in
/-- Both centralizer cases kill every element of the actual nine-path
two-subgroup, with the original source markings and earlier inputs. -/
theorem source_suzuki_nine_path_element_eq_one
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {σ : Vertex (reducedFamily L S)}
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1, Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S))⁆ ≤ Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)))
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
    (hc : IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hc6 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) (!i)))
    (hc2 : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc8 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (U : Subgroup (G₀ L S)) (hU : IsPGroup 2 U)
    (hfix : U ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ U)
    (hbranchw : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) : t = 1 := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let x : Vertex F := p.1
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.1
  let C := centralizer ({t} : Set (G₀ L S))
  let A := V F x 1 ⊓ C
  let D := A ⊓ Q F w
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hcore := source_mixed_path_two_subgroup_core h i e eSuz p hp U hU hfix
  have htype : w.type = !i := by
    have h3 : (p.2.2.1 : Vertex F).type = !i := congrArg Subgroup.CosetGeometry.Vertex.type hy
    have h4 : (!i) ≠ z.type := h3 ▸ p.2.2.2.1.property.1
    exact (Bool.eq_not_iff.mpr p.2.2.2.2.1.property.1.symm).trans (Bool.not_eq_iff.mpr h4.symm)
  have hzt : z.type = i := by
    have hh := Bool.eq_not_iff.mpr (htype ▸ p.2.2.2.2.1.property.1)
    simpa only [Bool.not_not] using hh
  have hzyEdge : (graph F).Adj z y := by
    have hh : (graph F).Adj z (p.2.2.1 : Vertex F) := p.2.2.2.1.property.symm
    simpa only [hy] using hh
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwc : (graph F).Adj w c := p.2.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hzn : z ≠ m := by simpa only [hm] using hp.2.2.1
  have hxm : (graph F).Adj x m := by
    have hh : (graph F).Adj x (p.2.1 : Vertex F) := p.2.1.property
    simpa only [hm] using hh
  have hxne : x ≠ y := by
    have hh := hp.2.1
    simpa only [hy] using hh.symm
  have htx : t ∈ Q F x := hcore _ (by simp [BasedWalk.vertices,x]) ht
  have htz : t ∈ Q F z := hcore _ (by simp [BasedWalk.vertices,z]) ht
  have htw : t ∈ Q F w := hcore _ (by simp [BasedWalk.vertices,w]) ht
  have hbranchx : ⁅V F x 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    have hym : (graph F).Adj y m :=
      ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive h (!i) hzyEdge.symm hym
    have hgy : g • y = y := star_le_stabilizer (!i) hg
    have hmgw : (graph F).Adj m (g • w) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hzw
      change (graph F).Adj (g • z) (g • w) at hh
      rwa [hgz] at hh
    have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
    obtain ⟨u,hu,huw⟩ := linear_common_sylow_transitive h i e T hT
      hmgw hxm.symm hgwne hxne
    have huy : u • y = y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (reduced_triple h) m).2.trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right)) hu
    have hty : (u*g) • y = y := by rw [mul_smul,hgy,huy]
    have htw : (u*g) • w = x := by rw [mul_smul,huw]
    have hh := (map_eq_bot_iff_of_injective
      (⁅V F w 1 ⊓ Q F y,V F y 1⁆ : Subgroup (G₀ L S))
      (f := (MulAut.conj (u*g)).toMonoidHom) (MulAut.conj (u*g)).injective).not.mpr hbranchw
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hty,htw] at hh
  by_cases htrap : A ≤ Q F y
  · obtain ⟨Rz,hRz⟩ := source_common_sylow_neighbors h (!i) Ry
      (by simpa only [Bool.not_not] using hRy) z hzyEdge.symm
    obtain ⟨hA,hescape,_,_⟩ := source_suzuki_trapped_centralizer_escape
      h i hb hxm.symm hxne T R hT hR e hz hcard hcardy hzx hzy
      hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc
      p.1.property.symm hmin hnat hzyEdge.symm hzw.symm hwc hzn hc6 Rz hRz t htx htrap
    have hiA : (Q F z).relIndex A = Nat.card k := by
      rw [show A = V F x 1 ⊓ Q F y from hA]
      exact incoming_second_index h (!i) hb hn eSuz (by cases i <;> exact e) hfield
        Ry (by simpa only [Bool.not_not] using hRy) (by cases i <;> exact T)
        (by cases i <;> exact hT) (by simpa only [Bool.not_not] using hxm)
        hzyEdge.symm (by simpa only [Bool.not_not] using hzn) hbranchx
    have hlocal := interior_center_transitivity h (!i) hb hn eSuz (by cases i <;> exact e)
      Ry (by simpa only [Bool.not_not] using hRy)
      p.2.2.1.property p.2.2.2.1.property p.2.2.2.2.1.property
      p.2.2.2.2.2.1.property p.2.2.2.2.2.2.1.property p.2.2.2.2.2.2.2.1.property
      hp.2.2.2.2.1 htype hc2 hc8 U
      (hcore _ (by simp [BasedWalk.vertices]))
      (hcore _ (by simp [BasedWalk.vertices]))
      (hcore _ (by simp [BasedWalk.vertices]))
      (hcore _ (by simp [BasedWalk.vertices]))
    have hlocalC : ∀ v, (graph F).Adj w v → ∃ a ∈ stabilizer F w ⊓ C, a • z = v := by
      intro v hv
      obtain ⟨a,ha,he⟩ := hlocal v hv
      exact ⟨a,⟨ha.1,mem_centralizer_singleton_iff.mpr (ha.2 t ht).symm⟩,he⟩
    obtain ⟨a,ha,hac⟩ := hlocalC c hwc
    let g := a⁻¹
    let f := (MulAut.conj g).toMonoidHom
    let E := D.map f
    have hgw : g • w = w := (stabilizer F w).inv_mem ha.1
    have hgc : g • c = z := inv_smul_eq_iff.mpr hac.symm
    have hEQ : E ≤ Q F w := by
      have hh := map_mono (f := f) (show D ≤ Q F w from inf_le_right)
      change E ≤ (Q F w).map (MulAut.conj g).toMonoidHom at hh
      rwa [←Q_translate F,hgw] at hh
    have hEesc : ¬ E ≤ Q F z := by
      intro hE
      apply hescape
      intro d hd
      have hh := hE (mem_map_of_mem f hd)
      rw [←hgc,Q_translate F] at hh
      obtain ⟨u,hu,he⟩ := hh
      exact (MulAut.conj g).injective he ▸ hu
    have hEp : IsPGroup 2 E :=
      ((isPGroup_pCoreIn 2 (stabilizer F w)).to_le (show D ≤ Q F w from inf_le_right)).map f
    have hEC : E ≤ C := by
      have hh := map_mono (f := f) (show D ≤ C from inf_le_left.trans inf_le_right)
      have he : C.map (MulAut.conj g).toMonoidHom = C :=
        mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer (C.inv_mem ha.2))
      exact hh.trans he.le
    have hlinear := linear_full_index_escape_transitive_at h i e eSuz T hT hzt
      hzyEdge hzw hwy.symm A E htrap hiA hEQ hEp hEesc
    have hCN : C ≤ normalizer (zpowers t : Set (G₀ L S)) := by
      rw [zpowers_eq_closure]
      exact (show C ≤ centralizer (closure ({t} : Set (G₀ L S)) : Set (G₀ L S)) by
        rw [centralizer_closure]).trans (Subgroup.centralizer_le_normalizer _)
    have hlinearC : ∀ v, (graph F).Adj z v → ∃ g ∈ C, g • w = v := by
      obtain ⟨b,hb,hby⟩ := hlinear w hzw
      intro v hv
      obtain ⟨d,hd,hdy⟩ := hlinear v hv
      have hAC : A ⊔ E ≤ C := sup_le inf_le_right hEC
      refine ⟨d*b⁻¹,C.mul_mem (hAC hd) (C.inv_mem (hAC hb)),?_⟩
      rw [mul_smul,inv_smul_eq_iff.mpr hby.symm,hdy]
    have hbot := source_normalized_edge_eq_bot (reduced_triple h) hzw (zpowers t)
      (zpowers_le.mpr ⟨Q_le_stabilizer F z htz,Q_le_stabilizer F w htw⟩)
      (fun v hv => by obtain ⟨g,hg,he⟩ := hlinearC v hv; exact ⟨g,hCN hg,he⟩)
      (fun v hv => by obtain ⟨g,hg,he⟩ := hlocalC v hv; exact ⟨g,hCN hg.2,he⟩)
    exact mem_bot.mp (hbot ▸ mem_zpowers t)
  · exact source_suzuki_nine_path_untrapped_eq_one h (!i) hb hn eSuz
      (by cases i <;> exact e) Ry (by simpa only [Bool.not_not] using hRy) hfield
      (by cases i <;> exact T) (by cases i <;> exact hT) p hp
      (by simpa only [Bool.not_not] using hm) hy hc2 hc8 hc6 U hU hfix t ht htrap hbranchw

set_option backward.isDefEq.respectTransparency false in
/-- The literal normalized nonbinary nine-path stabilizer has odd order,
including its image in the original completion. -/
theorem source_suzuki_nine_path_odd
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {σ : Vertex (reducedFamily L S)}
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1, Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S))⁆ ≤ Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)))
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
    (hc : IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hc6 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) (!i)))
    (hc2 : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc8 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hbranchw : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    Odd (Nat.card (pathStabilizer F p)) ∧
      Odd (Nat.card ((pathStabilizer F p).map (G₀ L S).subtype)) := by
  let F := reducedFamily L S
  let P := pathStabilizer F p
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  let J : Sylow 2 P := Classical.choice inferInstance
  let U := (J : Subgroup P).map P.subtype
  have hU : U = ⊥ := by
    apply eq_bot_iff.mpr
    intro t ht
    exact mem_bot.mpr (source_suzuki_nine_path_element_eq_one h i hb p hp hm hy T R hT hR e
      hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc
      hmin hnat hc6 hc2 hc8 U (J.isPGroup'.map P.subtype) (map_subtype_le _) t ht hbranchw)
  have hJ : (J : Subgroup P) = ⊥ := (map_eq_bot_iff_of_injective
    (J : Subgroup P) P.subtype_injective).mp hU
  have hindex : (J : Subgroup P).index = Nat.card P := by
    rw [hJ,index_bot]
  have hodd : Odd (Nat.card P) := by
    rw [←Nat.not_even_iff_odd,even_iff_two_dvd,←hindex]
    exact J.not_dvd_index
  refine ⟨hodd,?_⟩
  rw [card_map_of_injective (G₀ L S).subtype_injective]
  exact hodd

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
