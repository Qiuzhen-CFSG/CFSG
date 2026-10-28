module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearComplementTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSixPathMovement

/-!
# Regularity of the first source six-path

For a--x--m--y--z--w--c with linear endpoints, put
D = V_y intersect Q_x intersect Q_w. The previously proved escape from
Q_a and the action of the full edge complement give the full left root
orbit. To handle the right endpoint, move w to x inside the middle star.
This transports the nonzero branch commutator and the order q^3 of the
span intersection. The second-index exchange then gives
[V_y intersect Q_w : V_y intersect Q_w intersect Q_c] = q.

If D lay in Q_c, the first-index bounds force it to equal V_w intersect
V_y. Both generating span intersections would then lie in Q_x, contrary
to the nonzero image of V_y there. Thus D also escapes Q_c. The same full
edge complement, transferred to w--c, gives the right root orbit. Both
orbits lie in the literal six-path stabilizer, proving its regularity.
The two exact indices and the original completion inclusions are retained.

The supplied complement fixes the literal path, as in the source's choice
of gamma_1. Its choice together with the earlier source markings and
critical data remains to be instantiated in the final assembly. This is
the gamma_1 argument of (12.8); the opposite six-path orientation and
s >= 7, full-kernel equalities, Suzuki selection, binary alternatives,
and the remaining (12.6)--(12.9)/(13.1) and marked premise discharge remain.
No endpoint transitivity, opposite branch commutator, or numerical bound
is added as a hypothesis to this source application.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.8), printed p.185, using (12.3)(a) and (12.6).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual threefold intersection has the full left endpoint orbit. -/
private theorem source_suzuki_six_path_endpoint_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
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
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) i)
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) (!i)))
    (Rz : Sylow 2 (star L S (!i)))
    (hRz : (Rz : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (C : Subgroup (G₀ L S))
    (hC : C ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)
    (hK : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)))
    (hodd : Odd (Nat.card C))
    (hfix : C ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) w) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
    ∃ p : SimpleGraph.BasedWalk (graph F) 6 a,
      p.vertices = [a,x,m,y,z,w,c] ∧ p.Nonbacktracking ∧
      D ≤ pathStabilizer F p ∧
      D.map (G₀ L S).subtype ≤ (pathStabilizer F p).map (G₀ L S).subtype ∧
      (Q F a).relIndex D = Nat.card k ∧
      ((Q F a).map (G₀ L S).subtype).relIndex (D.map (G₀ L S).subtype) = Nat.card k ∧
      ∀ u v, (graph F).Adj a u → (graph F).Adj a v → u ≠ x → v ≠ x →
        ∃ d ∈ D, d • u = v := by
  let F := reducedFamily L S
  let y := base F (!i)
  let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  obtain ⟨p,hpv,hp,hDp,hDo,t,ht,v,hav,_,htv⟩ :=
    source_suzuki_six_path_movement h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
      hyz hwz hwc hzn hcc Rz hRz hbranch
  have hesc : ¬ D ≤ Q F a := by
    intro hh
    have htv' := (source_Z_Q_U (reduced_triple h) a).2 (hh ht) v
      ((mem_ball_one F a v).mpr (.inl hav))
    exact htv htv'
  have hxt : x.type = !i := Bool.eq_not_iff.mpr hxadj.1.symm
  have hat : a.type = i := (Bool.eq_not_iff.mpr hxa.1.symm).trans (by rw [hxt,Bool.not_not])
  have hnQ (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set (G₀ L S)) :=
    (stabilizer F v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F v)))
  have hnorm : C ≤ normalizer (D : Set (G₀ L S)) :=
    (le_inf ((le_inf ((hfix.trans inf_le_left).trans (stabilizer_normalizes_V F y 1))
      ((hC.trans inf_le_left).trans (hnQ x))).trans inf_normalizer_le_normalizer_inf)
      ((hfix.trans inf_le_right).trans (hnQ w))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨hi,htrans⟩ := linear_complement_invariant_transitive_at h i e T hT hat hxa.symm
    D C (inf_le_left.trans inf_le_right) hesc hC hK hodd hnorm
  refine ⟨p,hpv,hp,hDp,hDo,hi,?_,htrans⟩
  rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
  exact hi

/-- Move the nonzero branch across the middle star and exclude containment in the right endpoint core. -/
private theorem six_path_right_escape
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
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
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) i)
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) (!i)))
    (Rz : Sylow 2 (star L S (!i)))
    (hRz : (Rz : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let y := base F (!i)
    ¬ (V F y 1 ⊓ Q F x) ⊓ Q F w ≤ Q F c := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let X := V F x 1
  let Y := V F y 1
  let W := V F w 1
  let D := (Y ⊓ Q F x) ⊓ Q F w
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hVQ := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb
  let : Finite Y := Finite.of_injective (inclusion ((hVQ y).trans (Q_le_stabilizer F y))) (inclusion_injective _)
  have hym : (graph F).Adj y m :=
    ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
  have hwy : w ≠ y := by
    intro he
    have hh := (Z_neighbor_le_V F hwc).trans (hVQ w)
    rw [he] at hh
    exact hcc.2 (hh.trans (hQU y))
  have hcz : c ≠ z := by
    intro he
    exact hcc.2 (he ▸ ((Z_neighbor_le_V F hyz).trans ((hVQ y).trans (hQU y))))
  obtain ⟨g,hg,hgz⟩ := star_locally_transitive h (!i) hyz hym
  have hgy : g • y = y := star_le_stabilizer (!i) hg
  have hmgw : (graph F).Adj m (g • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hwz.symm
    change (graph F).Adj (g • z) (g • w) at hh
    rwa [hgz] at hh
  have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
  obtain ⟨u,hu,huw⟩ := linear_common_sylow_transitive h i e T hT hmgw hxadj hgwne hne
  have huy : u • y = y :=
    (sup_le (Q_le_stabilizer F y)
      (((hQU m).trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right)) hu
  have hty : (u*g) • y = y := by rw [mul_smul,hgy,huy]
  have htw : (u*g) • w = x := by rw [mul_smul,huw]
  have hbranchw : ⁅W ⊓ Q F y,Y⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map (MulAut.conj (u*g)).toMonoidHom) he
    change (⁅V F w 1 ⊓ Q F y,V F y 1⁆ : Subgroup (G₀ L S)).map _ = _ at hh
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hty,htw,Subgroup.map_bot] at hh
    exact hbranch hh
  have hHcard : Nat.card (W ⊓ Y : Subgroup (G₀ L S)) = q^3 := by
    have hh := card_map_of_injective (K := W ⊓ Y) (f := (MulAut.conj (u*g)).toMonoidHom) (MulAut.conj (u*g)).injective
    change Nat.card ((V F w 1 ⊓ V F y 1).map (MulAut.conj (u*g)).toMonoidHom) = _ at hh
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,←V_translate F,←V_translate F,htw,hty] at hh
    exact hh.symm.trans (source_suzuki_intersection_card h i hb hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).1
  have hYcard : Nat.card Y = q^5 :=
    (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  have hYix : (Q F x).relIndex Y = q :=
    (source_suzuki_reverse_first_index h (!i) hb hc hxa hxadj.symm hym hn eSuz
      (by cases i <;> exact e) Ry hRy).1
  have hYiw : (Q F w).relIndex Y = q :=
    (source_suzuki_reverse_first_index h (!i) hb hcc hwc hwz hyz hn eSuz
      (by cases i <;> exact e) Rz hRz).1
  have hstar : W ⊓ Q F y ≤ star L S i :=
    inf_le_right.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _))
  have hmove := source_suzuki_intersection_moves_other_center h (!i) hb hn eSuz Ry
    (by simpa only [Bool.not_not] using hRy) hwz hyz
    (by simpa only [Bool.not_not] using hzn) hbranchw
  obtain ⟨_,hiW',_,_⟩ := source_suzuki_second_index h (!i) hb hwz hyz
    (by simpa only [Bool.not_not] using hzn) hn hfield eSuz Ry Rz
    (by simpa only [Bool.not_not] using hRy) hRz (by cases i <;> exact e) (by simpa only [Bool.not_not] using hstar) hmove
  have hiW : (Q F m).relIndex (W ⊓ Q F y) = q := by
    have he : (W ⊓ Q F m).subgroupOf (W ⊓ Q F y) = (Q F m).subgroupOf (W ⊓ Q F y) := by
      ext d
      exact and_iff_right d.property.1
    change ((Q F m).subgroupOf (W ⊓ Q F y)).index = q
    rw [←he]
    simpa only [Bool.not_not, Subgroup.relIndex] using hiW'
  have hiC : (Q F c).relIndex (Y ⊓ Q F w) = q := by
    have hh : (Q F c).relIndex (Y ⊓ Q F w) = (Q F m).relIndex (W ⊓ Q F y) := by
      simpa only [Bool.not_not] using (source_suzuki_second_index_exchange h (!i) hn eSuz (by cases i <;> exact e) Ry
      (by simpa only [Bool.not_not] using hRy) hyz hwz hwc
      (by simpa only [Bool.not_not] using hzn) hwy hcz)
    exact hh.trans hiW
  have hprod : (X ⊓ Y) ⊔ (W ⊓ Y) = Y := (source_suzuki_six_path_intersection_escape h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
    hyz hwz hwc hzn hcc Rz hRz hbranch).1
  let B := Y ⊓ Q F w
  let J := B ⊓ Q F c
  let H := W ⊓ Y
  have hDB : D ≤ B := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let : Finite B := Finite.of_injective (inclusion (show B ≤ Y from inf_le_left)) (inclusion_injective _)
  let : Finite J := Finite.of_injective (inclusion (show J ≤ B from inf_le_left)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDB) (inclusion_injective _)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hBcard : Nat.card B = q^4 := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) B Y bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hYiw,hYcard] at he
    exact Nat.eq_of_mul_eq_mul_right hqpos (he.trans (by ring))
  have hJcard : Nat.card J = q^3 := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) J B bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hiC,hBcard] at he
    exact Nat.eq_of_mul_eq_mul_right hqpos (he.trans (by ring))
  have hHJ : H ≤ J := le_inf (le_inf inf_le_right (inf_le_left.trans (hVQ w)))
    (inf_le_left.trans (V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hwc))
  have hHJ_eq : H = J := eq_of_le_of_card_ge hHJ (by rw [hJcard,hHcard])
  have hDlow : q^3 ≤ Nat.card D := by
    have hiD : D.relIndex B ≤ q := by
      have he : D = B ⊓ Q F x := by dsimp [D,B]; ac_rfl
      rw [he,inf_relIndex_left]
      exact (relIndex_le_of_le_right (show B ≤ Y from inf_le_left) index_ne_zero_of_finite).trans_eq hYix
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) D B bot_le hDB
    rw [relIndex_bot_left,relIndex_bot_left,hBcard] at he
    have hm := Nat.mul_le_mul_left (Nat.card D) hiD
    rw [he,show q^4 = q^3*q by ring] at hm
    exact (mul_le_mul_iff_left₀ hqpos).mp (by simpa only [mul_comm] using hm)
  change ¬ D ≤ Q F c
  intro hDc
  have hDJ : D ≤ J := le_inf hDB hDc
  have hDH : D = H := (eq_of_le_of_card_ge hDJ (by rw [hJcard]; exact hDlow)).trans hHJ_eq.symm
  have hHQ : H ≤ Q F x := hDH ▸ (show D ≤ Q F x from inf_le_left.trans inf_le_right)
  have hYx : Y ≤ Q F x := by
    rw [←hprod]
    exact sup_le (inf_le_left.trans (hVQ x)) hHQ
  have hh := relIndex_eq_one.mpr hYx
  rw [hYix] at hh
  have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
  omega

/-- The source complement-fixed six-path starting in the linear orbit is regular, with both exact root indices and original inclusions. -/
theorem source_suzuki_six_path_regular
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
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
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) i)
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) (!i)))
    (Rz : Sylow 2 (star L S (!i)))
    (hRz : (Rz : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (C : Subgroup (G₀ L S))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)))
    (hodd : Odd (Nat.card C))
    (hfix : ∀ v ∈ [a,x,base (reducedFamily L S) i,base (reducedFamily L S) (!i),z,w,c],
      C ≤ stabilizer (reducedFamily L S) v) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
    ∃ p : SimpleGraph.BasedWalk (graph F) 6 a,
      p.vertices = [a,x,m,y,z,w,c] ∧ p.Nonbacktracking ∧
      D ≤ pathStabilizer F p ∧
      D.map (G₀ L S).subtype ≤ (pathStabilizer F p).map (G₀ L S).subtype ∧
      (Q F a).relIndex D = Nat.card k ∧ (Q F c).relIndex D = Nat.card k ∧
      ((Q F a).map (G₀ L S).subtype).relIndex (D.map (G₀ L S).subtype) = Nat.card k ∧
      ((Q F c).map (G₀ L S).subtype).relIndex (D.map (G₀ L S).subtype) = Nat.card k ∧
      Theory.GroupAction.CubicTree.Regular (A := G₀ L S) p := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let D := (V F y 1 ⊓ Q F x) ⊓ Q F w
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hC : C ≤ stabilizer F x ⊓ stabilizer F a := le_inf (hfix x (by simp)) (hfix a (by simp))
  obtain ⟨p,hpv,hp,hDp,hDo,hia,hiao,hleft⟩ := source_suzuki_six_path_endpoint_transitive
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor
    hn eSuz hfield Ry hRy hc hxa hmin hnat hyz hwz hwc hzn hcc Rz hRz hbranch
    C hC hK hodd (le_inf (hfix y (by simp [y,F])) (hfix w (by simp)))
  have hesc := six_path_right_escape h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy
    hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
    hyz hwz hwc hzn hcc Rz hRz hbranch
  have hCwc : C ≤ stabilizer F w ⊓ stabilizer F c := le_inf (hfix w (by simp)) (hfix c (by simp))
  have hKc := source_edge_complement_transfer h hxa hwc
    (C.subgroupOf (stabilizer F x ⊓ stabilizer F a)) hK C hCwc hodd
    (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).symm
  have hzt : z.type = i := (Bool.eq_not_iff.mpr hyz.1.symm).trans (by simp)
  have hwt : w.type = !i := Bool.eq_not_iff.mpr (hzt ▸ hwz.1)
  have hct : c.type = i := (Bool.eq_not_iff.mpr hwc.1.symm).trans (by rw [hwt,Bool.not_not])
  have hnQ (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set (G₀ L S)) :=
    (stabilizer F v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F v)))
  have hnorm : C ≤ normalizer (D : Set (G₀ L S)) :=
    (le_inf ((le_inf ((hfix y (by simp [y,F])).trans (stabilizer_normalizes_V F y 1))
      ((hfix x (by simp)).trans (hnQ x))).trans inf_normalizer_le_normalizer_inf)
      ((hfix w (by simp)).trans (hnQ w))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨hic,hright⟩ := linear_complement_invariant_transitive_at h i e T hT hct hwc.symm
    D C inf_le_right hesc hCwc hKc hodd hnorm
  refine ⟨p,hpv,hp,hDp,hDo,hia,hic,hiao,?_,?_⟩
  · exact (relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective).trans hic
  · have hadj : (graph F).Adj m y :=
      ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
    let p₀ : SimpleGraph.BasedWalk (graph F) 6 a :=
      ⟨⟨x,hxa.symm⟩,⟨⟨m,hxadj.symm⟩,⟨⟨y,hadj⟩,⟨⟨z,hyz⟩,⟨⟨w,hwz.symm⟩,⟨⟨c,hwc⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
    have he : p = p₀ := SimpleGraph.BasedWalk.vertices_injective 6 a hpv
    subst p
    constructor
    · intro u v hu hv
      obtain ⟨d,hd,hdv⟩ := hleft u v hu.1 hv.1 hu.2 hv.2
      exact ⟨d,hDp hd,hdv⟩
    · intro u v hu hv
      obtain ⟨d,hd,hdv⟩ := hright u v hu.1 hv.1 hu.2 hv.2
      exact ⟨d,hDp hd,hdv⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
