module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreSpanSupplement
public import Theory.GroupTheory.Commutator.CentralModuloSupplement

/-!
# The Suzuki span inside the actual derived core

Let Y = V_y and K = G_y^(2), with y the Suzuki vertex adjacent to the
linear vertex m. We prove Y ≤ [Q_y,Q_y]. If the invariant intersection
Y ∩ [Q_y,Q_y] were contained in Z_y, the elementary middle span W would
satisfy [W,Q_y] ≤ Z_y. Neighbor transport, the middle-core product and
three-core generation would then make its defining seed invariant under
the middle star. Neighbor transitivity extends this invariance to the full
stabilizer, collapsing W to that seed and contradicting the nonzero branch
commutator. Irreducibility of the literal Y/Z_y action gives the inclusion.

Combining this with the already proved Suzuki-star span supplement gives
[Q_y,Q_y] = Y ∨ [K,K], also under the original completion inclusion. The
remaining containment [K,K] ≤ Y is not asserted. The source markings,
natural center, common Sylows and reciprocal commutator inputs remain
explicit, as do all earlier-source obligations in the Chapter 12 assembly.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (12.9), printed p.188, especially the action preceding (3).
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups commutatorElement
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The irreducible center layer and actual neighboring actions force
V_y into the derived subgroup of the full Suzuki core. -/
theorem source_suzuki_core_derived_contains_span
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let y := base F (!i)
    V F y 1 ≤ ⁅Q F y,Q F y⁆ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let B := star L S (!i)
  let Y := V F y 1
  let C := Y ⊓ Q F x
  let W := conjugateSpanBy C (stabilizer F m)
  let Zm := Z F m
  let Zy := Z F y
  let D := Y ⊓ ⁅Q F y,Q F y⁆
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hYQ : Y ≤ Q F y := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  let : IsElementaryAbelian 2 Y := V_elementary F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb y
  let : (Zy.subgroupOf Y).Normal := normal_of_isMulCommutative _
  have hZY : Zy ≤ Y := Z_le_V F y 1
  have hZD : Zy ≤ D := le_inf hZY (hcommy.ge.trans (commutator_mono hYQ le_rfl))
  have hBY : B ≤ normalizer (Y : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (stabilizer_normalizes_V F y 1)
  have hBQ : B ≤ normalizer (Q F y : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (CommutingTrivial.stabilizer_normalizes_Q F y)
  have hBD : B ≤ normalizer (D : Set (G₀ L S)) := by
    intro u hu
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Y ⊓ ⁅Q F y,Q F y⁆).map _ = _
    rw [map_inf _ _ _ (MulAut.conj u).injective,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hBY hu),
      mem_normalizer_iff_map_conj_eq.mp (hBQ hu)]
  have hspan := source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  obtain ⟨hWel,_,_,hnW,hWY,_,hWQ,_,_⟩ := hspan
  change stabilizer F m ≤ normalizer (W : Set (G₀ L S)) at hnW
  change W ⊓ Y = C at hWY
  let : IsElementaryAbelian 2 W := hWel
  have hAW : A ≤ normalizer (W : Set (G₀ L S)) := (star_le_stabilizer i).trans hnW
  have hQyA : Q F y ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hQxA : Q F x ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hQmA : Q F m ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hAZ : A ≤ normalizer (Zm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_normalizes_Z F m)
  have hp := source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hZC : Zm ≤ C := le_inf (ht.2.2.2.2.2.2.1.trans inf_le_right)
    (ht.2.2.2.2.2.2.1.trans (inf_le_left.trans
      (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x)))
  have hs := source_suzuki_core_span_supplement h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hmove : ¬ D ≤ Zy := by
    intro hDZ
    have hWy : ⁅W,Q F y⁆ ≤ Zy := (le_inf (hs.2.1.trans inf_le_left)
      (commutator_mono (hWQ y hadj) le_rfl)).trans hDZ
    obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
    have hWx : ⁅W,Q F x⁆ ≤ Z F x := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hWy
      have hWg : W.map (MulAut.conj g).toMonoidHom = W :=
        mem_normalizer_iff_map_conj_eq.mp (hAW hg)
      change (⁅W,Q F y⁆).map _ ≤ (Z F y).map _ at hh
      rwa [map_commutator,hWg,←Q_translate F,←Z_translate F,hgy] at hh
    have hWm : ⁅W,Q F m⁆ ≤ Zm := by
      rw [hp.1,commutator_comm]
      exact commutator_sup_le_of_relative_normal A (Q F x ⊓ Q F m) (Q F y ⊓ Q F m) W Zm
        hAZ (inf_le_left.trans hQxA) (inf_le_left.trans hQyA)
        (by rw [commutator_comm]; exact (commutator_mono le_rfl inf_le_left).trans (hWx.trans hzx))
        (by rw [commutator_comm]; exact (commutator_mono le_rfl inf_le_left).trans (hWy.trans hzy))
    have hWA : ⁅W,A⁆ ≤ Zm := by
      change ⁅W,star L S i⁆ ≤ Zm
      rw [star_three_core_generation h i hxadj hne T R hT hR,commutator_comm]
      exact commutator_sup_le_of_relative_normal A (Q F y ⊔ Q F x) (Q F m) W Zm hAZ
        (sup_le hQyA hQxA) hQmA
        (commutator_sup_le_of_relative_normal A (Q F y) (Q F x) W Zm hAZ hQyA hQxA
          (by rw [commutator_comm]; exact hWy.trans hzy)
          (by rw [commutator_comm]; exact hWx.trans hzx))
        (by rw [commutator_comm]; exact hWm)
    have hAC : A ≤ normalizer (C : Set (G₀ L S)) :=
      le_normalizer_iff_commutator_le_left.mpr
        ((commutator_mono (le_conjugateSpanBy C (stabilizer F m)) le_rfl).trans (hWA.trans hZC))
    have hstabC : stabilizer F m ≤ normalizer (C : Set (G₀ L S)) := by
      intro g hg
      have hgy : (graph F).Adj m (g • y) := by
        have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hadj
        change (graph F).Adj (g • m) (g • y) at hh
        rwa [show g • m = m from hg] at hh
      obtain ⟨t,htA,hty⟩ := star_locally_transitive h i hadj hgy
      have heq (u : G₀ L S) (hu : u ∈ stabilizer F m) :
          C.map (MulAut.conj u).toMonoidHom = W ⊓ V F (u • y) 1 := by
        have hWu : W.map (MulAut.conj u).toMonoidHom = W :=
          mem_normalizer_iff_map_conj_eq.mp (hnW hu)
        change C.map (MulAut.conj u).toMonoidHom = W ⊓ (V F (u • y) 1)
        rw [←hWY,map_inf _ _ _ (MulAut.conj u).injective,hWu]
        change W ⊓ (V F y 1).map (MulAut.conj u).toMonoidHom = _
        rw [←V_translate F]
      apply mem_normalizer_iff_map_conj_eq.mpr
      change C.map (MulAut.conj g).toMonoidHom = C
      rw [heq g hg,←hty,←heq t (star_le_stabilizer i htA)]
      exact mem_normalizer_iff_map_conj_eq.mp (hAC htA)
    have hWC : W = C := le_antisymm (conjugateSpanBy_le le_rfl hstabC)
      (le_conjugateSpanBy C (stabilizer F m))
    have hB := (source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear).2.2.2.1.ge
    have hBY : V F x 1 ⊓ Q F y ≤ Y := (hB.trans inf_le_left).trans (hWC.le.trans inf_le_left)
    exact hbranch (bot_unique ((commutator_mono hBY le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer Y)).le))
  obtain ⟨_,_,_,ρ,_,hirr,_,hρ⟩ := source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  let := hirr
  have hgen : D ⊔ Zy = Y := (inf_or_sup_of_irreducible_quotient Y Zy D hZY inf_le_left
    (fun u => (originalActor (L := L) (S := S) (!i) u : G₀ L S))
    (QuotientGroup.mk' (pCore 2 (L (if !i then 1 else 0))))
    (QuotientGroup.mk'_surjective _)
    (fun u => hBY (originalActor (L := L) (S := S) (!i) u).property)
    (fun u => hBD (originalActor (L := L) (S := S) (!i) u).property) ρ hρ).resolve_left hmove
  exact hgen.ge.trans (sup_le inf_le_right (hZD.trans inf_le_right))

/-- The literal derived-core calculation, with its remaining full-kernel
factor and both original completion images retained. -/
theorem source_suzuki_core_derived_reduction
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let y := base F (!i)
    let K := ballKernel F y 2
    let Y := V F y 1
    ⁅Q F y,Q F y⁆ = Y ⊔ ⁅K,K⁆ ∧
    ⁅(Q F y).map (G₀ L S).subtype,(Q F y).map (G₀ L S).subtype⁆ =
      Y.map (G₀ L S).subtype ⊔ ⁅K.map (G₀ L S).subtype,K.map (G₀ L S).subtype⁆ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let K := ballKernel F y 2
  let Y := V F y 1
  let W := conjugateSpanBy (Y ⊓ Q F x) (stabilizer F m)
  let J := conjugateSpanBy W (star L S (!i))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hs := source_suzuki_core_span_supplement h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hY := source_suzuki_core_derived_contains_span h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have heq : ⁅Q F y,Q F y⁆ = Y ⊔ ⁅K,K⁆ :=
    commutator_eq_sup_of_central_modulo_supplement (Q F y) J K Y hs.2.2.2.1
      ((Q_le_stabilizer F y).trans (stabilizer_le_normalizer_ballKernel F y 2))
      ((Q_le_stabilizer F y).trans (stabilizer_normalizes_V F y 1)) hs.2.2.1 hY
  refine ⟨heq,?_⟩
  have hh := congrArg (Subgroup.map (G₀ L S).subtype) heq
  rwa [map_commutator,Subgroup.map_sup,map_commutator] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
