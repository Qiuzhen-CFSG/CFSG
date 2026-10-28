module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullThirdKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondKernelSpan
public import Theory.GroupTheory.Commutator.NormalSpan
public import Theory.Representation.SL2.NaturalConjugateQuotient

/-!
# The natural quotient of the literal Suzuki second-kernel span

For adjacent m,y and another neighbor x of the linear vertex m, set
C = V_y ∩ Q_x and W = ⟨C^(G_m)⟩. We construct natural SL₂(q) coordinates
on W/G_m^(3), using the proved equality G_m^(3) = V_x ∩ V_y = H.
Every original endpoint element acts by its actual conjugation on W and
by its prescribed quotient matrix on the coordinates.

The elementary quotient Q_y/G_y^(2) and Ω₁(G_y^(2)) = V_y imply
[W,Q_y] ≤ W ∩ V_y = C. Transport gives the corresponding x-bound.
The proved middle-core product then gives [C,Q_m] ≤ H, which propagates
to [W,Q_m] ≤ H. The full stabilizer and starred parabolic give the same
span of C because they have the same neighbor orbit and C = W ∩ V_y.
Thus C/H is a generating Sylow-fixed seed of order q containing all
Sylow displacements. Small-seed recognition constructs the natural
coordinates. In particular W has order q⁵ and equals the elementary
product (V_y ∩ Q_x)(V_x ∩ Q_y).

All earlier source hypotheses of the full-third-kernel theorem remain.
The reciprocal near-intersection commutator is the existing (12.1)(g)
input used to construct the elementary W, not a naturality assumption.
The exhaustive selection, remaining full-kernel series, binary alternatives,
and final Chapter 12/13.1 discharge remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1)(g), (12.9), printed pp.178,188, especially steps (1),(2),(4).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
local instance suzukiSpanNaturalFieldAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem source_suzuki_span_action_data
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
    let m := base F i
    let y := base F (!i)
    let H := V F x 1 ⊓ V F y 1
    let C := V F y 1 ⊓ Q F x
    let W := conjugateSpanBy C (stabilizer F m)
    IsElementaryAbelian 2 W ∧
    W ≤ ballKernel F m 2 ∧
    stabilizer F m ≤ normalizer (W : Set (G₀ L S)) ∧
    stabilizer F m ≤ normalizer (H : Set (G₀ L S)) ∧
    H ≤ C ∧ C ≤ W ∧ W = conjugateSpanBy C (star L S i) ∧ W ≠ C ∧
    ⁅W,Q F m⁆ ≤ H ∧
    ⁅W,(T : Subgroup (star L S i)).map (star L S i).subtype⁆ ≤ C ∧
    ⁅C,(T : Subgroup (star L S i)).map (star L S i).subtype⁆ ≤ H ∧
    H.relIndex C = Nat.card k := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let C := V F y 1 ⊓ Q F x
  let W := conjugateSpanBy C (stabilizer F m)
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  obtain ⟨hWel,hW2,_,hnW,hWY,hHW,hWz,_,_⟩ :=
    source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  change W ⊓ V F y 1 = C at hWY
  change stabilizer F m ≤ normalizer (W : Set (G₀ L S)) at hnW
  let : IsElementaryAbelian 2 W := hWel
  let : Finite W := Finite.of_injective
    (inclusion (hW2.trans (ballKernel_le_stabilizer F m 2))) (inclusion_injective _)
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have ho := source_suzuki_full_kernel_omegas h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hs := source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear
  have hp := source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
  have hQyA : Q F y ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hQmA : Q F m ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hQxA : Q F x ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hAW := (star_le_stabilizer i).trans hnW
  have hAH := (star_le_stabilizer i).trans ht.1
  have hCW : C ≤ W := le_conjugateSpanBy _ _
  have hHC : H ≤ C := le_inf inf_le_right (inf_le_left.trans
    (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x))
  have hZyH : Z F y ≤ H := hzy.trans ht.2.2.2.2.2.2.1
  have hWQy : ⁅W,Q F y⁆ ≤ C := by
    have hder : ⁅Q F y,Q F y⁆ ≤ ballKernel F y 2 := by
      have hplace : Q F y ≤ star L S (!(!i)) := by simpa only [Bool.not_not] using hQyA
      have hnat' : Noncommuting.HasNaturalCenter (star L S (!(!i))) (Z F (base F (!(!i))))
          (Q F (base F (!(!i)))) := by simpa only [Bool.not_not] using hnat
      let : ((ballKernel F y 2).subgroupOf (Q F y)).Normal :=
        normal_subgroupOf_of_le_normalizer
          ((Q_le_stabilizer F y).trans (stabilizer_le_normalizer_ballKernel F y 2))
      let : IsElementaryAbelian 2 (Q F y ⧸ (ballKernel F y 2).subgroupOf (Q F y)) :=
        source_second_kernel_elementary h (!i) hplace hnat' hcommy.le
      have hd := Normal.quotient_commutative_iff_commutator_le.mp
        (inferInstance : IsMulCommutative (Q F y ⧸ (ballKernel F y 2).subgroupOf (Q F y)))
      apply commutator_le.mpr
      intro u hu v hv
      exact hd (commutator_mem_commutator (mem_top (⟨u,hu⟩ : Q F y))
        (mem_top (⟨v,hv⟩ : Q F y)))
    have hw : ⁅W,Q F y⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp (hQyA.trans hAW)
    let : IsElementaryAbelian 2 (⁅W,Q F y⁆ : Subgroup (G₀ L S)) := IsElementaryAbelian.of_le hw
    have hv : ⁅W,Q F y⁆ ≤ V F y 1 := by
      rw [←ho.1,←omegaOneAmbient_eq_self ⁅W,Q F y⁆]
      exact omegaOneAmbient_mono ((commutator_mono (hWz y hadj) le_rfl).trans hder)
    exact (le_inf hw hv).trans hWY.le
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
  have hgm := star_le_stabilizer i hg
  have hWQx : ⁅W,Q F x⁆ ≤ W ⊓ V F x 1 := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hWQy
    have hWg : W.map (MulAut.conj g).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hnW hgm)
    rw [map_commutator,hWg,←Q_translate F,hgy,←hWY,
      map_inf _ _ _ (MulAut.conj g).injective,hWg,←V_translate F,hgy] at hm
    exact hm
  have hCQm : ⁅C,Q F m⁆ ≤ H := by
    have hCQ : Q F m ≤ normalizer (C : Set (G₀ L S)) := by
      rw [←hWY]
      exact (le_inf (hQmA.trans hAW)
        (((hQU m).trans ((ballKernel_one_le_edge F hadj).trans inf_le_right)).trans
          (stabilizer_normalizes_V F y 1))).trans inf_normalizer_le_normalizer_inf
    rw [hp.1,commutator_comm]
    apply commutator_sup_le_of_relative_normal A (Q F x ⊓ Q F m) (Q F y ⊓ Q F m) C H
      hAH (inf_le_left.trans hQxA) (inf_le_left.trans hQyA)
    · rw [commutator_comm]
      exact le_inf ((commutator_mono hCW inf_le_left).trans (hWQx.trans inf_le_right))
        ((le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hCQ)).trans inf_le_left)
    · rw [commutator_comm]
      exact ((commutator_mono inf_le_left inf_le_left).trans hcommy.le).trans hZyH
  have hWQm : ⁅W,Q F m⁆ ≤ H := by
    change ⁅conjugateSpanBy C (stabilizer F m),Q F m⁆ ≤ H
    rw [commutator_conjugateSpanBy_of_normalized_right C (stabilizer F m) (Q F m)
      (hCW.trans (hW2.trans (ballKernel_le_stabilizer F m 2)))
      (CommutingTrivial.stabilizer_normalizes_Q F m)]
    exact conjugateSpanBy_le hCQm ht.1
  have hWT : ⁅W,(T : Subgroup A).map A.subtype⁆ ≤ C := by
    have hnC : Q F y ⊔ Q F m ≤ normalizer (C : Set (G₀ L S)) := by
      rw [←hWY]
      apply (le_inf ((sup_le hQyA hQmA).trans hAW) ?_).trans inf_normalizer_le_normalizer_inf
      exact (sup_le (Q_le_stabilizer F y)
        ((hQU m).trans ((ballKernel_one_le_edge F hadj).trans inf_le_right))).trans
          (stabilizer_normalizes_V F y 1)
    rw [hT,commutator_comm]
    exact commutator_sup_le_of_relative_normal (Q F y ⊔ Q F m) (Q F y) (Q F m) W C
      hnC le_sup_left le_sup_right
      (by rw [commutator_comm]; exact hWQy)
      (by rw [commutator_comm]; exact hWQm.trans hHC)
  have hCT : ⁅C,(T : Subgroup A).map A.subtype⁆ ≤ H := by
    rw [hT,commutator_comm]
    exact commutator_sup_le_of_relative_normal A (Q F y) (Q F m) C H
      hAH hQyA hQmA
      (by rw [commutator_comm]; exact ((commutator_mono inf_le_left le_rfl).trans hcommy.le).trans hZyH)
      (by rw [commutator_comm]; exact hCQm)
  have hspan : W = conjugateSpanBy C A := by
    apply le_antisymm _ (conjugateSpanBy_mono le_rfl (star_le_stabilizer i))
    change conjugateSpanBy C (stabilizer F m) ≤ _
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro g
    have hgy : (graph F).Adj m ((g : G₀ L S) • y) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G₀ L S)).map_adj_iff.mpr hadj
      change (graph F).Adj ((g : G₀ L S) • m) ((g : G₀ L S) • y) at hh
      rwa [show (g : G₀ L S) • m = m from g.property] at hh
    obtain ⟨t,htA,hty⟩ := star_locally_transitive h i hadj hgy
    have heq (u : G₀ L S) (hu : u ∈ stabilizer F m) :
        C.map (MulAut.conj u).toMonoidHom = W ⊓ V F (u • y) 1 := by
      have huW : W.map (MulAut.conj u).toMonoidHom = W :=
        mem_normalizer_iff_map_conj_eq.mp (hnW hu)
      rw [←hWY,map_inf _ _ _ (MulAut.conj u).injective,huW,←V_translate F]
    rw [heq g g.property,←hty,←heq t (star_le_stabilizer i htA)]
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun t : A => C.map (MulAut.conj (t : G₀ L S)).toMonoidHom) ⟨t,htA⟩
  have hneW : W ≠ C := by
    intro he
    have hlo := hs.2.2.2.2.2.2.2.2.2.1
    have hCcard := hs.2.2.2.2.1
    change (2^(2*n+1))^5 ≤ Nat.card W at hlo
    rw [he,hCcard] at hlo
    have hq : 1 < 2^(2*n+1) := by rw [←hfield]; exact Finite.one_lt_card
    have hh := Nat.pow_lt_pow_right hq (by decide : 4 < 5)
    omega
  have hindex : H.relIndex C = Nat.card k := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) H C bot_le hHC
    rw [relIndex_bot_left,relIndex_bot_left,ht.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.1] at hm
    rw [hfield]
    have hpow : (2^(2*n+1))^4 = (2^(2*n+1))^3 * 2^(2*n+1) := by ring
    rw [hpow] at hm
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hm
  exact ⟨hWel,hW2,hnW,ht.1,hHC,hCW,hspan,hneW,hWQm,hWT,hCT,hindex⟩


/-- DGS85 p.188(4): the literal W/G_m^(3) has natural coordinates for the
original marked SL₂(k) action; in particular |W| = q⁵. -/
theorem source_suzuki_span_natural
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
    let m := base F i
    let y := base F (!i)
    let C := V F y 1 ⊓ Q F x
    let W := conjugateSpanBy C (stabilizer F m)
    ∃ hWel : IsElementaryAbelian 2 W,
    ∃ hAW : star L S i ≤ normalizer (W : Set (G₀ L S)),
      let := hWel
      let : ((ballKernel F m 3).subgroupOf W).Normal := normal_of_isMulCommutative _
      W ≤ ballKernel F m 2 ∧ ballKernel F m 3 ≤ W ∧
      Nat.card W = Nat.card k ^ 5 ∧
      W = C ⊔ (V F x 1 ⊓ Q F y) ∧
      ballKernel F m 3 = V F x 1 ⊓ V F y 1 ∧
      Nat.card (W ⧸ (ballKernel F m 3).subgroupOf W) = Nat.card k ^ 2 ∧
      ∃ E : Additive (W ⧸ (ballKernel F m 3).subgroupOf W) ≃ₗ[ZMod 2] (Fin 2 → k),
        ∀ u : L (if i then 1 else 0), ∀ w : W,
          E (Additive.ofMul (QuotientGroup.mk
            ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * w *
                (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hAW
                (originalActor (L := L) (S := S) i u).property) w).mp w.property⟩)) =
            Matrix.mulVec (e (QuotientGroup.mk u)).val
              (E (Additive.ofMul (QuotientGroup.mk w))) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let C := V F y 1 ⊓ Q F x
  let W := conjugateSpanBy C (stabilizer F m)
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  obtain ⟨hWel,hW2,hnW,hnH,hHC,hCW,hspan,hneW,hcore,hmove,hfix,hindex⟩ :=
    source_suzuki_span_action_data h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy
      hc hxa hmin hnat hbranch hnear
  let : IsElementaryAbelian 2 W := hWel
  let : Finite W := Finite.of_injective
    (inclusion (hW2.trans (ballKernel_le_stabilizer F m 2))) (inclusion_injective _)
  have hAW := (star_le_stabilizer i).trans hnW
  have hAH := (star_le_stabilizer i).trans hnH
  let eA := (originalQuotient h i).symm.trans e
  obtain ⟨horder,E,hE⟩ := Representation.SL2.natural_conjugate_quotient
    A W H C hAW hAH hHC hCW hspan hneW
    (by rw [star_core h i]; exact hcore) T eA hmove hfix hindex.le
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hN := source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hHW : H ≤ W := hHC.trans hCW
  let : (H.subgroupOf W).Normal := normal_of_isMulCommutative _
  have hWcard : Nat.card W = Nat.card k ^ 5 := by
    have hh := (H.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hHW).toEquiv,index_eq_card,horder,
      ht.2.2.2.2.2.2.2.2.1,←hfield] at hh
    calc Nat.card W = Nat.card k ^ 3 * Nat.card k ^ 2 := hh.symm
         _ = Nat.card k ^ 5 := by ring
  have hs := source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear
  have hprod : W = C ⊔ (V F x 1 ⊓ Q F y) := by
    apply (eq_of_le_of_card_ge hs.2.2.2.2.2.2.2.2.1 ?_).symm
    rw [hWcard,hfield,hs.2.2.2.2.2.2.2.1]
  refine ⟨hWel,hAW,hW2,hN.1.le.trans hHW,hWcard,hprod,hN.1,?_⟩
  change Nat.card (W ⧸ (ballKernel F m 3).subgroupOf W) = Nat.card k ^ 2 ∧ _
  rw [hN.1]
  refine ⟨horder,E,?_⟩
  intro u w
  have hqu : eA (QuotientGroup.mk (originalActor (L := L) (S := S) i u)) =
      e (QuotientGroup.mk u) := by
    change e ((originalQuotient h i).symm
      (QuotientGroup.mk (originalActor (L := L) (S := S) i u))) = _
    exact congrArg e
      ((congrArg (originalQuotient h i).symm (originalQuotient_mk h i u).symm).trans
        ((originalQuotient h i).symm_apply_apply (QuotientGroup.mk u)))
  have he := hE (originalActor (L := L) (S := S) i u) w
  rwa [hqu] at he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
