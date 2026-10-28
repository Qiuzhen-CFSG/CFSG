module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTorusCentralizerLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanNatural
-- This continuation of the same source proof reuses the internal action data;
-- its public statements contain only the original groups and kernels.
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanNatural
/-!
# The selected torus centralizer in the literal span W

The natural action on W/H has no nonzero fixed vector for any nontrivial
odd subgroup D of the starred parabolic: its intersection with the
two-core is trivial, so it contains an actor with nonidentity natural
image. Consequently C_W(D) = C_H(D), of order q by the preceding
third-kernel calculation.

This module intentionally continues the internal proof in SuzukiSpanNatural:
its private action data feeds the existing natural-quotient theorem, giving
the full starred action without repeating the kernel or module recognition
proof. No private declaration occurs in the new public statements.

The final source consumer constructs the original full-edge complement
fixing the displayed second neighbor, restricts it to the starred
parabolic, and preserves the literal completion inclusion on all
centralizers and commutators. No extra complement or torus-selection
premise is introduced.

The remaining source step is C_(Q_m)(D) ≤ H: the present calculations
place that centralizer inside C_(Q_m)(H) and determine its intersection
with W, but do not exclude fixed elements outside W. Irreducibility of
C/W, the full second-kernel identity and final Chapter 12/13.1 discharge
remain outstanding under the retained earlier-source hypotheses.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188--189, natural layers (4)--(5) and the
nonbinary torus-centralizer argument.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- An odd starred actor has the same fixed subgroup in W and the full third kernel. -/
theorem source_suzuki_odd_span_centralizer
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
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (D : Subgroup (G₀ L S)) (hDA : D ≤ star L S i)
    (hodd : Odd (Nat.card D)) (hneD : D ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let H := ballKernel F m 3
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    W ⊓ centralizer (D : Set (G₀ L S)) = H ⊓ centralizer (D : Set (G₀ L S)) ∧
      Nat.card (W ⊓ centralizer (D : Set (G₀ L S)) : Subgroup (G₀ L S)) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let Qm := Q F m
  let H := V F x 1 ⊓ V F y 1
  let B := V F y 1 ⊓ Q F x
  let W := conjugateSpanBy B (stabilizer F m)
  let J := centralizer (D : Set (G₀ L S))
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  let : Finite Qm := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have hcDQ : Nat.Coprime (Nat.card D) (Nat.card Qm) := by
    have hp : IsPGroup 2 Qm := isPGroup_pCoreIn 2 _
    obtain ⟨r,hr⟩ := hp.exists_card_eq
    rw [hr]
    exact (Nat.coprime_two_right.mpr hodd).pow_right r
  have hdq : Disjoint D Qm := disjoint_of_coprime_natCard hcDQ
  obtain ⟨t,ht,ht1⟩ : ∃ t ∈ D, t ≠ 1 := by
    by_contra! hh
    exact hneD (eq_bot_iff.mpr fun t ht => mem_bot.mpr (hh t ht))
  let tA : A := ⟨t,hDA ht⟩
  have hto : Odd (orderOf tA) := by
    rw [←Subgroup.orderOf_coe]
    exact hodd.of_dvd_nat (D.orderOf_dvd_natCard ht)
  have htQ : t ∉ Qm := fun htq => ht1 (mem_bot.mp (hdq.eq_bot ▸ (show t ∈ D ⊓ Qm from ⟨ht,htq⟩)))
  obtain ⟨hWel,hW2,hnW,hnH,hHB,hBW,hspan,hneW,hcore,hmove,hfix,hindex⟩ :=
    source_suzuki_span_action_data h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy
      hc hxa hmin hnat hbranch hnear
  let : IsElementaryAbelian 2 W := hWel
  let : Finite W := Finite.of_injective
    (inclusion (hW2.trans (ballKernel_le_stabilizer F m 2))) (inclusion_injective _)
  have hAW : A ≤ normalizer (W : Set (G₀ L S)) := (star_le_stabilizer i).trans hnW
  let eA := (originalQuotient h i).symm.trans e
  obtain ⟨_,E,hE⟩ := Representation.SL2.natural_conjugate_quotient
    A W H B hAW ((star_le_stabilizer i).trans hnH) hHB hBW hspan hneW
    (by rw [star_core h i]; exact hcore) T eA hmove hfix hindex.le
  let : (H.subgroupOf W).Normal := normal_of_isMulCommutative _
  let q := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hqt : q tA ≠ 1 := by
    intro he
    have hm : tA ∈ pCore 2 A := (QuotientGroup.eq_one_iff tA).mp (eA.injective (he.trans eA.map_one.symm))
    apply htQ
    change t ∈ Q (reducedFamily L S) (base (reducedFamily L S) i)
    rw [←star_core h i]
    exact mem_map_of_mem A.subtype hm
  have hWJH : W ⊓ J ≤ H := by
    rintro w ⟨hw,hwJ⟩
    let wW : W := ⟨w,hw⟩
    have he : (⟨(tA : G₀ L S)*wW*(tA : G₀ L S)⁻¹,
        (mem_normalizer_iff.mp (hAW tA.property) wW).mp wW.property⟩ : W) = wW := by
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (hwJ t ht)
    have hv := (hE tA wW).symm
    rw [he] at hv
    have hv0 := Representation.SL2.natural_odd_fixed_eq_zero (q tA)
      (hto.of_dvd_nat (orderOf_map_dvd q tA)) hqt _ hv
    have hz0 : Additive.ofMul (QuotientGroup.mk wW : W ⧸ H.subgroupOf W) = 0 :=
      E.injective (hv0.trans E.map_zero.symm)
    exact (QuotientGroup.eq_one_iff wW).mp (congrArg Additive.toMul hz0)
  have hf := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have heq : W ⊓ J = H ⊓ J := le_antisymm (le_inf hWJH inf_le_right)
    (inf_le_inf_right J (hHB.trans hBW))
  have hsize := (source_suzuki_odd_centralizer_layers h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
    D hDA hodd hneD).2.2.2
  change W ⊓ J = ballKernel F m 3 ⊓ J ∧ Nat.card (W ⊓ J : Subgroup (G₀ L S)) = Nat.card k
  constructor
  · rw [hf]; exact heq
  · rw [heq]
    simpa only [hf] using hsize

/-- Choose the full-edge complement fixing the displayed second neighbor and
compute its linear part's centralizers through the original completion. -/
theorem source_suzuki_selected_torus_centralizers
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
    let A := star L S i
    let B := stabilizer F y ⊓ stabilizer F m
    let H := ballKernel F m 3
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    ∃ K : Subgroup B, (pCore 2 B).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map B.subtype ≤ stabilizer F x ∧
      let D := K.map B.subtype ⊓ A
      D ≠ ⊥ ∧ Odd (Nat.card D) ∧
      Q F m ⊓ centralizer (D : Set (G₀ L S)) ≤ C ∧
      Z F m ⊓ centralizer (D : Set (G₀ L S)) = ⊥ ∧
      ⁅H,D⁆ = Z F m ∧
      W ⊓ centralizer (D : Set (G₀ L S)) = H ⊓ centralizer (D : Set (G₀ L S)) ∧
      Nat.card (W ⊓ centralizer (D : Set (G₀ L S)) : Subgroup (G₀ L S)) = Nat.card k ∧
      (Q F m).map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) ≤
        C.map (G₀ L S).subtype ∧
      ⁅H.map (G₀ L S).subtype,D.map (G₀ L S).subtype⁆ = (Z F m).map (G₀ L S).subtype ∧
      W.map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) =
        H.map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) ∧
      Nat.card (W.map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) : Subgroup G) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let B := stabilizer F y ⊓ stabilizer F m
  let H := ballKernel F m 3
  let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨K,hK,hodd,hKx,_,_⟩ := source_linear_edge_complement h i e hadj.symm hxadj.symm hne
  let D := K.map B.subtype ⊓ A
  obtain ⟨hneD,hoddD,hQ,hZ,hHD,_,hQmap,hHDmap,_⟩ :=
    source_suzuki_edge_torus_centralizer_layers h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch K hK hodd
  obtain ⟨heq,hsize⟩ := source_suzuki_odd_span_centralizer h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
    D inf_le_right hoddD hneD
  refine ⟨K,hK,hodd,hKx,hneD,hoddD,hQ,hZ,hHD,heq,hsize,hQmap,hHDmap,?_,?_⟩
  · rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,
      map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective]
    exact congrArg (Subgroup.map (G₀ L S).subtype) heq
  · rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,
      card_map_of_injective (G₀ L S).subtype_injective]
    exact hsize

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
