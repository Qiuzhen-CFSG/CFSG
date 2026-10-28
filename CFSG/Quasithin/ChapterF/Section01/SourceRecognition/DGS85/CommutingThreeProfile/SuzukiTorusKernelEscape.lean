module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTorusSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondKernelCentralizer
public import Theory.GroupAction.RankTwoCosetGeometry.TransitiveKernelPropagation
/-!
# The selected linear torus avoids the first three local kernels

At the linear vertex m put H = G_m^(3), W equal to the original span,
and C = C_(Q_m)(H). For every nontrivial odd subgroup D of star_m,
coprime splitting of the already established natural actions gives
Q_m = [Q_m,D] C, W = [W,D] H, and [Z_m,D] = Z_m.

The centralizer placement C ≤ V_x (Q_m ∩ Q_y), of proper index q in
Q_m, excludes D from the first neighboring permutation kernel. Relative
normality and three-path transitivity propagate a second-vertex constraint
on W to the whole third kernel, contradicting |W| > |H|. On the third
vertex the transported critical pair excludes Z_m from the local kernel.
Applying these arguments to every nontrivial subgroup of D proves trivial
intersections, not merely noncontainment.

The final application constructs the same full-edge complement used in
SuzukiTorusSpan, retains its order-q fixed subgroup in W, and transports all
three kernel exclusions through the literal original completion inclusion.
These are the local-action inputs to the eight-path centralizer argument.
The bound C_(Q_m)(D) ≤ H, irreducibility of C/W, and G_m^(2) = W remain
to be proved. All original markings, natural-center and reciprocal
commutator hypotheses remain explicit, as do the remaining Chapter 12/13
assembly obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed p.189, the three nonbinary torus kernel exclusions.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
private theorem source_suzuki_odd_torus_kernel_escape
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
    (∀ z, (graph F).Adj m z → ¬ D ≤ ballKernel F z 1) ∧
      ∀ p : BasedWalk (graph F) 3 m, p.Nonbacktracking →
        (¬ D ≤ ballKernel F (p.2.1 : Vertex F) 1) ∧
        (¬ D ≤ ballKernel F p.endpoint 1) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let Qm := Q F m
  let H := ballKernel F m 3
  let Zm := Z F m
  let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
  let C := Qm ⊓ centralizer (H : Set (G₀ L S))
  let P := V F x 1 ⊔ (Qm ⊓ Q F y)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite D := Finite.of_injective (inclusion (hDA.trans (star_le_stabilizer i))) (inclusion_injective _)
  let : Finite Qm := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  obtain ⟨hWel,hW2,_,hnW,_,_,_,_,_⟩ :=
    source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  let : IsElementaryAbelian 2 W := hWel
  let : Finite W := Finite.of_injective (inclusion (hW2.trans (ballKernel_le_stabilizer F m 2))) (inclusion_injective _)
  let : IsElementaryAbelian 2 Zm := Noncommuting.graph_Z_elementary (reduced_triple h) m
  have hQnorm := CommutingTrivial.stabilizer_normalizes_Q F m
  have hCnorm : stabilizer F m ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf hQnorm ((stabilizer_le_normalizer_ballKernel F m 3).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hDZ : D ≤ normalizer (Zm : Set (G₀ L S)) :=
    (hDA.trans (star_le_stabilizer i)).trans (stabilizer_normalizes_Z F m)
  have hcop (B : Subgroup (G₀ L S)) [Finite B] (hp : IsPGroup 2 B) :
      Nat.Coprime (Nat.card D) (Nat.card B) := by
    obtain ⟨j,hj⟩ := hp.exists_card_eq
    rw [hj]
    exact (Nat.coprime_two_right.mpr hodd).pow_right j
  obtain ⟨hQfix,hZfix,_,_⟩ := source_suzuki_odd_centralizer_layers h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
    D hDA hodd hneD
  obtain ⟨hWfix,_⟩ := source_suzuki_odd_span_centralizer h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
    D hDA hodd hneD
  have hpQ : IsPGroup 2 Qm := isPGroup_pCoreIn 2 _
  let : Group.IsNilpotent Qm := hpQ.isNilpotent
  have hQsplit : Qm ≤ ⁅Qm,D⁆ ⊔ C := by
    have hs := eq_commutator_sup_centralizer_of_finite_solvable_coprime Qm D
      ((hDA.trans (star_le_stabilizer i)).trans hQnorm)
      inferInstance
      (hcop Qm (isPGroup_pCoreIn 2 _))
    exact hs.le.trans (sup_le_sup_left hQfix _)
  have hWsplit : W ≤ ⁅W,D⁆ ⊔ H := by
    have hs := eq_commutator_sup_centralizer_of_finite_solvable_coprime W D
      ((hDA.trans (star_le_stabilizer i)).trans hnW)
      (Group.isSolvable_of_comm fun a b => mul_comm a b)
      (hcop W (IsElementaryAbelian.isPGroup 2 W))
    exact hs.le.trans (sup_le_sup_left (hWfix.le.trans inf_le_left) _)
  change Zm ⊓ centralizer (D : Set (G₀ L S)) = ⊥ at hZfix
  have hZsplit : ⁅Zm,D⁆ = Zm := by
    have hs := eq_commutator_sup_centralizer_of_finite_solvable_coprime Zm D hDZ
      (Group.isSolvable_of_comm fun a b => mul_comm a b)
      (hcop Zm (IsElementaryAbelian.isPGroup 2 Zm))
    simpa only [hZfix,sup_bot_eq] using hs.symm
  have hCP : C ≤ P := (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have hPi : P.relIndex Qm = Nat.card k := by
    have hh := (source_suzuki_middle_core_bounds (k := k) h (!i) hb hc hxa
      (by simpa only [Bool.not_not] using hxadj.symm) hn eSuz
      (by cases i <;> exact e) Ry (by simpa only [Bool.not_not] using hRy)).2.2.1
    simpa only [Bool.not_not,←hfield] using hh
  have hnotW : ¬ W ≤ H := (source_suzuki_second_kernel_span_centralizers h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear).2.2.2.2.1
  have hZH : Zm ≤ H := by
    have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
    exact ht.2.2.2.2.2.2.1.trans ht.2.2.1
  have comm_kernel (N : Subgroup (G₀ L S)) (z : Vertex F)
      (hNz : N ≤ stabilizer F z) (hDz : D ≤ ballKernel F z 1) :
      ⁅N,D⁆ ≤ ballKernel F z 1 :=
    (commutator_mono le_rfl hDz).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hNz.trans (stabilizer_le_normalizer_ballKernel F z 1)))
  constructor
  · intro z hzadj hDz
    obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hzadj
    let f := (MulAut.conj g).toMonoidHom
    have hQf : Qm.map f = Qm := mem_normalizer_iff_map_conj_eq.mp (hQnorm (star_le_stabilizer i hg))
    have hCf : C.map f = C := mem_normalizer_iff_map_conj_eq.mp (hCnorm (star_le_stabilizer i hg))
    have hCnew : C ≤ P.map f := hCf ▸ map_mono hCP
    have hcore : ⁅Qm,D⁆ ≤ Q F z := by
      apply CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z)
        ((isPGroup_pCoreIn 2 _).to_le
          (le_normalizer_iff_commutator_le_left.mp ((hDA.trans (star_le_stabilizer i)).trans hQnorm)))
      exact comm_kernel Qm z (((source_Z_Q_U (reduced_triple h) m).2.trans
        (ballKernel_one_le_edge F hzadj)).trans inf_le_right) hDz
    have hcomm : ⁅Qm,D⁆ ≤ P.map f := by
      have hm := map_mono (f := f) (show Qm ⊓ Q F y ≤ P from le_sup_right)
      rw [map_inf _ _ _ (MulAut.conj g).injective,hQf,←Q_translate F,hgy] at hm
      exact (le_inf (le_normalizer_iff_commutator_le_left.mp
        ((hDA.trans (star_le_stabilizer i)).trans hQnorm)) hcore).trans hm
    have hle : Qm ≤ P.map f := hQsplit.trans (sup_le hcomm hCnew)
    have hi : (P.map f).relIndex Qm = Nat.card k := by
      rw [←hQf,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hPi]
    rw [relIndex_eq_one.mpr hle] at hi
    have hbig : 1 < Nat.card k := by rw [hfield]; exact Nat.one_lt_pow (by omega) (by decide)
    omega
  · intro p hp
    constructor
    · intro hDp
      have hHz : H ≤ ballKernel F (p.2.1 : Vertex F) 1 :=
        (ballKernel_succ_le F p.1.property 2).trans (ballKernel_succ_le F p.2.1.property 1)
      have hWz : W ≤ stabilizer F (p.2.1 : Vertex F) :=
        ((hW2.trans (ballKernel_succ_le F p.1.property 1)).trans
          (ballKernel_succ_le F p.2.1.property 0)).trans (ballKernel_le_stabilizer F _ 0)
      have hWU := hWsplit.trans (sup_le (comm_kernel W _ hWz hDp) hHz)
      exact hnotW (le_third_ballKernel_of_normalized_two_kernel F
        (source_mixed_three_path_transitive h i hn e eSuz T hT Ry hRy i) p hp W hnW hW2 hWU)
    · intro hDp
      have hZp : Zm ≤ stabilizer F p.endpoint := by
        intro z hz
        exact hZH hz p.endpoint p.toWalk.edist_le
      have hh : Zm ≤ ballKernel F p.endpoint 1 := hZsplit.ge.trans (comm_kernel Zm _ hZp hDp)
      have hcrit := source_critical_pair_on_three_path (F := F) (reduced_triple h).generate hc hb3 p hp
        (source_mixed_three_path_transitive h i hn e eSuz T hT Ry hRy i)
        (by change i = a.type; exact (source_critical_pair_linear_type h i hb3 hzy hc).symm)
      exact hcrit.2 hh

/-- Every odd subgroup of the original linear star avoids the local kernels along each three-path. -/
theorem source_suzuki_odd_torus_kernel_disjoint
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
    (hodd : Odd (Nat.card D)) :
    let F := reducedFamily L S
    let m := base F i
    (∀ z, (graph F).Adj m z → Disjoint D (ballKernel F z 1)) ∧
      ∀ p : BasedWalk (graph F) 3 m, p.Nonbacktracking →
        Disjoint D (ballKernel F (p.2.1 : Vertex F) 1) ∧
        Disjoint D (ballKernel F p.endpoint 1) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite D := Finite.of_injective (inclusion (hDA.trans (star_le_stabilizer i))) (inclusion_injective _)
  have avoid (J : Subgroup (G₀ L S))
      (hJ : ∀ E : Subgroup (G₀ L S), E ≤ D → Odd (Nat.card E) → E ≠ ⊥ → ¬ E ≤ J) :
      Disjoint D J := by
    apply disjoint_iff.mpr
    by_contra hneE
    exact hJ (D ⊓ J) inf_le_left
      (hodd.of_dvd_nat (card_dvd_of_le (show D ⊓ J ≤ D from inf_le_left))) hneE inf_le_right
  constructor
  · intro z hzadj
    apply avoid
    intro E hED hoddE hneE
    exact (source_suzuki_odd_torus_kernel_escape h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
      E (hED.trans hDA) hoddE hneE).1 z hzadj
  · intro p hp
    constructor
    · apply avoid
      intro E hED hoddE hneE
      exact ((source_suzuki_odd_torus_kernel_escape h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
        E (hED.trans hDA) hoddE hneE).2 p hp).1
    · apply avoid
      intro E hED hoddE hneE
      exact ((source_suzuki_odd_torus_kernel_escape h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
        E (hED.trans hDA) hoddE hneE).2 p hp).2

/-- The selected full-edge complement has the required kernel exclusions, also after the original completion inclusion. -/
theorem source_suzuki_selected_torus_kernel_disjoint
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
    let B := stabilizer F y ⊓ stabilizer F m
    let H := ballKernel F m 3
    let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    ∃ K : Subgroup B, (pCore 2 B).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map B.subtype ≤ stabilizer F x ∧
      let D := K.map B.subtype ⊓ star L S i
      D ≠ ⊥ ∧ Odd (Nat.card D) ∧
      Q F m ⊓ centralizer (D : Set (G₀ L S)) ≤ C ∧
      W ⊓ centralizer (D : Set (G₀ L S)) = H ⊓ centralizer (D : Set (G₀ L S)) ∧
      Nat.card (W ⊓ centralizer (D : Set (G₀ L S)) : Subgroup (G₀ L S)) = Nat.card k ∧
      ∀ p : BasedWalk (graph F) 3 m, p.Nonbacktracking →
        Disjoint D (ballKernel F (p.1 : Vertex F) 1) ∧
        Disjoint D (ballKernel F (p.2.1 : Vertex F) 1) ∧
        Disjoint D (ballKernel F p.endpoint 1) ∧
        Disjoint (D.map (G₀ L S).subtype) ((ballKernel F (p.1 : Vertex F) 1).map (G₀ L S).subtype) ∧
        Disjoint (D.map (G₀ L S).subtype) ((ballKernel F (p.2.1 : Vertex F) 1).map (G₀ L S).subtype) ∧
        Disjoint (D.map (G₀ L S).subtype) ((ballKernel F p.endpoint 1).map (G₀ L S).subtype) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let B := stabilizer F y ⊓ stabilizer F m
  obtain ⟨K,hK,hodd,hKx,hneD,hoddD,hQ,_,_,hW,hsize,_⟩ :=
    source_suzuki_selected_torus_centralizers h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let D := K.map B.subtype ⊓ star L S i
  obtain ⟨hfirst,hlater⟩ := source_suzuki_odd_torus_kernel_disjoint h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
    D inf_le_right hoddD
  refine ⟨K,hK,hodd,hKx,hneD,hoddD,hQ,hW,hsize,?_⟩
  intro p hp
  have h₁ := hfirst (p.1 : Vertex F) p.1.property
  obtain ⟨h₂,h₃⟩ := hlater p hp
  exact ⟨h₁,h₂,h₃,disjoint_map (G₀ L S).subtype_injective h₁,
    disjoint_map (G₀ L S).subtype_injective h₂,disjoint_map (G₀ L S).subtype_injective h₃⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
