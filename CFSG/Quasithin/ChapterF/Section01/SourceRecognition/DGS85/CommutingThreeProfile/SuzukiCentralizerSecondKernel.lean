module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondKernelSpan
public import Theory.GroupTheory.Commutator.SharpCentralizerIndex
/-!
# The full second kernel inside the third-kernel centralizer

Put H = G_m^(3), C = C_(Q_m)(H), and N = G_m^(2), at the linear
vertex of the nonbinary Suzuki branch. The sharp index |Q_m:C| = q²
forces C into V_x (Q_m ∩ Q_y): equality in the transverse displacement
bound identifies this product with its full commutator preimage.

The two disjoint center lines show N ≤ C. The product has elementary
image modulo Q_y, so Φ(C) lies in Q_y. The middle-core product also gives
[C,Q_m] ≤ Q_y. Both subgroups are normalized by the full middle vertex
stabilizer; its second-ball normal-core formula places both in N.
Consequently C/N is elementary and the actual conjugation action descends
to the original marked linear quotient. Its size is between q and q⁴:
the escaping neighboring span supplies the lower bound, and the full-core
upper bound together with the elementary span of order q⁵ supplies the upper.

The consumer preserves original endpoint conjugation and maps C to the
centralizer of the actual third kernel inside the original parabolic core.
All earlier source hypotheses are retained. In particular, this does not
identify N with W or assert irreducibility of C/W. The radius-two center
span V_m^(2) is not identified with the full permutation kernel N.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188–189, following (4) and (5).
-/
public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The sharp local centralizer position, its full second kernel, and the
Frattini and core-commutator containments needed for action descent. -/
theorem source_suzuki_centralizer_second_kernel
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
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    C ≤ V F x 1 ⊔ (Q F m ⊓ Q F y) ∧
    ballKernel F m 2 ≤ C ∧
    (frattini C).map C.subtype ≤ ballKernel F m 2 ∧
    ⁅C,Q F m⁆ ≤ ballKernel F m 2 := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let A := star L S i
  let Qm := Q F m
  let Zm := Z F m
  let D := V F x 1 ⊔ (Qm ⊓ Q F y)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite Qm := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite Zm := Finite.of_injective (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hXm : V F x 1 ≤ Qm := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxadj.symm
  have hQA : Qm ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hAQ : A ≤ normalizer (Qm : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F m)
  have hZQ : Zm ≤ Qm := (hZ m).trans (map_subtype_le _)
  have hZC : Zm ≤ centralizer (Qm : Set (G₀ L S)) := Z_centralizes_Q F m (hZ m)
  have ht := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hp := source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
  have hi : D.relIndex Qm = Nat.card k := by
    have hh := (source_suzuki_middle_core_bounds (k := k) h (!i) hb hc hxa
      (by simpa only [Bool.not_not] using hxadj.symm) hn eSuz
      (by cases i <;> exact e) Ry (by simpa only [Bool.not_not] using hRy)).2.2.1
    simpa only [Bool.not_not,←hfield] using hh
  have hD : D ≤ Qm := sup_le hXm inf_le_left
  have hQC : Qm ≤ centralizer (Z F y : Set (G₀ L S)) := le_centralizer_iff.mp (hzy.trans hZC)
  have hDH : ⁅D,H⁆ ≤ Z F y := by
    apply commutator_sup_le_of_relative_normal Qm (V F x 1) (Qm ⊓ Q F y) H (Z F y)
      (hQC.trans (Subgroup.centralizer_le_normalizer _)) hXm inf_le_left
    · have hX : IsElementaryAbelian 2 (V F x 1) := V_elementary F
        (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
      let := hX
      exact (commutator_mono le_rfl inf_le_left).trans
        ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)).le.trans bot_le)
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right inf_le_right).trans hcommy.le
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
  let f := (MulAut.conj g).toMonoidHom
  have hQf : Qm.map f = Qm := mem_normalizer_iff_map_conj_eq.mp (hAQ hg)
  have hHf : H.map f = H := mem_normalizer_iff_map_conj_eq.mp ((star_le_stabilizer i).trans ht.1 hg)
  have hZf : (Z F y).map f = Z F x := by rw [←Z_translate F,hgy]
  have hEH : ⁅D.map f,H⁆ ≤ Z F x := by
    have hh := map_mono (f := f) hDH
    rwa [map_commutator,hHf,hZf] at hh
  have hEQ : D.map f ≤ Qm := (map_mono hD).trans_eq hQf
  have hj : (D.map f).relIndex Qm = Nat.card k := by
    rw [←hQf,relIndex_map_map_of_injective D Qm (MulAut.conj g).injective,hi]
  have hdisj : Z F y ⊓ Z F x = ⊥ := by
    apply bot_unique
    intro z hz'
    have hzQ : z ∈ Qm := hZQ (hzy hz'.1)
    have hzA : z ∈ A := hQA hzQ
    have hzC : z ∈ centralizer (A : Set (G₀ L S)) := by
      have hgeneration := star_three_core_generation h i hxadj hne T R hT hR
      have hh : A ≤ centralizer ({z} : Set (G₀ L S)) := by
        change star L S i ≤ _
        rw [hgeneration]
        exact sup_le (sup_le
          (fun t ht => mem_centralizer_singleton_iff.mpr ((Z_centralizes_Q F y (hZ y) hz'.1) t ht))
          (fun t ht => mem_centralizer_singleton_iff.mpr ((Z_centralizes_Q F x (hZ x) hz'.2) t ht)))
          (fun t ht => mem_centralizer_singleton_iff.mpr (hZC (hzy hz'.1) t ht))
      exact fun t ht => mem_centralizer_singleton_iff.mp (hh ht)
    have hh : (⟨z,hzA⟩ : A) ∈ center A := mem_center_iff.mpr (fun a => Subtype.ext (hzC a a.property))
    have hh' := mem_bot.mp (hz ▸ hh)
    exact mem_bot.mpr (congrArg Subtype.val hh')
  have hfull := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  let C := Qm ⊓ centralizer (H : Set (G₀ L S))
  let N := ballKernel F m 2
  have hnormC : stabilizer F m ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf (CommutingTrivial.stabilizer_normalizes_Q F m)
      (ht.1.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hCQ : C ≤ Qm := inf_le_left
  have hCX : C ≤ centralizer (H : Set (G₀ L S)) := inf_le_right
  have hindex : (centralizer (H : Set (G₀ L S))).relIndex Qm = Nat.card k ^ 2 := by
    obtain ⟨hN,hi,_⟩ := source_suzuki_centralizer_quotient h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
    rw [hfull] at hi
    exact hi
  have hsharp := commutatorPreimage_eq_of_sharp_transverse_index Qm H (Z F y) (Z F x)
    D (D.map f) (hQC.trans (Subgroup.centralizer_le_normalizer _))
    ((le_centralizer_iff.mp (hzx.trans hZC)).trans (Subgroup.centralizer_le_normalizer _))
    hdisj hD hEQ hDH hEH Nat.card_pos hi hj hindex
  have hCD : C ≤ D := by
    rw [←hsharp.1]
    apply le_commutatorPreimage hCQ
    exact (commutator_eq_bot_iff_le_centralizer.mpr hCX).le.trans bot_le
  have hq4 : 4 ≤ Nat.card k := by
    rw [hfield]
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hNQ : N ≤ Qm := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) hq4 m
  have hNQz (z : Vertex F) (hz : (graph F).Adj m z) : N ≤ Q F z :=
    CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z)
      ((isPGroup_pCoreIn 2 _).to_le hNQ) (ballKernel_succ_le F hz 1)
  have hNC : N ≤ C := by
    apply le_inf hNQ
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [←hdisj,commutator_comm]
    exact le_inf ((commutator_mono inf_le_right (hNQz y hadj)).trans hcommy.le)
      ((commutator_mono inf_le_left (hNQz x hxadj)).trans hcommx)
  have hQy : Qm ≤ normalizer (Q F y : Set (G₀ L S)) :=
    (((source_Z_Q_U (reduced_triple h) m).2.trans
      (ballKernel_one_le_edge F hadj)).trans inf_le_right).trans
        (CommutingTrivial.stabilizer_normalizes_Q F y)
  have hNy : Qm ≤ normalizer ((Qm ⊓ Q F y : Subgroup (G₀ L S)) : Set (G₀ L S)) :=
    (le_inf Qm.le_normalizer hQy).trans inf_normalizer_le_normalizer_inf
  have hXel : IsElementaryAbelian 2 (V F x 1) :=
    V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  let := hXel
  let : Finite (V F x 1) := Finite.of_injective (inclusion hXm) (inclusion_injective _)
  have hDsq (d : D) : (d : G₀ L S)^2 ∈ Q F y := by
    have hn : V F x 1 ≤ normalizer ((Qm ⊓ Q F y : Subgroup (G₀ L S)) : Set (G₀ L S)) := hXm.trans hNy
    let : Fact (IsPGroup 2 (V F x 1)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
    have he := elementary_sup_quotient_of_frattini_image_le (V F x 1) (Qm ⊓ Q F y)
      (IsElementaryAbelian.isPGroup 2 _) hn (by
        rw [frattini_eq_bot_of_isElementaryAbelian (p := 2),Subgroup.map_bot]
        exact bot_le)
    let : ((Qm ⊓ Q F y).subgroupOf D).Normal := normal_subgroupOf_sup_of_le_normalizer hn
    let : IsElementaryAbelian 2 (D ⧸ (Qm ⊓ Q F y).subgroupOf D) := he
    have hs := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (D ⧸ (Qm ⊓ Q F y).subgroupOf D))
      (QuotientGroup.mk' ((Qm ⊓ Q F y).subgroupOf D) d)
    rw [←map_pow] at hs
    exact ((QuotientGroup.eq_one_iff _).mp hs).2
  let : Finite C := Finite.of_injective (inclusion hCQ) (inclusion_injective _)
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 _).to_le hCQ
  have hphiQ : (frattini C).map C.subtype ≤ Qm := (map_subtype_le _).trans hCQ
  have hphiy : (frattini C).map C.subtype ≤ Q F y := by
    rw [map_le_iff_le_comap,hpC.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro u ⟨c,rfl⟩
    exact hDsq ⟨c,hCD c.property⟩
  have hphiNorm : stabilizer F m ≤ normalizer (((frattini C).map C.subtype : Subgroup (G₀ L S)) : Set (G₀ L S)) :=
    hnormC.trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hXQ : ⁅V F x 1,Qm⁆ ≤ Q F y := by
    have hprod : Qm = (Q F x ⊓ Qm) ⊔ (Q F y ⊓ Qm) := hp.1
    rw [hprod,commutator_comm]
    apply commutator_sup_le_of_relative_normal Qm (Q F x ⊓ Qm) (Q F y ⊓ Qm)
      (V F x 1) (Q F y) hQy inf_le_right inf_le_right
    · rw [commutator_comm]
      exact ((commutator_mono le_rfl inf_le_left).trans hcommx).trans
        (hzx.trans (ht.2.2.2.2.2.2.1.trans (inf_le_right.trans
          (V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y))))
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hXm.trans hQy))
  have hCQy : ⁅C,Qm⁆ ≤ Q F y :=
    (commutator_mono hCD le_rfl).trans
      (commutator_sup_le_of_relative_normal Qm (V F x 1) (Qm ⊓ Q F y) Qm (Q F y)
        hQy hXm inf_le_left hXQ
        ((commutator_mono inf_le_right le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp hQy)))
  have hcommNorm : stabilizer F m ≤ normalizer ((⁅C,Qm⁆ : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnormC hg),
      mem_normalizer_iff_map_conj_eq.mp (CommutingTrivial.stabilizer_normalizes_Q F m hg)]
  have normal_into_second (J : Subgroup (G₀ L S)) (hJQ : J ≤ Qm)
      (hJy : J ≤ Q F y) (hJ : stabilizer F m ≤ normalizer (J : Set (G₀ L S))) : J ≤ N := by
    have hJm := hJQ.trans (Q_le_stabilizer F m)
    let : (J.subgroupOf (stabilizer F m)).Normal := normal_subgroupOf_of_le_normalizer hJ
    have hh : J.subgroupOf (stabilizer F m) ≤ N.subgroupOf (stabilizer F m) := by
      rw [ballKernel_two_eq_normalCore F hadj]
      apply normal_le_normalCore.mpr
      intro j hj
      exact ⟨(source_Z_Q_U (reduced_triple h) m).2 (hJQ hj),
        (source_Z_Q_U (reduced_triple h) y).2 (hJy hj)⟩
    intro j hj
    exact hh (show (⟨j,hJm hj⟩ : stabilizer F m) ∈ J.subgroupOf (stabilizer F m) from hj)
  dsimp only
  rw [hfull]
  exact ⟨hCD,hNC,normal_into_second _ hphiQ hphiy hphiNorm,
    normal_into_second _ ((commutator_mono hCQ le_rfl).trans (commutator_le_self _)) hCQy hcommNorm⟩

/-- The literal elementary C/G_m^(2) action, with geometric order bounds
and the original endpoint conjugation and centralizer denominator. -/
theorem source_suzuki_centralizer_second_action
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
    let H := ballKernel F m 3
    let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
    let N := ballKernel F m 2
    ∃ hAC : star L S i ≤ normalizer (C : Set (G₀ L S)),
    ∃ hN : (N.subgroupOf C).Normal,
      let := hN
      IsElementaryAbelian 2 (C ⧸ N.subgroupOf C) ∧
        Nat.card k ≤ Nat.card (C ⧸ N.subgroupOf C) ∧
        Nat.card (C ⧸ N.subgroupOf C) ≤ Nat.card k ^ 4 ∧
        C.map (G₀ L S).subtype = (parabolic L S (if i then 1 else 0)).pCoreIn 2 ⊓
          centralizer (H.map (G₀ L S).subtype : Set G) ∧
        N.map (G₀ L S).subtype ≤ C.map (G₀ L S).subtype ∧
        ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
          MulAut (C ⧸ N.subgroupOf C),
          ∀ a : L (if i then 1 else 0), ∀ c : C,
            ρ (QuotientGroup.mk a) (QuotientGroup.mk c) =
              QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i a : G₀ L S) * c *
                (originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (hAC
                  (originalActor (L := L) (S := S) i a).property) c).mp c.property⟩ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := ballKernel F m 3
  let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
  let N := ballKernel F m 2
  let A := star L S i
  let q := Nat.card k
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F m) := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Q F m from inf_le_left)) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 2)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨hCD,hNC,hphi,hCQ⟩ := source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hNC' : N ≤ C := hNC
  have hNormC : stabilizer F m ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf (CommutingTrivial.stabilizer_normalizes_Q F m)
      ((stabilizer_le_normalizer_ballKernel F m 3).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hAC : A ≤ normalizer (C : Set (G₀ L S)) := (star_le_stabilizer i).trans hNormC
  have hAN : A ≤ normalizer (N : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F m 2)
  let hN : (N.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    ((inf_le_left.trans (Q_le_stabilizer F m)).trans (stabilizer_le_normalizer_ballKernel F m 2))
  let := hN
  let hel : IsElementaryAbelian 2 (C ⧸ N.subgroupOf C) :=
    elementary_quotient_of_frattini_le ((isPGroup_pCoreIn 2 _).to_le (show C ≤ Q F m from inf_le_left))
      (N.subgroupOf C) (map_le_iff_le_comap.mp hphi)
  let := hel
  have hfull := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hXQ : V F x 1 ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate
    hZ (reduced_kernel_sylow h) hb hxadj.symm
  have hXC : V F x 1 ≤ C := by
    apply le_inf hXQ
    have he : IsElementaryAbelian 2 (V F x 1) :=
      V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
    let := he
    have hHX : H ≤ V F x 1 := hfull.le.trans inf_le_left
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hHX)
  have hNy : N ≤ Q F y := CommutingTrivial.two_subgroup_le_Q F y (reduced_kernel_sylow h y)
    ((isPGroup_pCoreIn 2 _).to_le (hNC'.trans inf_le_left)) (ballKernel_succ_le F hadj 1)
  have hXindex : (Q F y).relIndex (V F x 1) = q := by
    have hh := (source_suzuki_first_index h (!i) hb hc hxa hxadj.symm hadj.symm hn eSuz
      (by cases i <;> exact e) Ry hRy).1
    rw [inf_relIndex_left] at hh
    exact hh.trans hfield.symm
  have hlo : q ≤ Nat.card (C ⧸ N.subgroupOf C) := by
    rw [←hXindex]
    exact (relIndex_le_of_le_right hXC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_left hNy index_ne_zero_of_finite)
  have hupper := (source_suzuki_vertex_core_upper h i hb3 T hT e hz hcard hcardy hzy
    hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch).1
  have hqpos : 0 < q := Nat.card_pos
  have hCindex : C.relIndex (Q F m) = q^2 := by
    change (Q F m ⊓ centralizer (H : Set (G₀ L S))).relIndex (Q F m) = _
    rw [inf_relIndex_left]
    obtain ⟨_,hh,_⟩ := source_suzuki_centralizer_quotient h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
    exact hh
  have hCcard : Nat.card C ≤ q^9 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) C (Q F m) bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hCindex] at hh
    apply Nat.le_of_mul_le_mul_right (c := q^2) _ (by positivity)
    calc Nat.card C * q^2 = Nat.card (Q F m) := hh
         _ ≤ (2^(2*n+1))^11 := hupper
         _ = q^9 * q^2 := by dsimp [q]; rw [←hfield]; ring
  have hNcard : q^5 ≤ Nat.card N := by
    have hh := (source_suzuki_second_kernel_span_order h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hnear).2.2.2.2.2.2.2.2.2.2.1
    simpa only [q,hfield] using hh
  have hhi : Nat.card (C ⧸ N.subgroupOf C) ≤ q^4 := by
    have hh := (N.subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hNC').toEquiv,index_eq_card] at hh
    apply Nat.le_of_mul_le_mul_left (c := q^5) _ (by positivity)
    calc q^5 * Nat.card (C ⧸ N.subgroupOf C) ≤ Nat.card N * Nat.card (C ⧸ N.subgroupOf C) :=
           Nat.mul_le_mul_right _ hNcard
         _ = Nat.card C := hh
         _ ≤ q^9 := hCcard
         _ = q^5 * q^4 := by ring
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action A C N hAC hAN hN
  have hkill := quotient_conjugation_action_kills_commutator_layer A C N (Q F m) hN hAC hCQ α hα
  have hk : pCore 2 A ≤ α.ker := by
    intro a ha
    apply hkill
    change (a : G₀ L S) ∈ Q F m
    rw [←star_core h i]
    exact mem_map_of_mem A.subtype ha
  let β := QuotientGroup.lift (pCore 2 A) α hk
  let ρ := β.comp (originalQuotient h i).toMonoidHom
  have hQmap : (Q F m).map (G₀ L S).subtype = (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    change (Q (reducedFamily L S) (base (reducedFamily L S) i)).map _ = _
    rw [←star_core h i,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective,map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨hAC,hN,hel,hlo,hhi,?_,map_mono hNC',ρ,?_⟩
  · change (Q F m ⊓ centralizer (H : Set (G₀ L S))).map _ = _
    rw [←map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hQmap]
  · intro a c
    change β ((originalQuotient h i) (QuotientGroup.mk a)) (QuotientGroup.mk c) = _
    rw [originalQuotient_mk h i a]
    exact hα (originalActor (L := L) (S := S) i a) c
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
