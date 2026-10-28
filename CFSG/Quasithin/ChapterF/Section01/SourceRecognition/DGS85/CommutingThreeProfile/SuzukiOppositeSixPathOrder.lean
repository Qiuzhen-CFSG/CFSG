module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiComplementTransitivity

/-!
# The order estimate for the opposite source six-path

The Suzuki span has order q^5 and fixes the second ball. The actual
second-kernel quotient has order at least q^4, so the Suzuki core has
order at least q^9. The two common-Sylow indices, q and q^2, then give
order at least q^10 for the neighboring linear core.

On the opposite six-path a--r--t--u--w--m--v, the vertices r,u,m are
linear. Each distance-two restriction costs at most q^3, so the literal
intersection D = Q_r intersect Q_u intersect Q_m has index at most q^6
in Q_u and order at least q^4. In the small-image branch at v,
D intersect Q_v has order at least q^3. For every neighbor z of v,
D intersect Q_z has order at least q^2, the bound used by (12.7) in the
next step of (12.8).

The last theorem applies these bounds to the opposite six-path selected
with the source-minimal nonregular path's own full-Borel complement.
It retains the minimal path, the literal complement, both endpoint
orientations and all original inclusion maps. No core order, selected
path or endpoint transitivity is assumed. The original quotient marks,
critical geometry, common Sylows, natural center and earlier source
commutator/center data remain explicit.

The left-end transitivity from the nine-path argument and the deduction
s >= 7 remain to be assembled. Full-kernel equalities, Suzuki selection,
binary alternatives and the remaining (12.6)--(12.9)/(13.1) conclusions
are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.8), printed pp.185--186, using (12.1)(c,e), (12.5) and (12.6).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual Suzuki and linear cores have the source lower bounds q^9 and q^10. -/
theorem source_suzuki_core_order_lower
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆)
    (hcardZ : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^(2*n+1)) :
    let F := reducedFamily L S
    let q := 2^(2*n+1)
    q^9 ≤ Nat.card (Q F (base F i)) ∧
      q^10 ≤ Nat.card (Q F (base F (!i))) ∧
      q^9 ≤ Nat.card ((Q F (base F i)).map (G₀ L S).subtype) ∧
      q^10 ≤ Nat.card ((Q F (base F (!i))).map (G₀ L S).subtype) := by
  let F := reducedFamily L S
  let v := base F i
  let m := base F (!i)
  let q := 2^(2*n+1)
  let N := Q F v ⊓ ballKernel F v 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  let : Finite (Q F m) := Finite.of_injective (inclusion (Q_le_stabilizer F m))
    (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion (show N ≤ Q F v from inf_le_left))
    (inclusion_injective _)
  have hV := (source_suzuki_center_layer h i hb hc hxa hxm hn hq eSuz eLin
    T hT R hR hzy hcomm T₀ hT₀ hnat hfull hcardZ).2.1
  have hVN : V F v 1 ≤ N := le_inf
    (V_le_Q F (reduced_triple h).generate
      (fun z => (source_Z_Q_U (reduced_triple h) z).1) (reduced_kernel_sylow h) hb v)
    (V_le_ballKernel F (reduced_triple h).generate v
      (by change 3 ≤ b (reducedFamily L S); omega))
  have hN : q^5 ≤ Nat.card N := hV ▸
    Nat.card_le_card_of_injective (inclusion hVN) (inclusion_injective _)
  obtain ⟨ρ,hρ,hi,_⟩ := source_suzuki_second_kernel_faithful h i hb eSuz T₀ hT₀ R hR
    hnat hzy hcomm hfull
  have hiN : q^4 ≤ N.relIndex (Q F v) := by
    rw [inf_relIndex_left]
    exact hi
  have hmN := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) N (Q F v) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hmN
  have hv : q^9 ≤ Nat.card (Q F v) := by
    calc
      q^9 = q^5*q^4 := by ring
      _ ≤ Nat.card N * N.relIndex (Q F v) := Nat.mul_le_mul hN hiN
      _ = Nat.card (Q F v) := hmN
  obtain ⟨U,_,hiLin,_⟩ := source_common_sylow_core_index h (!i) eLin T₀ hT₀
  have hiL : (Q F v ⊓ Q F m).relIndex (Q F v) = q :=
    hiLin.trans ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.toEquiv).trans hq)
  obtain ⟨P,_,hiSuz,_⟩ := source_common_sylow_core_index h i eSuz R hR
  have hiS : (Q F m ⊓ Q F v).relIndex (Q F m) = q^2 :=
    hiSuz.trans (suzukiSylow_card hn (MulEquiv.refl _) P)
  have hmL := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F v ⊓ Q F m)
    (Q F v) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hiL] at hmL
  have hmS := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F m ⊓ Q F v)
    (Q F m) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hiS,inf_comm (Q F m)] at hmS
  have hm : q^10 ≤ Nat.card (Q F m) := by
    calc
      q^10 = q^9*q := by ring
      _ ≤ Nat.card (Q F v)*q := Nat.mul_le_mul_right q hv
      _ = Nat.card (Q F m) := by rw [←hmL,←hmS]; ring
  exact ⟨hv,hm,(card_map_of_injective (G₀ L S).subtype_injective).symm ▸ hv,
    (card_map_of_injective (G₀ L S).subtype_injective).symm ▸ hm⟩


private theorem core_index_at {F : Bool → Subgroup (G₀ L S)} {i : Bool} {d : ℕ}
    (hi : (Q F (base F i)).relIndex (Q F (base F (!i))) = d)
    {u v : Vertex F} (hu : u.type = i) (huv : (graph F).Adj u v) :
    (Q F u).relIndex (Q F v) = d := by
  obtain ⟨g,hgu,hgv⟩ := incident_common_translate F huv.2
  have hv : v.type = !i := Bool.eq_not_iff.mpr (hu ▸ huv.1.symm)
  rw [hu] at hgu
  rw [hv] at hgv
  rw [←hgu,←hgv,Q_translate,Q_translate,
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hi

private theorem core_card_at {F : Bool → Subgroup (G₀ L S)} {i : Bool}
    {u : Vertex F} (hu : u.type = i) : Nat.card (Q F u) = Nat.card (Q F (base F i)) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F u
  rw [hu] at hg
  rw [←hg,Q_translate]
  exact card_map_of_injective (MulAut.conj g).injective

private theorem two_step_core_index (Q M R : Subgroup (G₀ L S)) [Finite Q] [Finite M]
    {q : ℕ} (hQM : M.relIndex Q = q^2) (hMR : R.relIndex M = q) :
    R.relIndex Q ≤ q^3 := by
  have ht : (R ⊓ M).relIndex Q ≤ q*q^2 := by
    rw [←relIndex_inf_mul_relIndex,hQM]
    exact Nat.mul_le_mul_right (q^2) ((relIndex_le_of_le_right inf_le_left
      (show (R.subgroupOf M).index ≠ 0 from index_ne_zero_of_finite)).trans_eq hMR)
  exact ((relIndex_le_of_le_left inf_le_left
    (show ((R ⊓ M).subgroupOf Q).index ≠ 0 from index_ne_zero_of_finite)).trans ht).trans_eq
      (by ring)

/-- Bound the literal three-core intersection and its further endpoint restrictions. -/
theorem source_suzuki_three_core_order
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆)
    (hcardZ : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^(2*n+1))
    {r t u w : Vertex (reducedFamily L S)}
    (hrt : (graph (reducedFamily L S)).Adj r t)
    (htu : (graph (reducedFamily L S)).Adj t u)
    (huw : (graph (reducedFamily L S)).Adj u w)
    (hwm : (graph (reducedFamily L S)).Adj w (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    let q := 2^(2*n+1)
    let D := (Q F r ⊓ Q F u) ⊓ Q F (base F (!i))
    D.relIndex (Q F u) ≤ q^6 ∧ q^4 ≤ Nat.card D ∧
      (D.map (G₀ L S).subtype).relIndex ((Q F u).map (G₀ L S).subtype) ≤ q^6 ∧
      q^4 ≤ Nat.card (D.map (G₀ L S).subtype) ∧
      ((Q F (base F i)).relIndex D ≤ q →
        q^3 ≤ Nat.card (D ⊓ Q F (base F i) : Subgroup (G₀ L S)) ∧
        ∀ z, (graph F).Adj (base F i) z → q^2 ≤ Nat.card (D ⊓ Q F z : Subgroup (G₀ L S))) := by
  let F := reducedFamily L S
  let m := base F (!i)
  let v := base F i
  let q := 2^(2*n+1)
  let D := (Q F r ⊓ Q F u) ⊓ Q F m
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hfin (z : Vertex F) : Finite (Q F z) :=
    Finite.of_injective (inclusion (Q_le_stabilizer F z)) (inclusion_injective _)
  let := hfin u
  let := hfin t
  let := hfin w
  have hDu : D ≤ Q F u := inf_le_left.trans inf_le_right
  let : Finite D := Finite.of_injective (inclusion hDu) (inclusion_injective _)
  have hwt : w.type = i := by
    have hh : w.type = !(!i) := Bool.eq_not_iff.mpr hwm.1
    simpa only [Bool.not_not] using hh
  have hut : u.type = !i := Bool.eq_not_iff.mpr (hwt ▸ huw.1)
  have htt : t.type = i := by
    have hh : t.type = !(!i) := Bool.eq_not_iff.mpr (hut ▸ htu.1)
    simpa only [Bool.not_not] using hh
  have hrt' : r.type = !i := Bool.eq_not_iff.mpr (htt ▸ hrt.1)
  obtain ⟨P,_,hiS,_⟩ := source_common_sylow_core_index h i eSuz R hR
  have hs : (Q F v).relIndex (Q F m) = q^2 := by
    rw [inf_relIndex_left] at hiS
    exact hiS.trans (suzukiSylow_card hn (MulEquiv.refl _) P)
  obtain ⟨U,_,hiL,_⟩ := source_common_sylow_core_index h (!i) eLin T₀ hT₀
  have hl : (Q F m).relIndex (Q F v) = q := by
    rw [inf_relIndex_left] at hiL
    exact hiL.trans ((Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.toEquiv).trans hq)
  have hr : (Q F r).relIndex (Q F u) ≤ q^3 :=
    two_step_core_index (Q F u) (Q F t) (Q F r)
      (core_index_at hs htt htu) (core_index_at (by simpa only [Bool.not_not] using hl) hrt' hrt)
  have hm : (Q F m).relIndex (Q F u) ≤ q^3 :=
    two_step_core_index (Q F u) (Q F w) (Q F m)
      (core_index_at hs hwt huw.symm)
      (core_index_at (i := !i) (by simpa only [Bool.not_not] using hl) rfl hwm.symm)
  have hidx : D.relIndex (Q F u) ≤ q^6 := by
    have he : D = Q F u ⊓ (Q F r ⊓ Q F m) := by dsimp only [D]; ac_rfl
    rw [he,inf_relIndex_left]
    exact (relIndex_inf_le.trans (Nat.mul_le_mul hr hm)).trans_eq (by ring)
  have hcore := (source_suzuki_core_order_lower h i hb hc hxa hxm hn hq eSuz eLin
    T hT R hR hzy hcomm T₀ hT₀ hnat hfull hcardZ).2.1
  have hu : q^10 ≤ Nat.card (Q F u) := (core_card_at hut).symm ▸ hcore
  have hmult := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) D (Q F u) bot_le hDu
  rw [relIndex_bot_left,relIndex_bot_left] at hmult
  have hD : q^4 ≤ Nat.card D := by
    have hh : q^4*q^6 ≤ Nat.card D*q^6 := by
      calc
        q^4*q^6 = q^10 := by ring
        _ ≤ Nat.card (Q F u) := hu
        _ = Nat.card D * D.relIndex (Q F u) := hmult.symm
        _ ≤ Nat.card D * q^6 := Nat.mul_le_mul_left _ hidx
    exact (Nat.le_of_mul_le_mul_right hh (by positivity : 0 < q^6))
  refine ⟨hidx,hD,?_,?_,?_⟩
  · rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact hidx
  · rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hD
  · intro hsmall
    have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (D ⊓ Q F v) D bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at he
    have hh : q^3*q ≤ Nat.card (D ⊓ Q F v : Subgroup (G₀ L S))*q := by
      calc
        q^3*q = q^4 := by ring
        _ ≤ Nat.card D := hD
        _ = Nat.card (D ⊓ Q F v : Subgroup (G₀ L S)) * (Q F v).relIndex D := he.symm
        _ ≤ Nat.card (D ⊓ Q F v : Subgroup (G₀ L S))*q := Nat.mul_le_mul_left _ hsmall
    have hKlow := Nat.le_of_mul_le_mul_right hh (by positivity : 0 < q)
    refine ⟨hKlow,?_⟩
    intro z hz
    let K := D ⊓ Q F v
    let : Finite K := Finite.of_injective
      (inclusion (show K ≤ D from inf_le_left)) (inclusion_injective _)
    let : Finite (D ⊓ Q F z : Subgroup (G₀ L S)) := Finite.of_injective
      (inclusion (show D ⊓ Q F z ≤ D from inf_le_left)) (inclusion_injective _)
    let := hfin v
    have hzt : z.type = !i := Bool.eq_not_iff.mpr hz.1.symm
    have hzidx : (Q F z).relIndex (Q F v) = q :=
      core_index_at (i := !i) (by simpa only [Bool.not_not] using hl) hzt hz.symm
    have hki : (Q F z).relIndex K ≤ q :=
      (relIndex_le_of_le_right inf_le_right
        (show ((Q F z).subgroupOf (Q F v)).index ≠ 0 from index_ne_zero_of_finite)).trans_eq hzidx
    have hkm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (K ⊓ Q F z) K bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hkm
    have hkz : q^2 ≤ Nat.card (K ⊓ Q F z : Subgroup (G₀ L S)) := by
      refine Nat.le_of_mul_le_mul_right
        (show q^2*q ≤ Nat.card (K ⊓ Q F z : Subgroup (G₀ L S))*q from ?_) (by positivity)
      calc
        q^2*q = q^3 := by ring
        _ ≤ Nat.card K := hKlow
        _ = Nat.card (K ⊓ Q F z : Subgroup (G₀ L S)) * (Q F z).relIndex K := hkm.symm
        _ ≤ Nat.card (K ⊓ Q F z : Subgroup (G₀ L S))*q := Nat.mul_le_mul_left _ hki
    exact hkz.trans (Nat.card_le_card_of_injective
      (inclusion (inf_le_inf_right (Q F z) (show K ≤ D from inf_le_left))) (inclusion_injective _))

/-- Apply the core bounds to the source-selected opposite six-path with its original complement. -/
theorem source_mixed_selected_opposite_six_path_order
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆)
    (hcardZ : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^(2*n+1)) :
    let F := reducedFamily L S
    let m := base F (!i)
    let v := base F i
    let q := 2^(2*n+1)
    ∃ l : ℕ, l+1 = sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) ∧
      ∃ j : Bool, ∃ p : SimpleGraph.BasedWalk (graph F) (l+1) (base F j),
        p.Nonbacktracking ∧ ¬ Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) p ∧
        p.toWalk.IsPath ∧ ∃ C : Subgroup (G₀ L S),
          Odd (Nat.card C) ∧ C ≤ pathStabilizer F p ∧
          C.map (G₀ L S).subtype ≤ B₀ L S ⊓ (pathStabilizer F p).map (G₀ L S).subtype ∧
          Disjoint (C.map (G₀ L S).subtype) ((commonBorel L S).pCoreIn 2) ∧
          C.map (G₀ L S).subtype ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧
          ∃ a' r t u w : Vertex F, ∃ γ : SimpleGraph.BasedWalk (graph F) 6 a',
            γ.vertices = [a',r,t,u,w,m,v] ∧ γ.Nonbacktracking ∧
            C ≤ pathStabilizer F γ ∧
            let D := (Q F r ⊓ Q F u) ⊓ Q F m
            D ≤ pathStabilizer F γ ∧
            D.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
            D.relIndex (Q F u) ≤ q^6 ∧ q^4 ≤ Nat.card D ∧
            (D.map (G₀ L S).subtype).relIndex ((Q F u).map (G₀ L S).subtype) ≤ q^6 ∧
            q^4 ≤ Nat.card (D.map (G₀ L S).subtype) ∧
            ((Q F v).relIndex D ≤ q ∧
              ((Q F v).map (G₀ L S).subtype).relIndex (D.map (G₀ L S).subtype) ≤ q ∧
              q^3 ≤ Nat.card (D ⊓ Q F v : Subgroup (G₀ L S)) ∧
              q^3 ≤ Nat.card ((D ⊓ Q F v).map (G₀ L S).subtype) ∧
              (∀ z, (graph F).Adj v z →
                q^2 ≤ Nat.card (D ⊓ Q F z : Subgroup (G₀ L S)) ∧
                q^2 ≤ Nat.card ((D ⊓ Q F z).map (G₀ L S).subtype)) ∨
              (Q F v).relIndex D = q^2 ∧
                Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) γ) := by
  let F := reducedFamily L S
  let m := base F (!i)
  let v := base F i
  let q := 2^(2*n+1)
  obtain ⟨l,hl,j,p,hp,hpn,hps,C,hodd,hCp,hCo,hdis,hsup,a',r,t,u,w,γ,hγv,hγn,hCγ,hD,hDo,hcase⟩ :=
    source_mixed_selected_opposite_six_path h (!i) hn eLin
      (by cases i <;> exact eSuz) (by cases i <;> exact R) (by cases i <;> exact hR)
  simp only [Bool.not_not] at hγv hD hDo hcase
  have hadj : (graph F).Adj r t ∧ (graph F).Adj t u ∧
      (graph F).Adj u w ∧ (graph F).Adj w m := by
    rcases γ with ⟨⟨r',hr'⟩,⟨⟨t',ht'⟩,⟨⟨u',hu'⟩,⟨⟨w',hw'⟩,⟨⟨m',hm'⟩,⟨⟨v',hv'⟩,z⟩⟩⟩⟩⟩⟩
    change [a',r',t',u',w',m',v'] = [a',r,t,u,w,m,v] at hγv
    simp only [List.cons.injEq] at hγv
    rcases hγv with ⟨_,rfl,rfl,rfl,rfl,rfl,rfl,_⟩
    exact ⟨ht',hu',hw',hm'⟩
  obtain ⟨hidx,hlow,hidxo,hlowo,hsmall⟩ := source_suzuki_three_core_order h i hb hc hxa hxm
    hn hq eSuz eLin T hT R hR hzy hcomm T₀ hT₀ hnat hfull hcardZ
    hadj.1 hadj.2.1 hadj.2.2.1 hadj.2.2.2
  refine ⟨l,hl,j,p,hp,hpn,hps,C,hodd,hCp,hCo,hdis,hsup,a',r,t,u,w,γ,hγv,hγn,hCγ,
    hD,hDo,hidx,hlow,hidxo,hlowo,?_⟩
  rcases hcase with ⟨hs,hso⟩ | hh
  · refine Or.inl ⟨hs,hso,(hsmall hs).1,?_,?_⟩
    · rw [card_map_of_injective (G₀ L S).subtype_injective]
      exact (hsmall hs).1
    · intro z hz
      refine ⟨(hsmall hs).2 z hz,?_⟩
      rw [card_map_of_injective (G₀ L S).subtype_injective]
      exact (hsmall hs).2 z hz
  · exact Or.inr hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
