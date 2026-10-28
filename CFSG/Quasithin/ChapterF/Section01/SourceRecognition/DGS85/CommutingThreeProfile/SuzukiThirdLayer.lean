module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionOrder
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The geometric intersection inside the full third kernel

The two neighboring cores and the middle core generate the middle star.
Their source commutator bounds show that the intersection H of the two
spans satisfies [H,star] = Z_middle. Hence the star normalizes H. Its
neighbor transitivity identifies H with the intersection of all neighboring
spans, and gives normality in the full middle stabilizer.

The exact second-kernel intersections then place H in the full third
kernel. Its intersection with either original span is exactly H. Together
with the proved order q^3 and the natural center of order q^2, this gives
the central order-q section H/Z_middle, retaining the original embeddings
and the full starred commutator.

These are genuine steps toward (12.9)(c3,c4). Equality of H with the whole
third kernel is not asserted. The earlier (12.1), (12.3) inputs, Suzuki
selection and all remaining source path and binary obligations are retained.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.6), (12.8), (12.9), printed pp.183,185--188.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual intersection lies in the third kernel and gives its central order-q layer. -/
theorem source_suzuki_third_kernel_layer
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
      (Q (reducedFamily L S) (base (reducedFamily L S) i))) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let H := V F x 1 ⊓ V F y 1
    stabilizer F m ≤ normalizer (H : Set (G₀ L S)) ∧
    H = ⨅ z, ⨅ (_ : (graph F).Adj m z), V F z 1 ∧
    H ≤ ballKernel F m 3 ∧
    V F y 1 ⊓ ballKernel F m 3 = H ∧
    V F x 1 ⊓ ballKernel F m 3 = H ∧
    ⁅H, star L S i⁆ = Z F m ∧
    Z F m ≤ H ∧
    (Z F m).relIndex H = 2^(2*n+1) ∧
    Nat.card H = (2^(2*n+1))^3 ∧
    H.map (G₀ L S).subtype ≤ (ballKernel F m 3).map (G₀ L S).subtype ∧
    ⁅H.map (G₀ L S).subtype, starredParabolic L S (if i then 1 else 0)⁆ =
      (Z F m).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let X := V F x 1
  let Y := V F y 1
  let H := X ⊓ Y
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hXm : X ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxadj.symm
  have hHm : H ≤ stabilizer F m := (inf_le_left.trans hXm).trans (Q_le_stabilizer F m)
  have hZHX : Z F m ≤ H := le_inf (Z_neighbor_le_V F hxadj.symm)
    (Z_neighbor_le_V F hadj.symm)
  have hp := source_suzuki_product_and_intersection_commutator h i hb hxadj hne
    T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor
    hn eSuz hfield Ry hRy hc hxa hmin
  have hgen := star_three_core_generation h i hxadj hne T R hT hR
  have hQA : Q F y ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hQxA : Q F x ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hQmA : Q F m ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hAZ : A ≤ normalizer (Z F m : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_normalizes_Z F m)
  have hHy : ⁅Q F y,H⁆ ≤ Z F m := by
    rw [commutator_comm]
    exact ((commutator_mono inf_le_right le_rfl).trans hcommy.le).trans hzy
  have hHx : ⁅Q F x,H⁆ ≤ Z F m := by
    rw [commutator_comm]
    exact ((commutator_mono inf_le_left le_rfl).trans hcommx).trans hzx
  have hHstar : ⁅H,A⁆ = Z F m := by
    apply le_antisymm
    · rw [commutator_comm]
      change ⁅star L S i,H⁆ ≤ Z F m
      rw [hgen]
      exact commutator_sup_le_of_relative_normal A (Q F y ⊔ Q F x) (Q F m) H (Z F m)
        hAZ (sup_le hQA hQxA) hQmA
        (commutator_sup_le_of_relative_normal A (Q F y) (Q F x) H (Z F m)
          hAZ hQA hQxA hHy hHx) (by rw [commutator_comm]; exact hp.2.1.le)
    · exact hp.2.1.ge.trans (commutator_mono le_rfl hQmA)
  have hnorm : A ≤ normalizer (H : Set (G₀ L S)) :=
    le_normalizer_iff_commutator_le_left.mpr (hHstar.le.trans hZHX)
  have hAllspan : ∀ z, (graph F).Adj m z → H ≤ V F z 1 := by
    intro z hz
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive h i hxadj hz
    have he : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hnorm hg)
    rw [←hgz,V_translate,←he]
    exact map_mono inf_le_left
  have hspan : H = ⨅ z, ⨅ (_ : (graph F).Adj m z), V F z 1 := by
    apply le_antisymm (le_iInf fun z => le_iInf fun hz => hAllspan z hz)
    exact le_inf (iInf_le_of_le x (iInf_le _ hxadj))
      (iInf_le_of_le y (iInf_le _ hadj))
  have hnfull : stabilizer F m ≤ normalizer (H : Set (G₀ L S)) := by
    apply le_normalizer_iff.mpr
    intro g hg u hu
    have hv (v : Vertex F) (hv : (graph F).Adj m v) : g * u * g⁻¹ ∈ V F v 1 := by
      have hpre : (graph F).Adj m (g⁻¹ • v) := by
        have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hv
        change (graph F).Adj (g⁻¹ • m) (g⁻¹ • v) at hh
        rwa [show g⁻¹ • m = m from (stabilizer F m).inv_mem hg] at hh
      have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom (hAllspan _ hpre hu)
      rw [←V_translate F,smul_inv_smul] at hm
      exact hm
    exact ⟨hv x hxadj,hv y hadj⟩
  obtain ⟨_,_,hNx,hNy,_,_⟩ := source_suzuki_intersection_kernels
    h i hb hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hHN : H ≤ ballKernel F x 2 := hNx.ge.trans inf_le_right
  have hAll : ∀ z, (graph F).Adj m z → H ≤ ballKernel F z 2 := by
    intro z hz
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive h i hxadj hz
    have he : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hnorm hg)
    rw [←hgz,ballKernel_translate,←he]
    exact map_mono hHN
  have hH3 : H ≤ ballKernel F m 3 := by
    intro g hg z hz
    have hdist : (graph F).edist m z ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp : (3 : ℕ∞) ≠ ⊤) hz
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
    have hlen : p.length ≤ 3 := by
      have hh : (p.length : ℕ∞) ≤ (3 : ℕ∞) := hp ▸ hz
      exact ENat.natCast_le_natCast.mp hh
    cases p with
    | nil => exact hHm hg
    | @cons _ u _ hu p =>
      apply hAll u hu hg z
      exact p.edist_le.trans (ENat.natCast_le_natCast.mpr (by
        simp only [SimpleGraph.Walk.length_cons] at hlen
        omega))
  have hY3 : Y ⊓ ballKernel F m 3 = H :=
    le_antisymm ((inf_le_inf_left Y (ballKernel_succ_le F hxadj 2)).trans hNx.le)
      (le_inf inf_le_right hH3)
  have hX3 : X ⊓ ballKernel F m 3 = H :=
    le_antisymm ((inf_le_inf_left X (ballKernel_succ_le F hadj 2)).trans hNy.le)
      (le_inf inf_le_left hH3)
  have hHcard := (source_suzuki_intersection_card h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy
    hc hxa hmin hnat).1
  have hind : (Z F m).relIndex H = 2^(2*n+1) := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Z F m) H bot_le hZHX
    rw [relIndex_bot_left,relIndex_bot_left,hcard,hfield] at hm
    change (2^(2*n+1))^2 * (Z F m).relIndex H = Nat.card H at hm
    rw [hHcard] at hm
    have hpow : (2^(2*n+1))^3 = (2^(2*n+1))^2 * 2^(2*n+1) := by ring
    rw [hpow] at hm
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hm
  have horig := congrArg (Subgroup.map (G₀ L S).subtype) hHstar
  rw [map_commutator,map_subgroupOf_eq_of_le (star_le_completion _)] at horig
  exact ⟨hnfull,hspan,hH3,hY3,hX3,hHstar,hZHX,hind,hHcard,map_mono hH3,horig⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
