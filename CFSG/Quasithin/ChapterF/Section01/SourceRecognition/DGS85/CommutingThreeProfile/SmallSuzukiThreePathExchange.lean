module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSymmetricIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiNeighborOrbits
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# Exchanging a three-path at the actual small Suzuki endpoint

The literal Sz(2) common-Sylow quotient supplies transitivity of the opposite
full core on the remaining neighbors. After exchanging the two quintic
vertices through their common linear neighbor, that core corrects the final
vertex without changing the first three images. One original transporter
therefore gives the exchanged second index. The same orbit transports a
nonzero intersection commutator to the chosen other neighbor center.

The source paths, original quotient markings and actual common Sylow remain
unchanged. No positive Suzuki parameter, short-path transitivity, or generation
of the order-twenty quotient by two involutions is assumed. The intentional
internal import reuses only this family's generic linear neighbor swap.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1)(c,e), (12.3)(a), and (*) in (12.7), printed pp.178--179,184;
the parameter-zero neighbor action is supplied by SmallSuzukiNeighborOrbits.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem small_suzuki_neighbor_core_transitive_at
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {u v a b : Vertex (reducedFamily L S)} (hu : u.type = i)
    (hv : (graph (reducedFamily L S)).Adj u v)
    (ha : (graph (reducedFamily L S)).Adj u a)
    (hb : (graph (reducedFamily L S)).Adj u b) (hav : a ≠ v) (hbv : b ≠ v) :
    ∃ g ∈ Q (reducedFamily L S) v, g • a = b := by
  let F := reducedFamily L S
  obtain ⟨s,hsu,hsv⟩ := incident_common_translate F hv.2
  have ht : v.type = !i := Bool.eq_not_iff.mpr (hu ▸ hv.1.symm)
  rw [hu] at hsu
  rw [ht] at hsv
  have hsu' : s⁻¹ • u = base F i := by rw [←hsu,inv_smul_smul]
  have hsv' : s⁻¹ • v = base F (!i) := by rw [←hsv,inv_smul_smul]
  have hadj {x : Vertex F} (hx : (graph F).Adj u x) :
      (graph F).Adj (base F i) (s⁻¹ • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F s⁻¹).map_adj_iff.mpr hx
    change (graph F).Adj (s⁻¹ • u) (s⁻¹ • x) at hh
    rwa [hsu'] at hh
  have hne {x : Vertex F} (hx : x ≠ v) : s⁻¹ • x ≠ base F (!i) := by
    rw [←hsv']
    exact fun he => hx ((MulAction.injective s⁻¹) he)
  obtain ⟨g,hg,he⟩ := small_suzuki_neighbor_core_transitive h i e T hT
    (hadj ha) (hadj hb) (hne hav) (hne hbv)
  refine ⟨s * g * s⁻¹,?_,?_⟩
  · have hh := mem_map_of_mem (MulAut.conj s).toMonoidHom hg
    rw [←Q_translate F,hsv] at hh
    exact hh
  · rw [mul_smul,mul_smul,he,smul_inv_smul]

/-- Exchange the two Suzuki vertices through their common linear neighbor,
then correct the final vertex by that neighbor's core. All four vertex
images are carried by the same element of the original reduced completion. -/
theorem source_small_suzuki_three_path_exchange
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {z w c : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hwy : w ≠ base (reducedFamily L S) i) (hcz : c ≠ z) :
    ∃ g : G₀ L S, g • z = z ∧ g • w = base (reducedFamily L S) i ∧
      g • base (reducedFamily L S) i = w ∧ g • base (reducedFamily L S) (!i) = c := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hym : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a,ha,ham⟩ := star_locally_transitive h i hyz hym
  have hay : a • y = y := star_le_stabilizer i ha
  have hmw : (graph F).Adj m (a • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr hwz.symm
    change (graph F).Adj (a • z) (a • w) at hh
    rwa [ham] at hh
  have hne : a • w ≠ y := fun he => hwy ((MulAction.injective a) (he.trans hay.symm))
  obtain ⟨u,hum,huw,huy⟩ := linear_neighbor_swap h (!i) eLin hmw hym.symm hne
  let t := a⁻¹ * u * a
  have htz : t • z = z := by
    dsimp only [t]
    rw [mul_smul,mul_smul,ham,hum,inv_smul_eq_iff]
    exact ham.symm
  have htw : t • w = y := by
    dsimp only [t]
    rw [mul_smul,mul_smul,huw,inv_smul_eq_iff]
    exact hay.symm
  have hty : t • y = w := by
    dsimp only [t]
    rw [mul_smul,mul_smul,hay,huy,inv_smul_smul]
  have hwtm : (graph F).Adj w (t • m) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F t).map_adj_iff.mpr hym
    change (graph F).Adj (t • y) (t • m) at hh
    rwa [hty] at hh
  have htmz : t • m ≠ z := by
    rw [←htz]
    exact fun he => hzn ((MulAction.injective t) he).symm
  have htype : w.type = i := by
    have hz : z.type = !i := Bool.eq_not_iff.mpr hyz.1.symm
    exact (Bool.eq_not_iff.mpr hwz.1).trans (by rw [hz,Bool.not_not])
  obtain ⟨r,hr,he⟩ := small_suzuki_neighbor_core_transitive_at h i eSuz T hT htype hwz hwtm hwc htmz hcz
  have hrfix {v : Vertex F} (hv : (graph F).Adj z v) : r • v = v :=
    (source_Z_Q_U (reduced_triple h) z).2 hr v ((mem_ball_one F z v).mpr (.inl hv))
  refine ⟨r * t,?_,?_,?_,?_⟩
  · rw [mul_smul,htz]
    exact Q_le_stabilizer F z hr
  · rw [mul_smul,htw]
    exact hrfix hyz.symm
  · rw [mul_smul,hty]
    exact hrfix hwz.symm
  · rw [mul_smul,he]

/-- The two literal second indices on the two sides of the middle edge
are equal; no path-transitivity or extra numerical premise is assumed. -/
theorem source_small_suzuki_second_index_exchange
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {z w c : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hwy : w ≠ base (reducedFamily L S) i) (hcz : c ≠ z) :
    let F := reducedFamily L S
    (Q F c).relIndex (V F (base F i) 1 ⊓ Q F w) =
      (Q F (base F (!i))).relIndex (V F w 1 ⊓ Q F (base F i)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  obtain ⟨g,_,hgw,hgy,hgm⟩ := source_small_suzuki_three_path_exchange h i eSuz eLin T hT
    hyz hwz hwc hzn hwy hcz
  have he := relIndex_map_map_of_injective (Q F (base F (!i))) (V F w 1 ⊓ Q F (base F i))
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rwa [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←Q_translate F,←Q_translate F,
    ←V_translate F,hgw,hgy,hgm] at he

/-- The nontrivial source intersection commutator moves the center of
 every other neighbor. The middle core normalizes the intersection and
 transports the first moved center to the selected one. -/
theorem source_small_suzuki_intersection_moves_other_center
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {w z : Vertex (reducedFamily L S)}
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) w 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) :
    ⁅V (reducedFamily L S) w 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      Z (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≠ ⊥ := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let W := V F w 1 ⊓ Q F (base F i)
  obtain ⟨hN,u,hu,huz,hmove,_,_,_⟩ := source_intersection_moved_neighbor h hb hwz hyz hbranch
  have hym : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨r,hr,hrm⟩ := small_suzuki_neighbor_core_transitive_at h i eSuz T hT rfl hyz hu hym huz hzn.symm
  have heW : W.map (MulAut.conj r).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp (hN hr)
  have hne : (⁅W,Z F u⁆ : Subgroup (G₀ L S)).map (MulAut.conj r).toMonoidHom ≠ ⊥ := by
    intro he
    exact hmove ((map_eq_bot_iff_of_injective _ (MulAut.conj r).injective).mp he)
  rw [map_commutator,heW,←Z_translate F,hrm] at hne
  exact hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
