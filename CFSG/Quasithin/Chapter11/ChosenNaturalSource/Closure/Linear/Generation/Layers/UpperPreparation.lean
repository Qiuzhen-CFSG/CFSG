module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Cartan
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.RecognitionApplications
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Assembly

/-!
# The literal upper-layer actors and quotient preparation

The opposite pair centralizes V: its commutators with V lie in two disjoint
marked points. Faithfulness of the actual starred action therefore places
this pair in the three-conjugate two-core, independently of layer generation.

The structural point-radical theorem is transported along the original star
projection to the root-geometry interface. Its six-root argument then proves
full invariance of S₃. These results construct both quotient actions without
assuming homogeneous coordinates, recognition, or core containment in G₁.
The point residual used below is Chapter 11's solvable residual.

Source: Aschbacher--Smith, 11.5.7, printed p.781, and G.2.5, pp.335--336.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup Matrix
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
  (hUT : E.W ≤ (T : Subgroup G))
  (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
include d hUT hf

/-- The third term of the original series, before its upper quotient is formed. -/
def thirdLayer (E : Geometry D) (x y : G) : Subgroup G := S₃ (setup E) x y

/-- The solvable residual is an actual subgroup of the three-conjugate group. -/
theorem pointResidual_le_threeGroup : E.L₁ ≤ threeGroup E x y :=
  E.L₁_le.trans (d.L_le_I hUT hf)

/-- The original Hall Cartan acts inside the same three-conjugate group. -/
theorem Cartan_le_threeGroup (hX : LocalGeometry.IsCartan T L E.X) :
    E.X ≤ threeGroup E x y :=
  (hX.1.trans inf_le_left).trans (d.L_le_I hUT hf)

/-- The original pair of U-conjugates lies in O₂(I), without a generation premise. -/
theorem oppositePair_le_threeCore : oppositePair E x y ≤ threeCore E x y := by
  have hVconj (a : G) (ha : a ∈ L) :
      V.map (MulAut.conj a⁻¹).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem
      (normalizes_of_span (setup E) d.span_eq ha))
  have hb (a : G) (ha : a ∈ L) :
      ⁅V, ChapterG.Section02.Setup.conjugate E.W a⁆ ≤
        ChapterG.Section02.Setup.conjugate E.V₁ a := by
    have hm := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom)
      (d.commutator_V_U_le_point hUT hf)
    rw [map_commutator] at hm
    change ⁅V.map (MulAut.conj a⁻¹).toMonoidHom,
      ChapterG.Section02.Setup.conjugate E.W a⁆ ≤
      ChapterG.Section02.Setup.conjugate E.V₁ a at hm
    rw [hVconj a ha] at hm
    exact hm
  have hcomm : ⁅V, oppositePair E x y⁆ = ⊥ := by
    apply bot_unique
    apply le_trans (le_inf ((commutator_mono le_rfl inf_le_left).trans (hb x d.g_mem))
      ((commutator_mono le_rfl inf_le_right).trans (hb y d.h_mem)))
    exact (d.third_disjoint.mono_left le_sup_right).eq_bot.le
  have hc : oppositePair E x y ≤ centralizer (V : Set G) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hPI : oppositePair E x y ≤ threeGroup E x y :=
    inf_le_left.trans (le_sup_right.trans le_sup_left)
  intro a ha
  have haI := hPI ha
  have haLT := d.I_le_LT hUT haI
  have hk : (⟨a, haLT⟩ : (setup E).LT) ∈ d.naturalAction.ker := by
    change d.naturalAction ⟨a, haLT⟩ = 1
    apply DFunLike.ext
    intro w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    rw [d.naturalAction_apply]
    change d.coordinates _ = d.coordinates v
    congr 1
    apply Subtype.ext
    change a * (v : G) * a⁻¹ = v
    rw [← hc ha v v.property, mul_inv_cancel_right]
  rw [d.naturalAction_ker] at hk
  change a ∈ S (setup E) x y
  rw [d.S_eq_star_kernel hUT hf]
  exact ⟨haI, ⟨⟨a, haLT⟩, hk, rfl⟩⟩

/-- The full source pair agrees with the pair of core intersections used by
the lower homogeneous model. Both conjugations are the source right action. -/
theorem oppositePair_eq_core_pair :
    oppositePair E x y =
      ChapterG.Section02.Setup.conjugate (W (setup E) x y) x ⊓
        ChapterG.Section02.Setup.conjugate (W (setup E) x y) y := by
  rw [conjugate_W (setup E) x y x ((d.L_le_I hUT hf) d.g_mem),
    conjugate_W (setup E) x y y ((d.L_le_I hUT hf) d.h_mem)]
  apply le_antisymm
  · intro a ha
    have hs := oppositePair_le_threeCore E d hUT hf ha
    exact ⟨⟨ha.1, hs⟩, ⟨ha.2, hs⟩⟩
  · exact fun _ ha => ⟨ha.1.1, ha.2.1⟩

/-- In particular the original opposite pair is already in the third layer. -/
theorem oppositePair_le_thirdLayer : oppositePair E x y ≤ thirdLayer E x y := by
  rw [oppositePair_eq_core_pair E d hUT hf]
  exact le_sup_right

/-- The recognition radical is the image under the original star projection. -/
theorem sourceUpperRadicalIdentification :
    Recognition.Hypothesis.UpperRadicalIdentification d (d.sourceStarComparison hUT hf) := by
  let C := setup E
  let e := d.sourceStarComparison hUT hf
  have himage : (C.U.subgroupOf (I C x y)).map e.projection =
      (C.star C.U).subgroupOf (C.star C.L) := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      change (e.projection i : C.Star) ∈ C.star C.U
      rw [d.sourceStarComparison_projection_apply hUT hf]
      exact ⟨inclusion (d.I_le_LT hUT) i, hi, rfl⟩
    · intro hz
      obtain ⟨u, hu, he⟩ := hz
      let i : I C x y := ⟨u, (le_sup_left.trans le_sup_left : C.U ≤ I C x y) hu⟩
      refine ⟨i, hu, ?_⟩
      rw [d.sourceStarComparison_projection_apply hUT hf]
      exact Subtype.ext he
  change (C.U.subgroupOf (I C x y)).map e.projection = _
  rw [himage]
  apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
  change d.pointRadicalImage = _
  rw [d.pointRadicalImage_eq_radical hUT hf (d.star_U_le_star_L hUT hf)]
  ext z
  rw [mem_map_equiv]
  change ((∀ v ∈ d.point, z.val *ᵥ v = v) ∧
    (∀ v, z.val *ᵥ v - v ∈ d.point)) ↔
    (∀ v, (d.model (d.model.symm z)).val *ᵥ v - v ∈ d.point) ∧
      (∀ v ∈ d.point, (d.model (d.model.symm z)).val *ᵥ v = v)
  rw [d.model.apply_symm_apply]
  exact and_comm

/-- Full invariance of S₃ follows from the six actual frame roots. -/
theorem threeGroup_normalizes_thirdLayer :
    threeGroup E x y ≤ normalizer (thirdLayer E x y : Set G) :=
  Recognition.DualGeometry.I_normalizes_third d hUT hf (d.L_le_I hUT hf)
    (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf x d.g_mem)
    (d.S_normalizes_marked hUT hf y d.h_mem) (d.sourceStarComparison hUT hf)
    (sourceUpperRadicalIdentification E d hUT hf)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
