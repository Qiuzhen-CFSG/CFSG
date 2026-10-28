module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# Source relative-normalizer orbits at the midpoint

The actual actor `G_c ∩ N(Q_b)` has the full plane-stabilizer image in the
compatible natural-module marking. The edge layer splits as its natural
plane and its full central fixed summand. A retained fixed line makes the
noncentral source plane have one-dimensional image modulo that summand.

Two explicit binary-plane actors move this image to the other two lines;
their lifted source conjugates generate the edge layer modulo the fixed
summand. A third actor moves the source plane and fixes a nonidentity natural
point, giving fixed index at most two on the entire edge layer. The lifted
element need not itself have order two. These witnesses feed the retained-line
comparison and reversed-pair argument for midpoint centrality.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation on printed p.881 and the second (4.6.6), pp.903--904.
-/

public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.SourceOrbit.Internal

private def cycle : SL := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

private def involution : Fin 3 → SL := ![
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩,
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide⟩]

private theorem cycle_mem : cycle ∈ planeStabilizer standardPlane := by
  rw [mem_planeStabilizer_iff]
  decide +kernel

private theorem involution_mem (i : Fin 3) :
    involution i ∈ planeStabilizer standardPlane := by
  rw [mem_planeStabilizer_iff]
  fin_cases i <;> decide +kernel

/-- The two conjugates different from the original vector generate the
whole plane. This is exactly the quotient calculation for the two distinct
conjugate planes, modulo the fixed summand. -/
private theorem moved_vectors_cover : ∀ v : Space,
    v ∈ standardPlane → v ≠ 1 →
      modelAction cycle v ≠ v ∧ modelAction (cycle ^ 2) v ≠ v ∧
      ∀ w : Space, w ∈ standardPlane →
        w = 1 ∨ w = modelAction cycle v ∨ w = modelAction (cycle ^ 2) v ∨
          w = modelAction cycle v * modelAction (cycle ^ 2) v := by
  decide +kernel

private theorem exists_moving_with_fixed_point : ∀ u : Space,
    u ∈ standardPlane → u ≠ 1 →
      ∃ i : Fin 3, ∃ v : Space, v ∈ standardPlane ∧ v ≠ 1 ∧
        modelAction (involution i) u ≠ u ∧ modelAction (involution i) v = v := by
  decide +kernel

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.SourceOrbit.Internal

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.SourceOrbit.Internal
variable {G : Type*} [Group G]

/-- An order-four plane with a retained fixed line has index two over its
intersection with the fixed summand. The rest of that summand is arbitrary. -/
private theorem fixed_summand_relIndex_two
    (P F S : Subgroup G) (hP : Nat.card P = 4) (hS : Nat.card S = 2)
    (hSP : S ≤ P) (hSF : S ≤ F) (hnot : ¬ P ≤ F) : F.relIndex P = 2 := by
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; decide)
  have hsmall : 2 ≤ Nat.card (F.subgroupOf P) := by
    have h := card_le_of_le (show S.subgroupOf P ≤ F.subgroupOf P from
      subgroupOf_mono P hSF)
    rw [Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv, hS] at h
    exact h
  have hmul := (F.subgroupOf P).index_mul_card
  rw [hP] at hmul
  have hzero : F.relIndex P ≠ 0 := (F.subgroupOf P).index_ne_zero_of_finite
  have hone : F.relIndex P ≠ 1 := fun h => hnot (relIndex_eq_one.mp h)
  change F.relIndex P * Nat.card (F.subgroupOf P) = 4 at hmul
  have hi2 : 2 ≤ F.relIndex P := by omega
  nlinarith

/-- Moving the natural component moves the full plane, including its
possibly nonzero graph component in the fixed summand. -/
private theorem plane_moved_of_component_moved
    (W F P : Subgroup G) (hdisj : Disjoint W F) (hindex : F.relIndex P = 2)
    (a : G ≃* G) (hW : W.map a.toMonoidHom = W)
    (hF : ∀ f ∈ F, a f = f)
    (w f : G) (hw : w ∈ W) (hf : f ∈ F) (hx : w * f ∈ P)
    (hxnot : w * f ∉ F) (hmove : a w ≠ w) : P.map a.toMonoidHom ≠ P := by
  intro heq
  have hay : a (w * f) ∈ P := heq ▸ mem_map_of_mem a.toMonoidHom hx
  have haynot : a (w * f) ∉ F := by
    intro hy
    have hh := hF _ hy
    have hfix := a.injective hh
    exact hxnot (hfix ▸ hy)
  have hdiff : a (w * f) * (w * f)⁻¹ ∈ F := by
    exact (F.subgroupOf P).mul_mem_iff_of_index_two hindex
      (a := ⟨a (w * f), hay⟩) (b := ⟨(w * f)⁻¹, P.inv_mem hx⟩) |>.mpr (by
        simp only [mem_subgroupOf, inv_mem_iff, haynot, hxnot])
  have he : a (w * f) * (w * f)⁻¹ = a w * w⁻¹ := by
    rw [map_mul, hF f hf, _root_.mul_inv_rev]
    group
  rw [he] at hdiff
  have haw : a w ∈ W := hW ▸ mem_map_of_mem a.toMonoidHom hw
  have h1 := disjoint_def.mp hdisj (W.mul_mem haw (W.inv_mem hw)) hdiff
  exact hmove (mul_inv_eq_one.mp h1)

/-- Once two moved natural components span W, the corresponding full
planes span E modulo the unchanged central summand. -/
private theorem two_plane_sup_fixed_eq
    (E W F P : Subgroup G) (hEF : E = W ⊔ F) (hPE : P ≤ E)
    (a b : G ≃* G) (haE : E.map a.toMonoidHom = E) (hbE : E.map b.toMonoidHom = E)
    (haF : ∀ f ∈ F, a f = f) (hbF : ∀ f ∈ F, b f = f)
    (w f : G) (_hw : w ∈ W) (hf : f ∈ F) (hx : w * f ∈ P)
    (hspan : ∀ u ∈ W, u = 1 ∨ u = a w ∨ u = b w ∨ u = a w * b w) :
    P.map a.toMonoidHom ⊔ P.map b.toMonoidHom ⊔ F = E := by
  let J := P.map a.toMonoidHom ⊔ P.map b.toMonoidHom ⊔ F
  have hFJ : F ≤ J := le_sup_right
  have haw : a w ∈ J := by
    have hh : a (w * f) ∈ J :=
      (show P.map a.toMonoidHom ≤ J from le_sup_left.trans le_sup_left)
        (mem_map_of_mem a.toMonoidHom hx)
    have hh' := J.mul_mem hh (J.inv_mem (hFJ hf))
    simpa only [map_mul, haF f hf, mul_inv_cancel_right] using hh'
  have hbw : b w ∈ J := by
    have hh : b (w * f) ∈ J :=
      (show P.map b.toMonoidHom ≤ J from le_sup_right.trans le_sup_left)
        (mem_map_of_mem b.toMonoidHom hx)
    have hh' := J.mul_mem hh (J.inv_mem (hFJ hf))
    simpa only [map_mul, hbF f hf, mul_inv_cancel_right] using hh'
  apply le_antisymm
  · exact sup_le (sup_le
      (by simpa only [haE] using map_mono (f := a.toMonoidHom) hPE)
      (by simpa only [hbE] using map_mono (f := b.toMonoidHom) hPE))
      (by rw [hEF]; exact le_sup_right)
  · rw [hEF]
    refine sup_le ?_ hFJ
    intro u hu
    rcases hspan u hu with rfl | rfl | rfl | rfl
    · exact J.one_mem
    · exact haw
    · exact hbw
    · exact J.mul_mem haw hbw

/-- A fixed nonidentity natural point bounds the fixed index on the full
edge layer; the arbitrarily large central fixed summand cancels. -/
private theorem fixed_index_le_two_of_fixed_component
    (E W F : Subgroup G) [Finite E] [IsMulCommutative E]
    (hEF : E = W ⊔ F) (hWcard : Nat.card W = 4)
    (h : G) (hF : F ≤ centralizer ({h} : Set G))
    (w : G) (hw : w ∈ W) (hw1 : w ≠ 1) (hwh : Commute w h) :
    (centralizer ({h} : Set G)).relIndex E ≤ 2 := by
  let C := centralizer ({h} : Set G)
  have hWE : W ≤ E := by rw [hEF]; exact le_sup_left
  have hFE : F ≤ E := by rw [hEF]; exact le_sup_right
  let : Finite W := Finite.of_injective (inclusion hWE) (inclusion_injective _)
  let WE := W.subgroupOf E
  let CE := C.subgroupOf E
  have hgen : WE ⊔ CE = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ (W.subgroupOf E) ⊔ F.subgroupOf E := by
      rw [← subgroupOf_sup hWE hFE, ← hEF, subgroupOf_self]
      trivial
    exact sup_le le_sup_left ((subgroupOf_mono E hF).trans le_sup_right) hx
  have hindex := relIndex_sup_right WE CE
  rw [hgen, relIndex_top_right, relIndex_subgroupOf hWE] at hindex
  change C.relIndex E = C.relIndex W at hindex
  rw [hindex]
  have hne : C.subgroupOf W ≠ ⊥ := by
    intro hz
    have hm : (⟨w, hw⟩ : W) ∈ C.subgroupOf W :=
      mem_centralizer_singleton_iff.mpr hwh
    rw [hz] at hm
    exact hw1 (congrArg Subtype.val hm)
  have hcard : 2 ≤ Nat.card (C.subgroupOf W) :=
    (one_lt_card_iff_ne_bot _).mpr hne
  have hmul := (C.subgroupOf W).index_mul_card
  rw [hWcard] at hmul
  change C.relIndex W * Nat.card (C.subgroupOf W) = 4 at hmul
  nlinarith

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.SourceOrbit.Internal

open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.SourceOrbit

open Initial
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual distance-four edge image is the pointwise fixer of its
natural plane. No earlier Counterexample or LocalControl is assumed. -/
private theorem edge_actorImage_eq_planeFixer
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b)
    (model : LocalModel c) :
    model.actorImage (Q R b) =
      planeFixer (model.coordinates (⁅Z R c, Q R b⁆)) := by
  have hloc : Q R b ≤ stabilizer R c :=
    fun _ hx => hx.2 c (adjacent_symm R hcb)
  have hU := edge_commutator_le_natural common c b hc hcb
  have hcentral : ⁅Z R c, Q R b⁆ ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
    have hz := edge.edge_commutator_le_Z c b hc hcb
    rw [edge_Z_eq_fixed common c b hc hcb] at hz
    exact hz.trans inf_le_right
  have hle : model.actorImage (Q R b) ≤
      planeFixer (model.coordinates (⁅Z R c, Q R b⁆)) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨u, hu, rfl⟩
    exact (model.action_fixed_iff g u).mpr (hcentral hu g hg)
  apply eq_of_le_of_card_ge hle
  rw [model.actorImage_card _ hloc, edge.edge_Q_index c b hc hcb,
    planeFixer_card _ (by
      rw [model.coordinates_card _ hU, edge.edge_commutator_card c b hc hcb])]

/-- Exact preimage of the source edge kernel in the compatible marking. -/
private theorem edge_planeFixer_comap
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b)
    (model : LocalModel c) :
    (planeFixer (model.coordinates (⁅Z R c, Q R b⁆))).comap model.projection =
      (Q R b).subgroupOf (stabilizer R c) := by
  rw [← edge_actorImage_eq_planeFixer common edge c b hc hcb model]
  apply model.actorImage_comap
  apply Q_le_adjacent_h R _ hcb
  have hn := adjacent_color_ne R hcb
  cases hb : color R b <;> simp_all

/-- The literal source relative normalizer is the inverse image of the
full plane stabilizer, with the local kernel retained. -/
private theorem relativeNormalizer_comap
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b)
    (model : LocalModel c) :
    (planeStabilizer (model.coordinates (⁅Z R c, Q R b⁆))).comap
        model.projection =
      (stabilizer R c ⊓ normalizer (Q R b : Set (FreeAmalgam R))).subgroupOf
        (stabilizer R c) := by
  have hcard : Nat.card (model.coordinates (⁅Z R c, Q R b⁆)) = 4 := by
    rw [model.coordinates_card _ (edge_commutator_le_natural common c b hc hcb),
      edge.edge_commutator_card c b hc hcb]
  rw [← planeFixer_normalizer _ hcard,
    comap_normalizer_eq_of_surjective _ model.surjective,
    edge_planeFixer_comap common edge c b hc hcb model,
    inf_subgroupOf_left, subgroupOf_normalizer_eq
      (show Q R b ≤ stabilizer R c from
        fun _ hx => hx.2 c (adjacent_symm R hcb))]

/-- Every matrix in the plane stabilizer lifts to the actual source actor. -/
private theorem relativeNormalizer_actorImage
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b)
    (model : LocalModel c) :
    model.actorImage (stabilizer R c ⊓ normalizer (Q R b : Set (FreeAmalgam R))) =
      planeStabilizer (model.coordinates (⁅Z R c, Q R b⁆)) := by
  rw [LocalModel.actorImage, ← relativeNormalizer_comap common edge c b hc hcb model]
  exact map_comap_eq_self_of_surjective model.surjective _

/-- Right-conjugation form of the actual actor lift. -/
private theorem exists_relative_actor
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b)
    (model : LocalModel c) (s : SL)
    (hs : s ∈ planeStabilizer (model.coordinates (⁅Z R c, Q R b⁆))) :
    ∃ h : FreeAmalgam R,
      h ∈ stabilizer R c ∧ h ∈ normalizer (Q R b : Set (FreeAmalgam R)) ∧
      ∃ hh : h ∈ stabilizer R c, model.projection ⟨h, hh⟩ = s⁻¹ := by
  have hs' : s⁻¹ ∈ model.actorImage
      (stabilizer R c ⊓ normalizer (Q R b : Set (FreeAmalgam R))) := by
    rw [relativeNormalizer_actorImage common edge c b hc hcb model]
    exact inv_mem hs
  obtain ⟨h, hh, he⟩ := hs'
  exact ⟨h, hh.1, hh.2, h.property, he⟩

omit [Finite M] in
private theorem center_le_centralizer (A : Subgroup (FreeAmalgam R)) :
    (center A).map A.subtype ≤ centralizer (A : Set (FreeAmalgam R)) := by
  rintro x ⟨z, hz, rfl⟩ y hy
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)

/-- The actual edge layer splits as its natural plane and its full local
fixed summand. Cardinality is obtained from the already checked index four. -/
private theorem edge_split_fixed
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b) :
    Z R b = ⁅Z R c, Q R b⁆ ⊔
      (Z R b ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
    Disjoint (⁅Z R c, Q R b⁆ : Subgroup (FreeAmalgam R))
      (Z R b ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype) := by
  let E := Z R b
  let W := ⁅Z R c, Q R b⁆
  let F := E ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype
  have hWE : W ≤ E := edge.edge_commutator_le_Z c b hc hcb
  have hFE : F ≤ E := inf_le_left
  have hWc : W ≤ stabilizer R c :=
    (edge_commutator_le_natural common c b hc hcb).trans
      ((U_le_Z c).trans (Z_le_stabilizer R c))
  have hFW : F ≤ centralizer (W : Set (FreeAmalgam R)) :=
    inf_le_right.trans ((center_le_centralizer _).trans (centralizer_le hWc))
  have hd : Disjoint W F := disjoint_iff.mpr (le_bot_iff.mp
    ((inf_le_inf le_rfl inf_le_right).trans
      (edge_plane_inf_center common c b hc hcb).le))
  let := finite_stabilizer R b
  let : Finite E := Finite.of_injective (inclusion (Z_le_stabilizer R b))
    (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion hFE) (inclusion_injective _)
  have hindex : F.relIndex E = 4 := by
    rw [inf_relIndex_left]
    exact edge_center_index common edge c b hc hcb
  have hcardE : Nat.card E = 4 * Nat.card F := by
    have hm := (F.subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hFE).toEquiv] at hm
    exact hm.symm.trans (by rw [show (F.subgroupOf E).index = 4 from hindex])
  have hcard : Nat.card (W ⊔ F : Subgroup (FreeAmalgam R)) = Nat.card E := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint W F
      (hFW.trans (Subgroup.centralizer_le_normalizer _)) hd,
      edge.edge_commutator_card c b hc hcb, hcardE]
  exact ⟨(eq_of_le_of_card_ge (sup_le hWE hFE) hcard.ge).symm, hd⟩

/-- Standard binary coordinates embedded in the actual natural layer,
with every plane actor lifted through the literal source normalizer. -/
private theorem exists_standard_edge_frame
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (c b : Vertex R) (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃ j : Space →* FreeAmalgam R, Function.Injective j ∧
      standardPlane.map j = ⁅Z R c, Q R b⁆ ∧
      ∀ s ∈ planeStabilizer standardPlane,
        ∃ h : FreeAmalgam R, h ∈ stabilizer R c ∧
          h ∈ normalizer (Q R b : Set (FreeAmalgam R)) ∧
          ∀ v : Space, (MulAut.conj h⁻¹) (j v) = j (modelAction s v) := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) c hc
  let W := ⁅Z R c, Q R b⁆
  have hWU : W ≤ U R c := edge_commutator_le_natural common c b hc hcb
  have hcard : Nat.card (model.coordinates W) = 4 := by
    rw [model.coordinates_card W hWU, edge.edge_commutator_card c b hc hcb]
  obtain ⟨a, ha⟩ := plane_transitive (model.coordinates W) hcard
  have ha' : standardPlane.map (modelAction a).toMonoidHom = model.coordinates W := ha
  let j : Space →* FreeAmalgam R := (U R c).subtype.comp
    (model.equiv.symm.toMonoidHom.comp (modelAction a).toMonoidHom)
  have hj : Function.Injective j := (U R c).subtype_injective.comp
    (model.equiv.symm.injective.comp (modelAction a).injective)
  have hjW : standardPlane.map j = W := by
    change standardPlane.map ((U R c).subtype.comp
      (model.equiv.symm.toMonoidHom.comp (modelAction a).toMonoidHom)) = W
    have he : model.equiv.symm.toMonoidHom.comp model.equiv.toMonoidHom =
        MonoidHom.id (U R c) := by ext x; simp
    have hback : (model.coordinates W).map model.equiv.symm.toMonoidHom =
        W.subgroupOf (U R c) := by
      rw [LocalModel.coordinates, Subgroup.map_map, he, Subgroup.map_id]
    rw [← Subgroup.map_map, ← Subgroup.map_map, ha', hback,
      map_subgroupOf_eq_of_le hWU]
  refine ⟨j, hj, hjW, ?_⟩
  intro s hs
  have hsa : MulAut.conj a s ∈ planeStabilizer (model.coordinates W) := by
    rw [← ha, planeStabilizer_move]
    exact mem_map_of_mem (MulAut.conj a).toMonoidHom hs
  obtain ⟨h, hhc, hhQ, hhc', hp⟩ :=
    exists_relative_actor common edge c b hc hcb model (MulAut.conj a s) hsa
  refine ⟨h, hhc, hhQ, ?_⟩
  intro v
  let u := model.equiv.symm (modelAction a v)
  let z : U R c := (U R c).normalizerMonoidHom
    ⟨h⁻¹, U_normalized c ((stabilizer R c).inv_mem hhc)⟩ u
  have hz := model.action ⟨h⁻¹, (stabilizer R c).inv_mem hhc⟩ u z rfl
  have hi : (⟨h⁻¹, (stabilizer R c).inv_mem hhc⟩ : stabilizer R c) =
      (⟨h, hhc'⟩ : stabilizer R c)⁻¹ := rfl
  rw [hi, map_inv, hp, inv_inv] at hz
  have hz' : model.equiv z = modelAction a (modelAction s v) := by
    rw [hz]
    simp only [u, MulEquiv.apply_symm_apply, action_conj]
  have he : z = model.equiv.symm (modelAction a (modelAction s v)) :=
    model.equiv.injective (hz'.trans (model.equiv.apply_symm_apply _).symm)
  exact congrArg Subtype.val he

omit [Finite M] in
private theorem edge_normalizer_normalizes_Z (b : Vertex R) (hb : color R b = true) :
    normalizer (Q R b : Set (FreeAmalgam R)) ≤ normalizer (Z R b) := by
  have hZ : Z R b = omegaCenter (Q R b) := by
    simp only [Z, hb, Bool.true_eq_false, if_false]
    rfl
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq, hZ,
    ← omegaCenter_map _ _ (MulAut.conj h).injective,
    mem_normalizer_iff_map_conj_eq.mp hh]

omit [Finite M] in
private theorem right_fixes_center
    (c : Vertex R) (h : FreeAmalgam R) (hh : h ∈ stabilizer R c)
    (x : FreeAmalgam R)
    (hx : x ∈ (center (stabilizer R c)).map (stabilizer R c).subtype) :
    (MulAut.conj h⁻¹) x = x := by
  have hc := center_le_centralizer _ hx h hh
  simp only [MulAut.conj_apply, inv_inv]
  rw [mul_assoc, ← hc, inv_mul_cancel_left]

omit [Finite M] in
/-- The source normalizer actor transports the plane even when it moves b. -/
private theorem right_plane_eq (d b : Vertex R) (k : FreeAmalgam R)
    (hk : k ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ⁅Z R (act R k d), Q R b⁆ =
      (⁅Z R d, Q R b⁆).map (MulAut.conj k⁻¹).toMonoidHom := by
  have hq : (Q R b).map (MulAut.conj k⁻¹).toMonoidHom = Q R b :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hk)
  rw [Z_act, map_commutator, hq]

/-- Two nontrivial source conjugates generate the edge layer modulo its
full central fixed summand. A third source actor moves the initial plane
and has fixed index at most two on the entire edge layer. -/
theorem source_orbit_witness
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (d c b : Vertex R) (hd : color R d = false) (hc : color R c = false)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (C : Subgroup (FreeAmalgam R)) (hCcard : Nat.card C = 2)
    (hC : C ≤ ⁅Z R d, Q R b⁆ ⊓
      (center (stabilizer R c)).map (stabilizer R c).subtype)
    (hnot : ¬ ⁅Z R d, Q R b⁆ ≤
      (center (stabilizer R c)).map (stabilizer R c).subtype) :
    ∃ r s h : FreeAmalgam R,
      r ∈ stabilizer R c ∧ r ∈ normalizer (Q R b : Set (FreeAmalgam R)) ∧
      s ∈ stabilizer R c ∧ s ∈ normalizer (Q R b : Set (FreeAmalgam R)) ∧
      h ∈ stabilizer R c ∧ h ∈ normalizer (Q R b : Set (FreeAmalgam R)) ∧
      ⁅Z R (act R r d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆ ∧
      ⁅Z R (act R s d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆ ∧
      (⁅Z R (act R r d), Q R b⁆ ⊔ ⁅Z R (act R s d), Q R b⁆) ⊔
        (Z R b ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype) = Z R b ∧
      ⁅Z R (act R h d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆ ∧
      (centralizer ({h} : Set (FreeAmalgam R))).relIndex (Z R b) ≤ 2 := by
  let E := Z R b
  let W := ⁅Z R c, Q R b⁆
  let F := E ⊓ (center (stabilizer R c)).map (stabilizer R c).subtype
  let P := ⁅Z R d, Q R b⁆
  have hPE : P ≤ E := edge.edge_commutator_le_Z d b hd hdb
  have hWE : W ≤ E := edge.edge_commutator_le_Z c b hc hcb
  have hWc : W ≤ stabilizer R c :=
    (edge_commutator_le_natural common c b hc hcb).trans
      ((U_le_Z c).trans (Z_le_stabilizer R c))
  obtain ⟨hEF, hdisj⟩ := edge_split_fixed common edge c b hc hcb
  change E = W ⊔ F at hEF
  change Disjoint W F at hdisj
  have hCF : C ≤ F := le_inf ((hC.trans inf_le_left).trans hPE)
    (hC.trans inf_le_right)
  have hnotPF : ¬ P ≤ F := fun hh => hnot (hh.trans inf_le_right)
  have hindex : F.relIndex P = 2 :=
    Internal.fixed_summand_relIndex_two P F C
      (edge.edge_commutator_card d b hd hdb) hCcard (hC.trans inf_le_left) hCF hnotPF
  obtain ⟨x, hxP, hxnot⟩ := SetLike.not_le_iff_exists.mp hnotPF
  have hWF : W ≤ normalizer (F : Set (FreeAmalgam R)) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply le_centralizer_iff.mpr
    exact fun f hf w hw => center_le_centralizer _ hf.2 w (hWc hw)
  have hxEF : x ∈ W ⊔ F := hEF ▸ hPE hxP
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right W F hWF] at hxEF
  obtain ⟨w, hw, f, hf, rfl⟩ := hxEF
  obtain ⟨j, hj, hjW, hframe⟩ := exists_standard_edge_frame common edge c b hc hcb
  have hwm : w ∈ standardPlane.map j := by rw [hjW]; exact hw
  obtain ⟨u, hu, hju⟩ := hwm
  subst w
  change j u * f ∈ P at hxP
  change j u * f ∉ F at hxnot
  change f ∈ F at hf
  have hu1 : u ≠ 1 := by
    intro hh
    have hj1 : j u = 1 := by rw [hh, map_one]
    apply hxnot
    rw [hj1, one_mul]
    exact hf
  obtain ⟨huCycle, huCycle2, hcover⟩ := Internal.moved_vectors_cover u hu hu1
  obtain ⟨i, v, hv, hv1, humove, hvfix⟩ :=
    Internal.exists_moving_with_fixed_point u hu hu1
  obtain ⟨r, hrc, hrQ, hrj⟩ := hframe Internal.cycle
    Internal.cycle_mem
  obtain ⟨s, hsc, hsQ, hsj⟩ := hframe (Internal.cycle ^ 2)
    (pow_mem Internal.cycle_mem 2)
  obtain ⟨h, hhc, hhQ, hhj⟩ := hframe (Internal.involution i)
    (Internal.involution_mem i)
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hcb
    cases hbool : color R b with
    | false => exact False.elim (hn (hc.trans hbool.symm))
    | true => rfl
  have fixed (k : FreeAmalgam R) (hkc : k ∈ stabilizer R c) :
      ∀ z ∈ F, (MulAut.conj k⁻¹) z = z :=
    fun z hz => right_fixes_center c k hkc z hz.2
  have stableE (k : FreeAmalgam R) (hkQ : k ∈ normalizer (Q R b : Set _)) :
      E.map (MulAut.conj k⁻¹).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp
      (edge_normalizer_normalizes_Z b hb ((normalizer _).inv_mem hkQ))
  have stableW (k : FreeAmalgam R) (hkc : k ∈ stabilizer R c)
      (hkQ : k ∈ normalizer (Q R b : Set _)) :
      W.map (MulAut.conj k⁻¹).toMonoidHom = W := by
    have hz : (Z R c).map (MulAut.conj k⁻¹).toMonoidHom = Z R c :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R c ((stabilizer R c).inv_mem hkc))
    have hq : (Q R b).map (MulAut.conj k⁻¹).toMonoidHom = Q R b :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hkQ)
    change (⁅Z R c, Q R b⁆).map (MulAut.conj k⁻¹).toMonoidHom = ⁅Z R c, Q R b⁆
    rw [map_commutator, hz, hq]
  have hjU : j u ∈ W := by
    change j u ∈ ⁅Z R c, Q R b⁆
    rw [← hjW]
    exact mem_map_of_mem j hu
  have hmover (k : FreeAmalgam R) (hkc : k ∈ stabilizer R c)
      (hkQ : k ∈ normalizer (Q R b : Set _))
      (hm : (MulAut.conj k⁻¹) (j u) ≠ j u) :
      P.map (MulAut.conj k⁻¹).toMonoidHom ≠ P :=
    Internal.plane_moved_of_component_moved W F P hdisj hindex
      (MulAut.conj k⁻¹) (stableW k hkc hkQ) (fixed k hkc)
      (j u) f hjU hf hxP hxnot hm
  have hrmove := hmover r hrc hrQ (by rw [hrj]; exact fun he => huCycle (hj he))
  have hsmove := hmover s hsc hsQ (by rw [hsj]; exact fun he => huCycle2 (hj he))
  have hhmove := hmover h hhc hhQ (by rw [hhj]; exact fun he => humove (hj he))
  have hgen : P.map (MulAut.conj r⁻¹).toMonoidHom ⊔
      P.map (MulAut.conj s⁻¹).toMonoidHom ⊔ F = E := by
    apply Internal.two_plane_sup_fixed_eq E W F P hEF hPE
      (MulAut.conj r⁻¹) (MulAut.conj s⁻¹) (stableE r hrQ) (stableE s hsQ)
      (fixed r hrc) (fixed s hsc) (j u) f hjU hf hxP
    intro z hz
    have hzm : z ∈ standardPlane.map j := by rw [hjW]; exact hz
    obtain ⟨t, ht, rfl⟩ := hzm
    rcases hcover t ht with ht1 | ht2 | ht3 | ht4
    · exact Or.inl (by rw [ht1, map_one])
    · exact Or.inr (Or.inl (by rw [ht2, hrj]))
    · exact Or.inr (Or.inr (Or.inl (by rw [ht3, hsj])))
    · exact Or.inr (Or.inr (Or.inr (by rw [ht4, map_mul, hrj, hsj])))
  have hFcentral : F ≤ centralizer ({h} : Set (FreeAmalgam R)) := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (center_le_centralizer _ hz.2 h hhc).symm
  have hjvW : j v ∈ W := by
    change j v ∈ ⁅Z R c, Q R b⁆
    rw [← hjW]
    exact mem_map_of_mem j hv
  have hjv1 : j v ≠ 1 := fun he => hv1 (hj (he.trans (map_one j).symm))
  have hjvh : Commute (j v) h := by
    have hhfix : (MulAut.conj h⁻¹) (j v) = j v := by rw [hhj, hvfix]
    have he := congrArg (fun z => h * z) hhfix
    change j v * h = h * j v
    simpa only [MulAut.conj_apply, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
      using he
  let := finite_stabilizer R b
  let : Finite E := Finite.of_injective (inclusion (Z_le_stabilizer R b))
    (inclusion_injective _)
  have hZ : Z R b = omegaCenter (Q R b) := by
    simp only [Z, hb, Bool.true_eq_false, if_false]
    rfl
  let : IsElementaryAbelian 2 E := by
    change IsElementaryAbelian 2 (Z R b)
    rw [hZ]
    exact omegaCenter_elementary (Q R b)
  have hsmall := Internal.fixed_index_le_two_of_fixed_component E W F hEF
    (edge.edge_commutator_card c b hc hcb) h hFcentral (j v) hjvW hjv1 hjvh
  refine ⟨r, s, h, hrc, hrQ, hsc, hsQ, hhc, hhQ, ?_, ?_, ?_, ?_, hsmall⟩
  · simpa only [right_plane_eq d b r hrQ] using hrmove
  · simpa only [right_plane_eq d b s hsQ] using hsmove
  · simpa only [right_plane_eq d b r hrQ, right_plane_eq d b s hsQ] using hgen
  · simpa only [right_plane_eq d b h hhQ] using hhmove

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.SourceOrbit
