module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootActions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.MarkingConstruction.PermutationGeometry
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

/-!
# Compatible marking of Held's symmetric seven-point extension

Inside the given S₇, the actual S₆ extension of A has order 720, so it is
a point stabilizer. The marked involutions form a three-edge path and
a disjoint edge: their commutation relations follow from the six-point
data and their distinctions from the faithful centralizer coordinates.
A single permutation labels these six endpoints and the fixed letter.

The A₆ image lies in the even part of the S₆ image. Their orders and the
marked odd transposition force equality, so the construction preserves
both the A₇ image and the even point stabilizer. No compatibility between
the initially supplied A₆ and S₆ equivalences is assumed.

Source: D. Held, *A Characterization of some multiply transitive permutation
groups, I*, Illinois J. Math. 13 (1969), Lemma 5.11, printed p.238,
DOI 10.1215/ijm/1256053756. The transposition conclusion of 5.10 is supplied
explicitly by `RootGeometry`; its construction belongs to the source assembly.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

noncomputable section

namespace MarkingConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (R : RootGeometry D e L)

local notation "P" => R.W ⊔ zpowers (mu' D e)
local notation "B" => L.A ⊔ zpowers (mu' D e)

private abbrev six_le : B ≤ P := sup_le_sup_right R.A_le _

private def sixImage : Subgroup (Perm (Fin 7)) :=
  ((L.A ⊔ zpowers (mu' D e)).subgroupOf P).map R.symmetricEquiv.toMonoidHom

private def sixEvenImage : Subgroup (Perm (Fin 7)) :=
  (L.A.subgroupOf P).map R.symmetricEquiv.toMonoidHom

private theorem sixImage_card : Nat.card (sixImage D e L R) = 720 := by
  rw [sixImage, card_map_of_injective R.symmetricEquiv.injective]
  rw [Nat.card_congr (subgroupOfEquivOfLe (six_le D e L R)).toEquiv]
  rw [Nat.card_congr L.symmetricEquiv.toEquiv, Nat.card_perm]
  norm_num [Nat.factorial]

private theorem sixEvenImage_card : Nat.card (sixEvenImage D e L R) = 360 := by
  rw [sixEvenImage, card_map_of_injective R.symmetricEquiv.injective]
  rw [Nat.card_congr (subgroupOfEquivOfLe (R.A_le.trans le_sup_left)).toEquiv]
  rw [Nat.card_congr L.alternatingEquiv.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem sixEvenImage_le : sixEvenImage D e L R ≤
    sixImage D e L R ⊓ alternatingGroup (Fin 7) := by
  rintro p ⟨x, hx, rfl⟩
  refine ⟨⟨x, show (x : G) ∈ B from (show L.A ≤ B from le_sup_left) hx, rfl⟩, ?_⟩
  change x ∈ (alternatingGroup (Fin 7)).comap R.symmetricEquiv.toMonoidHom
  rw [R.even_subgroup]
  exact R.A_le hx

private def ambientMark (i : Fin 4) : G :=
  ![mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e] i

private theorem ambientMark_mem_six (i : Fin 4) : ambientMark D e L i ∈ B := by
  have ha : mu' D e ∈ B := (show zpowers (mu' D e) ≤ B from le_sup_right) (mem_zpowers _)
  fin_cases i
  · exact ha
  · exact mul_mem ((show L.A ≤ B from le_sup_left) L.v_mem) ha
  · exact mul_mem ((show L.A ≤ B from le_sup_left) L.pi_mu_mem) ha
  · change xi D e ∈ B
    have h := mul_mem ha ((show L.A ≤ B from le_sup_left) L.mu'_xi_mem)
    simpa only [ambientMark, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.cons_val_one, Matrix.cons_val_zero, ← mul_assoc, ← pow_two,
      element_square D e 2 (by decide), one_mul] using h

private def mark (i : Fin 4) : Perm (Fin 7) :=
  R.symmetricEquiv ⟨ambientMark D e L i, six_le D e L R (ambientMark_mem_six D e L i)⟩

private theorem mark_mem_sixImage (i : Fin 4) : mark D e L R i ∈ sixImage D e L R :=
  ⟨_, ambientMark_mem_six D e L i, rfl⟩

private theorem mark_isSwap (i : Fin 4) : (mark D e L R i).IsSwap := by
  apply R.transpositions
  fin_cases i <;> simp [ambientMark]

private theorem ambientMark_not_commute_01 :
    ¬ Commute (ambientMark D e L 0) (ambientMark D e L 1) := by
  change ¬ Commute (mu' D e) (L.v * mu' D e)
  intro h
  have hs : mu' D e * mu' D e = 1 := by
    simpa only [pow_two] using element_square D e 2 (by decide)
  have hv : L.v⁻¹ = L.v := by
    calc
      _ = mu' D e * L.v * mu' D e := L.mu'_v.symm
      _ = L.v := by simpa only [mul_assoc, hs, mul_one] using h.eq
  have hv2 : L.v ^ 2 = 1 := by simpa only [pow_two, hv] using inv_mul_cancel L.v
  have hdiv := orderOf_dvd_of_pow_eq_one hv2
  rw [L.v_order] at hdiv
  norm_num at hdiv

private theorem ambientMark_not_commute_12 :
    ¬ Commute (ambientMark D e L 1) (ambientMark D e L 2) := by
  intro h
  have h' := h.map (MulAut.conj (crossingConjugator D e))
  change Commute ((MulAut.conj (crossingConjugator D e)) (L.v * mu' D e))
    ((MulAut.conj (crossingConjugator D e)) (pi D e * mu D e * mu' D e)) at h'
  rw [crossingConjugator_first D e L, crossingConjugator_middle D e] at h'
  exact ambientMark_not_commute_01 D e L h'.symm

private theorem ambientMark_commute_02 :
    Commute (ambientMark D e L 0) (ambientMark D e L 2) :=
  ((commute_pi D e 2).symm.mul_right (mu_commute_mu' D e).symm).mul_right (.refl _)

private theorem ambientMark_commute_03 :
    Commute (ambientMark D e L 0) (ambientMark D e L 3) := mu'_commute_xi D e

private theorem ambientMark_commute_13 :
    Commute (ambientMark D e L 1) (ambientMark D e L 3) :=
  L.v_xi_commute.mul_left (mu'_commute_xi D e)

private theorem ambientMark_commute_23 :
    Commute (ambientMark D e L 2) (ambientMark D e L 3) :=
  ((commute_pi D e 7).mul_left (mu_commute_xi D e)).mul_left (mu'_commute_xi D e)

private theorem ambientMark_ne_02 : ambientMark D e L 0 ≠ ambientMark D e L 2 := by
  intro h
  have hm : modelElement 2 = modelElement 0 * modelElement 1 * modelElement 2 := by
    apply D.a10ModelEmbedding_injective e
    simpa [ambientMark, element, map_mul] using h
  exact (by decide +kernel : modelElement 2 ≠ modelElement 0 * modelElement 1 * modelElement 2) hm

private theorem ambientMark_ne_03 : ambientMark D e L 0 ≠ ambientMark D e L 3 := by
  intro h
  have hm : modelElement 2 = modelElement 7 := D.a10ModelEmbedding_injective e h
  exact (by decide +kernel : modelElement 2 ≠ modelElement 7) hm

private theorem ambientMark_ne_23 : ambientMark D e L 2 ≠ ambientMark D e L 3 := by
  intro h
  have hm : modelElement 0 * modelElement 1 * modelElement 2 = modelElement 7 := by
    apply D.a10ModelEmbedding_injective e
    simpa [ambientMark, element, map_mul] using h
  exact (by decide +kernel : modelElement 0 * modelElement 1 * modelElement 2 ≠ modelElement 7) hm

private def toAmbient : Perm (Fin 7) →* G := (P).subtype.comp R.symmetricEquiv.symm.toMonoidHom

private theorem toAmbient_injective : Function.Injective (toAmbient D e L R) :=
  Subtype.val_injective.comp R.symmetricEquiv.symm.injective

@[simp] private theorem toAmbient_mark (i : Fin 4) :
    toAmbient D e L R (mark D e L R i) = ambientMark D e L i := by
  exact congrArg Subtype.val (R.symmetricEquiv.symm_apply_apply _)

private theorem sixEvenImage_eq : sixEvenImage D e L R =
    sixImage D e L R ⊓ alternatingGroup (Fin 7) := by
  let H := sixImage D e L R
  let C := H ⊓ alternatingGroup (Fin 7)
  have hc : C ≤ H := inf_le_left
  have hi0 : C.relIndex H ≠ 0 := (C.subgroupOf H).index_ne_zero_of_finite
  have hi1 : C.relIndex H ≠ 1 := by
    intro h
    have ht := (Subgroup.relIndex_eq_one.mp h) (mark_mem_sixImage D e L R 0)
    have hs := (mark_isSwap D e L R 0).sign_eq
    have he : Equiv.Perm.sign (mark D e L R 0) = 1 := ht.2
    rw [hs] at he
    contradiction
  have hi : 2 ≤ C.relIndex H := by omega
  have hcard := (C.subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv] at hcard
  change Nat.card C * C.relIndex H = Nat.card H at hcard
  rw [show Nat.card H = 720 from sixImage_card D e L R] at hcard
  apply eq_of_le_of_card_ge (sixEvenImage_le D e L R)
  rw [sixEvenImage_card]
  change Nat.card C ≤ 360
  nlinarith

private theorem compatible_labels : ∃ (x : Fin 7) (p : Perm (Fin 7)),
    sixImage D e L R = MulAction.stabilizer (Perm (Fin 7)) x ∧ p 6 = x ∧
    MulAut.conj p (swap 0 1) = mark D e L R 0 ∧
    MulAut.conj p (swap 1 2) = mark D e L R 1 ∧
    MulAut.conj p (swap 2 3) = mark D e L R 2 ∧
    MulAut.conj p (swap 4 5) = mark D e L R 3 := by
  obtain ⟨x, hx⟩ := exists_stabilizer_of_card_eq_720 _ (sixImage_card D e L R)
  have hfix (i : Fin 4) : mark D e L R i x = x := by
    have h := mark_mem_sixImage D e L R i
    rw [hx] at h
    exact h
  have hc (i j : Fin 4) : Commute (mark D e L R i) (mark D e L R j) ↔
      Commute (ambientMark D e L i) (ambientMark D e L j) := by
    rw [← toAmbient_mark D e L R i, ← toAmbient_mark D e L R j]
    exact (commute_map_iff (toAmbient_injective D e L R)).symm
  have hn (i j : Fin 4) : mark D e L R i = mark D e L R j ↔
      ambientMark D e L i = ambientMark D e L j := by
    rw [← toAmbient_mark D e L R i, ← toAmbient_mark D e L R j]
    exact (toAmbient_injective D e L R).eq_iff.symm
  obtain ⟨p, hp⟩ := simultaneous_labels
    (mark D e L R 0) (mark D e L R 1) (mark D e L R 2) (mark D e L R 3) x
    (mark_isSwap D e L R 0) (mark_isSwap D e L R 1)
    (mark_isSwap D e L R 2) (mark_isSwap D e L R 3)
    (fun h => ambientMark_not_commute_01 D e L ((hc 0 1).mp h))
    (fun h => ambientMark_not_commute_12 D e L ((hc 1 2).mp h))
    ((hc 0 2).mpr (ambientMark_commute_02 D e L))
    ((hc 0 3).mpr (ambientMark_commute_03 D e L))
    ((hc 1 3).mpr (ambientMark_commute_13 D e L))
    ((hc 2 3).mpr (ambientMark_commute_23 D e L))
    (fun h => ambientMark_ne_02 D e L ((hn 0 2).mp h))
    (fun h => ambientMark_ne_03 D e L ((hn 0 3).mp h))
    (fun h => ambientMark_ne_23 D e L ((hn 2 3).mp h))
    (hfix 0) (hfix 1) (hfix 2) (hfix 3)
  exact ⟨x, p, hx, hp⟩

private theorem toAmbient_map_image (H : Subgroup G) (hH : H ≤ P) :
    ((H.subgroupOf P).map R.symmetricEquiv.toMonoidHom).map (toAmbient D e L R) = H := by
  ext g
  constructor
  · rintro ⟨s, ⟨x, hx, rfl⟩, rfl⟩
    change (x : G) ∈ H at hx
    simpa only [toAmbient, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      R.symmetricEquiv.symm_apply_apply, Subgroup.coe_subtype] using hx
  · intro hg
    refine ⟨R.symmetricEquiv ⟨g, hH hg⟩, ⟨⟨g, hH hg⟩, hg, rfl⟩, ?_⟩
    exact congrArg Subtype.val (R.symmetricEquiv.symm_apply_apply _)

private theorem toAmbient_even : (alternatingGroup (Fin 7)).map (toAmbient D e L R) = R.W := by
  rw [toAmbient, ← map_map, map_equiv_eq_comap_symm', MulEquiv.symm_symm,
    R.even_subgroup, map_subgroupOf_eq_of_le le_sup_left]

end MarkingConstruction

open MarkingConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (R : RootGeometry D e L)

local notation "P" => R.W ⊔ zpowers (mu' D e)

/-- Choose all seven letters compatibly with the given S₆ subgroup and the
four transpositions of Held 5.10. Both alternating subgroup images are preserved. -/
public theorem exists_sevenMarking : Nonempty (SevenMarking D e L R) := by
  obtain ⟨x, p, hx, hp, h0, h1, h2, h3⟩ := compatible_labels D e L R
  let f := (toAmbient D e L R).comp (MulAut.conj p).toMonoidHom
  have hstab : (MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)).map
      (MulAut.conj p).toMonoidHom = sixImage D e L R := by
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    change MulAction.stabilizer (Perm (Fin 7)) (p 6) = _
    rw [hp, hx]
  have heven : (alternatingGroup (Fin 7)).map (MulAut.conj p).toMonoidHom =
      alternatingGroup (Fin 7) := Subgroup.Normal.map_conj_eq _ p
  refine ⟨{
    embedding := f
    injective := (toAmbient_injective D e L R).comp (MulAut.conj p).injective
    range := ?_
    even_range := ?_
    six_range := ?_
    six_even_range := ?_
    mark_mu' := ?_
    mark_v_mu' := ?_
    mark_pi_mu_mu' := ?_
    mark_xi := ?_ }⟩
  · dsimp only [f]
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulAut.conj p).surjective, ← MonoidHom.range_eq_map]
    change ((P).subtype.comp R.symmetricEquiv.symm.toMonoidHom).range = P
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr R.symmetricEquiv.symm.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · dsimp only [f]
    rw [← map_map, heven, toAmbient_even]
  · dsimp only [f]
    rw [← map_map, hstab]
    exact toAmbient_map_image D e L R _ (six_le D e L R)
  · dsimp only [f]
    rw [← map_map, map_inf _ _ _ (MulAut.conj p).injective,
      heven, hstab, inf_comm, ← sixEvenImage_eq]
    exact toAmbient_map_image D e L R _ (R.A_le.trans le_sup_left)
  · change toAmbient D e L R (MulAut.conj p (swap 0 1)) = _
    rw [h0, toAmbient_mark]; rfl
  · change toAmbient D e L R (MulAut.conj p (swap 1 2)) = _
    rw [h1, toAmbient_mark]; rfl
  · change toAmbient D e L R (MulAut.conj p (swap 2 3)) = _
    rw [h2, toAmbient_mark]; rfl
  · change toAmbient D e L R (MulAut.conj p (swap 4 5)) = _
    rw [h3, toAmbient_mark]; rfl

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
