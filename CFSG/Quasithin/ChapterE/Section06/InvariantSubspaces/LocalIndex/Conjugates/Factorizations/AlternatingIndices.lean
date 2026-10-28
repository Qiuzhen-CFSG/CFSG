module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.Inputs
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Setup
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.ThompsonImage

/-!
# The two alternating-five conjugate-action indices

A noncommuting conjugate Uˣ lies in Baum(R) and is R-normal. Its permutation
image is therefore a nontrivial subgroup of the pair-swap four-group preserved
by the pair exchange. Both remaining possibilities fix exactly four vectors
of U. Applying the same calculation to x⁻¹ and transporting the centralizer
back by x gives |Uˣ:C_{Uˣ}(U)| = 4. The Baumann image itself gives
|S:C_S(U)| = 4, and the defining block-module order supplies the third index.

The conditional assembly uses only the earlier full action and Thompson-image
inputs. It neither assumes factorization nor removes a central layer without
proof: construction of NaturalActionModel remains with its existing owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3),
printed p.155/PDF p.166; C.5.6, R-normal branch, printed p.157/PDF p.168;
B.3.2(4), printed pp.83–84.
-/

public section


open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices
open AlternatingFamily AlternatingFamily.Enumeration Baumann.AlternatingFive
universe u
variable {G : Type u} [Group G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G} {x : G}

private theorem coordinates_module_card (c : ActionCoordinates R L) : Nat.card (U L) = 16 := by
  rw [← c.moduleMap_range,
    ← Nat.card_congr (MonoidHom.ofInjective c.moduleMap_injective).toEquiv]
  exact vector_card

/-- The permutation action computes each actor-centralizer index literally. -/
theorem actor_index (c : ActionCoordinates R L) {B : Subgroup G} (hB : B ≤ R) :
    (centralizer (U L : Set G)).relIndex B = Nat.card (actionImage c.action B) := by
  have hk : c.action.ker = (centralizer (U L : Set G)).subgroupOf R := by
    ext r
    exact c.kernel r
  calc
    (centralizer (U L : Set G)).relIndex B =
        (centralizer (U L : Set G)).relIndex ((B.subgroupOf R).map R.subtype) := by
      rw [map_subgroupOf_eq_of_le hB]
    _ = ((centralizer (U L : Set G)).subgroupOf R).relIndex (B.subgroupOf R) :=
      (relIndex_comap _ _ _).symm
    _ = Nat.card (actionImage c.action B) := by
      rw [← hk, relIndex_ker]
      rfl

private theorem conjugate_le_baumann (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (hx : x ∈ A) :
    (U L).map (MulAut.conj x).toMonoidHom ≤ S R := by
  have he : (S R).map (MulAut.conj x).toMonoidHom = S R :=
    mem_normalizer_iff_map_conj_eq.mp (h.normalizes_S hx)
  exact he ▸ map_mono hb.module_le

/-- R-normality excludes the individual transposition lines. The possible
diagonal image has the same four fixed vectors as the full actor. -/
theorem module_centralizer_conjugate_card (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (c : ActionCoordinates R L) (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G)) :
    Nat.card (U L ⊓ centralizer ((U L).map (MulAut.conj x).toMonoidHom : Set G) :
      Subgroup G) = 4 := by
  let V := (U L).map (MulAut.conj x).toMonoidHom
  have hVS : V ≤ S R := conjugate_le_baumann h hb hx
  have hVR : V ≤ R := hVS.trans inf_le_left
  rw [module_centralizer_card c hVR]
  apply fixed_card_of_normal_image
  · exact (actionImage_mono c.action hVS).trans c.baumann_image.le
  · intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    apply hnc
    intro v hv
    exact (c.kernel ⟨v, hVR hv⟩).mp (hk hv)
  · obtain ⟨r, _hr, her⟩ := c.inner_exchange
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (actionImage c.action V).map (MulAut.conj exchange).toMonoidHom = _
    rw [← her, ← actionImage_conj c.action hVR r]
    have he : V.map (MulAut.conj (r : G)).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (R_normalizes_conjugate h hx r.property)
    rw [he]

/-- A noncommuting normal conjugate fixes exactly one quarter of U. -/
theorem module_index_conjugate (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (c : ActionCoordinates R L) (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G)) :
    (centralizer ((U L).map (MulAut.conj x).toMonoidHom : Set G)).relIndex (U L) = 4 := by
  have hc := module_centralizer_conjugate_card h hb c hx hnc
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G)
    (U L ⊓ centralizer ((U L).map (MulAut.conj x).toMonoidHom : Set G))
    (U L) bot_le inf_le_left
  simp only [relIndex_bot_left, inf_relIndex_left] at hm
  rw [hc, coordinates_module_card c] at hm
  omega

private theorem map_centralizer (V : Subgroup G) (e : G ≃* G) :
    (centralizer (V : Set G)).map e.toMonoidHom = centralizer (V.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e y) (mem_map_of_mem _ hy)

private theorem conjugate_inverse_cancel (V : Subgroup G) (x : G) :
    (V.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = V := by
  rw [map_map]
  have he : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- Conjugating the inverse-conjugator calculation gives the index on Uˣ. -/
theorem actionIndices_of_coordinates (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (hL : ChapterC.IsAlternatingBlock L 5)
    (c : ActionCoordinates R L) (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G)) :
    ActionIndices R L x 4 := by
  apply actionIndices_of_a5 hL
  · rw [actor_index c (show S R ≤ R from inf_le_left), c.baumann_image, actor_card]
  · have hnc' : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G) := by
      intro hc
      have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hc
      rw [conjugate_inverse_cancel, map_centralizer] at hh
      exact hnc (le_centralizer_iff.mp hh)
    have hi := module_index_conjugate h hb c (A.inv_mem hx) hnc'
    have he := relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom)
      (centralizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G)) (U L)
      (MulAut.conj x).injective
    rw [map_centralizer, conjugate_inverse_cancel] at he
    exact he.trans hi

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations

open Baumann.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conditional final assembly: the genuine action and Thompson image suffice.
Their source constructions are still required for `AlternatingIndicesInput`. -/
theorem alternatingIndicesInput_of_earlier_inputs (K : GroupClass.{u})
    (ha : NaturalActionInput (G := G) K) (hj : ThompsonImageInput (G := G) K) :
    AlternatingIndicesInput (G := G) K := by
  intro A H R L h hb hL x hx hnc
  obtain ⟨c⟩ := AlternatingIndices.coordinates_of_inputs ha hj h hL
  exact AlternatingIndices.actionIndices_of_coordinates h hb hL c hx hnc

/-- The completed natural-action and Thompson-image constructions discharge the
alternating-five index input used by the C.5.6 assembly. -/
theorem alternatingIndicesInput (K : GroupClass.{u}) :
    AlternatingIndicesInput (G := G) K :=
  alternatingIndicesInput_of_earlier_inputs K
    (Baumann.AlternatingFive.naturalActionInput (G := G) (K := K))
    (Baumann.AlternatingFive.thompsonImageInput (G := G) (K := K))

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations

end
