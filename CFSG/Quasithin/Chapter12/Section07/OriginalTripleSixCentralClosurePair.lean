module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureMatching
public import Theory.Representation.HexacodeAction.FullQuotientGeneration

/-!
# Original conjugates generating the full hexacode image

Lift the even matching conjugator to the original K. Its conjugate of W
has the transverse matching image. Every nonidentity nonswap image in
that conjugate generates the full symmetric quotient together with W.
Perfectness of the even cover restores the entire cubic kernel, so these
original subgroups induce the whole automizer on U.

This is the image-generation step after Aschbacher--Smith12.7.18,
printed p.845. Containment of the original K in the generated subgroup
requires the subsequent two-core lifting argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix MatchingEightGeneration BinaryAlternatingSix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

omit [Finite G] in
private theorem induced_conjugate (A : Subgroup G)
    (hA : A ≤ normalizer (U : Set G)) (g : normalizer (U : Set G)) :
    inducedAutomizer U (A.map (MulAut.conj g.val).toMonoidHom) =
      (inducedAutomizer U A).map
        (MulAut.conj (U.normalizerMonoidHom.rangeRestrict g)).toMonoidHom := by
  let N := normalizer (U : Set G)
  have hAg : A.map (MulAut.conj g.val).toMonoidHom ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact N.mul_mem (N.mul_mem g.property (hA hx)) (N.inv_mem g.property)
  have he : (A.map (MulAut.conj g.val).toMonoidHom).subgroupOf N =
      (A.subgroupOf N).map (MulAut.conj g).toMonoidHom := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hAg, map_map]
    change A.map (MulAut.conj g.val).toMonoidHom =
      (A.subgroupOf N).map ((MulAut.conj g.val).toMonoidHom.comp N.subtype)
    rw [← map_map, map_subgroupOf_eq_of_le hA]
  change ((A.map (MulAut.conj g.val).toMonoidHom).subgroupOf N).map
    U.normalizerMonoidHom.rangeRestrict = _
  rw [he, map_map]
  change _ = ((A.subgroupOf N).map U.normalizerMonoidHom.rangeRestrict).map _
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change U.normalizerMonoidHom.rangeRestrict (g * x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

omit [Finite G] in
private theorem full_image_of_matching_image
    (f : Automizer U →* HexAutomorphisms) (hf : Function.Bijective f)
    (r : alternatingGroup (Fin 6)) (q : Automizer U →* Equiv.Perm (Fin 6))
    (hq : ∀ b, q b = diagramAut (r.val * hexCoordinateSixHom (f b) * r.val⁻¹))
    (A : Subgroup (Automizer U)) (hA : A.map q = ⊤) : A = ⊤ := by
  let e := (MulAut.conj r.val).trans diagramAut
  have hc : (A.map f).map hexCoordinateSixHom = ⊤ := by
    apply top_unique
    intro x _
    have hx : e x ∈ A.map q := hA.symm ▸ mem_top _
    obtain ⟨b, hb, hbx⟩ := hx
    refine ⟨f b, mem_map_of_mem f hb, ?_⟩
    apply e.injective
    exact (hq b).symm.trans hbx
  have hfull := Hexacode.subgroup_eq_top_of_coordinate_image (A.map f) hc
  apply top_unique
  intro b _
  have hb : f b ∈ A.map f := hfull.symm ▸ mem_top _
  obtain ⟨c, hc, hcb⟩ := hb
  exact hf.1 hcb ▸ hc

/-- An actual K-conjugate of the original closure has transverse matching
image and generates the entire original automizer, including its cubic kernel. -/
theorem original_tripleSix_central_closure_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∃ (q : Automizer U →* Equiv.Perm (Fin 6)) (g : K),
      Function.Surjective q ∧
      (inducedAutomizer U K).map q = alternatingGroup (Fin 6) ∧
      (inducedAutomizer U W).map q = matchingEight ∧
      (let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
       (inducedAutomizer U Wg).map q = shiftedMatchingEight ∧
       inducedAutomizer U (W ⊔ Wg) = ⊤ ∧
       ∀ b : normalizer (U : Set G), (b : G) ∈ Wg →
         q (U.normalizerMonoidHom.rangeRestrict b) ≠ 1 →
         ¬ (q (U.normalizerMonoidHom.rangeRestrict b)).IsSwap →
         inducedAutomizer U (W ⊔ zpowers (b : G)) = ⊤) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  let N := normalizer (U : Set G)
  let α := U.normalizerMonoidHom.rangeRestrict
  obtain ⟨hWT, f, hf, _, _, _, r, q, hq, hqs, _, _, hW, hK⟩ :=
    original_tripleSix_central_closure_matching h structural D a z hz hzT hnot houter
  have hWN : W ≤ N := hWT.trans (((structural K h).2.2 U D).1)
  obtain ⟨p, hp⟩ := exists_even_matching_conjugator
  have hpK : p.val ∈ (inducedAutomizer U K).map q := hK.symm ▸ p.property
  obtain ⟨b, ⟨k, hk, rfl⟩, hkp⟩ := hpK
  let g : K := ⟨k.val, hk⟩
  let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
  have hWgN : Wg ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact N.mul_mem (N.mul_mem k.property (hWN hx)) (N.inv_mem k.property)
  have hWg : (inducedAutomizer U Wg).map q = shiftedMatchingEight := by
    rw [show inducedAutomizer U Wg = (inducedAutomizer U W).map
      (MulAut.conj (α k)).toMonoidHom from induced_conjugate W hWN k]
    have he : q.comp (MulAut.conj (α k)).toMonoidHom =
        (MulAut.conj p.val).toMonoidHom.comp q := by
      apply MonoidHom.ext
      intro x
      change q (α k * x * (α k)⁻¹) = p.val * q x * p.val⁻¹
      rw [map_mul, map_mul, map_inv, show q (α k) = p.val from hkp]
    rw [map_map, he, ← map_map, hW]
    exact hp
  have hsingle (b : N) (hb : b.val ∈ Wg)
      (hne : q (α b) ≠ 1) (hswap : ¬ (q (α b)).IsSwap) :
      inducedAutomizer U (W ⊔ zpowers b.val) = ⊤ := by
    apply full_image_of_matching_image f hf r q hq
    have hgen := matching_join_eq_top (q (α b))
      (hWg ▸ mem_map_of_mem q (show α b ∈ inducedAutomizer U Wg from ⟨b, hb, rfl⟩)) hne hswap
    apply top_unique
    rw [← hgen, ← hW]
    apply sup_le
    · exact map_mono (map_mono (comap_mono le_sup_left))
    · apply zpowers_le.mpr
      exact mem_map_of_mem q (show α b ∈ inducedAutomizer U (W ⊔ zpowers b.val) from
        ⟨b, mem_sup_right (mem_zpowers b.val), rfl⟩)
  have hpair : inducedAutomizer U (W ⊔ Wg) = ⊤ := by
    let x : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 1 2
    have hx : x ∈ shiftedMatchingEight :=
      mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have hxne : x ≠ 1 := by decide
    have hxswap : ¬ x.IsSwap := by unfold Equiv.Perm.IsSwap; decide
    have him : x ∈ (inducedAutomizer U Wg).map q := hWg.symm ▸ hx
    obtain ⟨_, ⟨b, hb, rfl⟩, hbx⟩ := him
    have htop := hsingle b hb (hbx.symm ▸ hxne) (hbx.symm ▸ hxswap)
    apply top_unique
    rw [← htop]
    exact map_mono (comap_mono (sup_le_sup_left
      (show zpowers (b : G) ≤ Wg from zpowers_le.mpr hb) W))
  exact ⟨q, g, hqs, hK, hW, hWg, hpair, hsingle⟩

end CFSG.Quasithin.Chapter12.Section07
