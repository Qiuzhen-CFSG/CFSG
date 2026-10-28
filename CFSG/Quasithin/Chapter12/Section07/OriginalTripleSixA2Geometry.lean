module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixAutomizer
public import CFSG.Quasithin.Chapter12.Section07.HexacodeA2Geometry
public import Theory.Representation.HexacodeAction.OffenderCommutator
public import CFSG.Quasithin.ChapterE.Section04.Basic
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Core.Lifting
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The common original A2 commutator and a full-weight point in it

The actual Sylow image on U contains a conjugate of the inner plane offender.
Uniqueness of the hexacode offender inside a two-group makes every original
A2 actor induce that same subgroup. Literal conjugation coordinates then
identify all their commutators with one actual subgroup V2 of U. Its model
commutator is the fixed four-space and contains a full-weight vector.

The selected t2 is a new original element of V2; no arbitrary supplied
even-orbit point is forced into this T-aligned plane.
Source: Aschbacher–Smith, 12.7.2(4), 12.7.3 and 12.7.11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Hexacode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original T-aligned common commutator and an actual full-weight point in it. -/
theorem original_tripleSix_a2_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    let := D.elementary
    ∃ V2 : Subgroup G, ∃ t2 : U, t2 ≠ 1 ∧ (t2 : G) ∈ V2 ∧
      hammingNorm (tripleSixPointCoordinates D a t2).toAdd.val = 6 ∧
      (∀ A : Subgroup G, A ≤ (T : Subgroup G) →
        inducedAutomizer U A ∈ fixedSpaceFamily (automizerRepresentation U) 2 →
          subgroupCorank A (A ⊓ centralizer (U : Set G)) = 2 ∧ ⁅U,A⁆ = V2) := by
  let := D.elementary
  obtain ⟨f, hf, _, himage, heq⟩ := original_tripleSix_full_automizer h structural D a
  let c := tripleSixPointCoordinates D a
  let E : Additive U ≃ₗ[ZMod 2] hexacode :=
    LinearEquiv.ofBijective (c.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) c.bijective
  have heq' (b : Automizer U) (v : Additive U) :
      E (automizerRepresentation U b v) = action (f b) (E v) := heq b v.toMul
  let N := normalizer (U : Set G)
  let q := U.normalizerMonoidHom.rangeRestrict
  have hTN : (T : Subgroup G) ≤ N := ((structural K h).2.2 U D).1
  let S : Sylow 2 (Automizer U) := (T.subtype hTN).mapSurjective
    U.normalizerMonoidHom.rangeRestrict_surjective
  have hS : (S : Subgroup (Automizer U)) = inducedAutomizer U (T : Subgroup G) := rfl
  let B0 := ThompsonOffenders.SylowModel.planeGroup.map hexSign.ker.subtype
  have hB0 : IsBestOffender action B0 := ThompsonOffenders.full_planeGroup_best
  have hB0range : B0 ≤ f.range := by
    apply (map_subtype_le _).trans
    rw [← himage]
    exact map_le_range _ _
  let A0 := B0.comap f
  have hA0map : A0.map f = B0 := map_comap_eq_self hB0range
  have hA0p : IsPGroup 2 A0 := by
    let j : A0 →* B0 := (f.comp A0.subtype).codRestrict B0 (fun b => b.property)
    have hj : Function.Injective j := by
      intro b d hbd
      exact Subtype.ext (hf (congrArg Subtype.val hbd))
    let := hB0.1.2
    exact (IsElementaryAbelian.isPGroup 2 B0).of_injective j hj
  obtain ⟨R, hA0R⟩ := hA0p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Automizer U) R S
  let B := A0.map (MulAut.conj g).toMonoidHom
  have hBS : B ≤ (S : Subgroup (Automizer U)) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hA0R
    exact hh.trans_eq (congrArg Sylow.toSubgroup hg)
  have hBmap : B.map f = B0.map (MulAut.conj (f g)).toMonoidHom := by
    have hh : f.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (f g)).toMonoidHom.comp f := by
      apply MonoidHom.ext
      intro b
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv]
    change (A0.map (MulAut.conj g).toMonoidHom).map f = _
    rw [map_map, hh, ← map_map, hA0map]
  have hbest : IsBestOffender action (B.map f) :=
    hBmap.symm ▸ hB0.map_conj action (f g)
  obtain ⟨R2, hR2T, hR2, _⟩ := core_lift_image_subgroup hTN B (hS ▸ hBS)
  let V2 := ⁅U,R2⁆
  have hR2N : R2 ≤ N := hR2T.trans hTN
  have hV2U : V2 ≤ U := le_normalizer_iff_commutator_le_left.mp hR2N
  let ρ := action.comp (f.comp q)
  let d : BinaryConjugationSection N U ⊥ ρ := {
    section_le := U.le_normalizer
    kernel_le := bot_le
    normalized := le_rfl
    coordinates := c.toMonoidHom
    onto := c.surjective
    kernel_eq := by
      rw [bot_subgroupOf]
      exact c.toMonoidHom.ker_eq_bot_iff.mpr c.injective
    equivariant := by
      intro n u
      exact heq (q n) u }
  have hUtop : d.imageSpace U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u, hu⟩ := c.surjective (Multiplicative.ofAdd v)
    exact (d.mem_imageSpace_iff U v).mpr ⟨u, u.property, congrArg Multiplicative.toAdd hu⟩
  have hcomm (A : Subgroup G) (hAN : A ≤ N) :
      d.imageSpace ⁅U,A⁆ = subspaceCommutator action ⊤ ((inducedAutomizer U A).map f) := by
    rw [commutator_comm, d.imageSpace_commutator A U hAN le_rfl, hUtop]
    change subspaceCommutator (action.comp (f.comp q)) ⊤ (A.subgroupOf N) = _
    rw [subspaceCommutator_comp_map, ← map_map]
    rfl
  have heven := ThompsonOffenders.bestOffender_le_even (B.map f) hbest
  let Be := (B.map f).subgroupOf hexSign.ker
  have hBe : IsBestOffender evenAction Be := hbest.subgroupOf action heven
  have hBeMap : Be.map hexSign.ker.subtype = B.map f := map_subgroupOf_eq_of_le heven
  have hmodel : subspaceCommutator evenAction ⊤ Be = subspaceCommutator action ⊤ (B.map f) := by
    change subspaceCommutator (action.comp hexSign.ker.subtype) ⊤ Be = _
    rw [subspaceCommutator_comp_map, hBeMap]
  obtain ⟨v, hv, hw⟩ := bestOffender_commutator_full_weight Be hBe
  have hv2 : v ∈ d.imageSpace V2 := by
    rw [hcomm R2 hR2N, hR2, ← hmodel]
    exact hv
  obtain ⟨t2, ht2, hct⟩ := (d.mem_imageSpace_iff V2 v).mp hv2
  have ht2ne : t2 ≠ 1 := by
    intro he
    have hz : v = 0 := hct.symm.trans (congrArg Multiplicative.toAdd
      (show c t2 = 1 from he ▸ c.map_one))
    rw [hz] at hw
    norm_num at hw
  refine ⟨V2, t2, ht2ne, ht2, ?_, ?_⟩
  · change hammingNorm (d.coordinates t2).toAdd.val = 6
    rw [hct]
    exact hw
  · intro A hAT hA
    have hAN : A ≤ N := hAT.trans hTN
    have hAf := fixedSpaceFamily_map_of_equivariant (automizerRepresentation U) action f hf E heq' hA
    have hAP : (inducedAutomizer U A).map f ≤ (S : Subgroup (Automizer U)).map f := by
      apply map_mono
      rw [hS]
      exact map_mono (subgroupOf_mono N hAT)
    have hsame : (inducedAutomizer U A).map f = B.map f :=
      ThompsonOffenders.bestOffender_unique_in_pgroup _ (S.isPGroup'.map f)
        hAP (map_mono hBS) (hexacode_a2_bestOffender _ hAf).2.2.2 hbest
    refine ⟨?_, ?_⟩
    · rw [← rank_inducedAutomizer U A hAN, ← rank_map_injective f hf]
      exact (hexacode_a2_bestOffender _ hAf).2.1
    · have himg : d.imageSpace ⁅U,A⁆ = d.imageSpace V2 := by
        rw [hcomm A hAN, hcomm R2 hR2N, hR2, hsame]
      have hAU : ⁅U,A⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hAN
      apply le_antisymm
      · intro u hu
        have hm := (d.mem_imageSpace_iff ⁅U,A⁆ (c ⟨u,hAU hu⟩).toAdd).mpr
          ⟨⟨u,hAU hu⟩,hu,rfl⟩
        rw [himg] at hm
        obtain ⟨v,hv,hvu⟩ := (d.mem_imageSpace_iff V2 _).mp hm
        have he : v = ⟨u,hAU hu⟩ := c.injective (Multiplicative.toAdd.injective hvu)
        have he' : (v : G) = u := congrArg (fun z : U => (z : G)) he
        exact he' ▸ hv
      · intro u hu
        have hm := (d.mem_imageSpace_iff V2 (c ⟨u,hV2U hu⟩).toAdd).mpr
          ⟨⟨u,hV2U hu⟩,hu,rfl⟩
        rw [← himg] at hm
        obtain ⟨v,hv,hvu⟩ := (d.mem_imageSpace_iff ⁅U,A⁆ _).mp hm
        have he : v = ⟨u,hV2U hu⟩ := c.injective (Multiplicative.toAdd.injective hvu)
        have he' : (v : G) = u := congrArg (fun z : U => (z : G)) he
        exact he' ▸ hv

end CFSG.Quasithin.Chapter12.Section07
