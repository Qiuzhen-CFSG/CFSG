module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCentralAction
public import Theory.SpecificGroups.BinaryLinear.LineRadical

/-!
# The marked binary three-space in the contrary order-four branch

A Sylow-central transvection normally generates the original faithful image.
Thus its G.3 orbit block is the whole space, and G.3 supplies the full linear
action. Fixing the marked quotient line lifts to normalization of the original
four-plane Z_S, hence of the layer. The layer image is therefore invariant
under the full point stabilizer. Transitivity on nonidentity common-center
transvections identifies that image with the entire line radical.

Its order is four, forcing dimension three. The final theorem constructs
an actual actor isomorphism and intertwining equivalence with GL₃(2) on its
natural module. These facts precede the four-space and ambient A₇ contradiction;
they do not exclude the contrary order-four branch on their own.

Source: Aschbacher--Smith, 6.2.11, printed p.686, first paragraph.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {L R : Subgroup G} {z : G}
  {κ : GroupClass} {P : Sylow 2 G} {M : Subgroup G} {n : ℕ}

private theorem full_action_of_normal_generator
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {A : Subgroup (BinaryLinear.GL W)} [Finite A] {x : W}
    (hG3 : ChapterG.Section03.Hypotheses A (MulAction.orbit A x))
    (hfull : ChapterG.Section03.FullAction A (MulAction.orbit A x))
    (hspan : Submodule.span (ZMod 2) (MulAction.orbit A x) = ⊤)
    (a : A) (ha : a.val ∈ rootGroup A x)
    (hgen : normalClosure ({a} : Set A) = ⊤) : A = ⊤ := by
  let Δ := MulAction.orbit A x
  let K := generated A Δ
  let : (K.subgroupOf A).Normal := generated_normal A Δ hG3.stable
  have hKA : K = A := by
    have hle : normalClosure ({a} : Set A) ≤ K.subgroupOf A := by
      apply normalClosure_le_normal
      rintro b rfl
      exact rootGroup_le_generated A (MulAction.mem_orbit_self x) ha
    rw [hgen] at hle
    have he : K.subgroupOf A = ⊤ := top_unique hle
    exact le_antisymm (generated_le A Δ) (subgroupOf_eq_top.mp he)
  let i : ChapterG.Section03.OrbitBlock A Δ :=
    ⟨Δ, x, MulAction.mem_orbit_self x, by change Δ = MulAction.orbit K x; rw [hKA]⟩
  let B := ChapterG.Section03.blockSpace A Δ i
  have hB : B = ⊤ := hspan
  have hs := hfull.surjective i
  apply top_unique
  intro g _
  let e : B ≃ₗ[ZMod 2] W := (LinearEquiv.ofEq _ _ hB).trans Submodule.topEquiv
  let gB : BinaryLinear.GL B := e.trans (g.trans e.symm)
  obtain ⟨b, hb⟩ := hs gB
  have hbg : b.val = g := by
    ext v
    have he := congrArg (fun t : BinaryLinear.GL B => (t (e.symm v) : W)) hb
    change b.val (e.symm v : W) = (e.symm (g (e (e.symm v))) : W) at he
    have heval (w : B) : e w = (w : W) := rfl
    have hev : (e.symm v : W) = v := by rw [← heval, e.apply_symm_apply]
    rw [heval, hev] at he
    simpa only [← heval, e.apply_symm_apply] using he
  exact hbg ▸ generated_le A i.val b.property

/-- G.3 and G.6 force the full linear group on the actual U/⟨z⟩.
The Sylow-central transvection normally generates the faithful image, so
its G.3 block is the entire original orbit span. -/
theorem four_image_full_linear (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    let := (reduced_space h hnatural hz ho hP).elementary
    (linearAction (P : Subgroup G) L R z).range = ⊤ := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let f := linearAction (P : Subgroup G) L R z
  let A := f.range
  let ρ := representation (P : Subgroup G) L R z
  obtain ⟨a, ha, hane, hdisp, hr, hgen, _⟩ := four_image_G6 h hnatural hz ho hP hplane hcard
  obtain ⟨x, hx, hxs, _, hG3, hfull, _⟩ := four_image_G3 h hnatural hz ho hP hplane hcard
  have hline : centerLine x = seedSubspace (P : Subgroup G) L R z := by
    apply Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxs))
    rw [finrank_span_singleton hx, seedSubspace_finrank h hnatural hz ho hP]
  have haroot : a.val ∈ rootGroup A x := by
    refine ⟨a.property, ?_, ?_⟩
    · intro v hv
      obtain ⟨b, hb, hab⟩ := ha
      have hm := (four_image_common_center h hnatural hz ho hP hplane hcard).2.2
        (action (P : Subgroup G) L R z b) (mem_map_of_mem _ hb)
      have hv' : v.toMul ∈ seedLine (P : Subgroup G) L R z := (show v ∈ seedSubspace (P : Subgroup G) L R z from hline ▸ hv)
      rw [← hab]
      exact congrArg Additive.ofMul (hm.1 v.toMul hv')
    · intro v
      have hv := LinearMap.mem_range_self (ρ a - LinearMap.id) v
      rw [hdisp, ← hline] at hv
      exact hv
  have hspan : Submodule.span (ZMod 2) (MulAction.orbit A x) = ⊤ := by
    have he := displacement_generates a hdisp
    apply top_unique
    rw [← he]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, rfl⟩
    have hv := LinearMap.mem_range_self (ρ a - LinearMap.id) v
    rw [hdisp, ← hline] at hv
    simp only [LinearMap.sub_apply, LinearMap.id_apply] at hv
    rcases (mem_centerLine_iff x _).mp hv with hv | hv
    · rw [hv, map_zero]
      exact Submodule.zero_mem _
    · rw [hv]
      exact Submodule.subset_span (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)
  exact full_action_of_normal_generator hG3 hfull hspan a haroot hgen


section PointControl
variable [IsElementaryAbelian 2 (space (P : Subgroup G) L R z)]

/-- Fixing the marked binary line means normalizing the original four-plane:
its inverse image under the literal central quotient is exactly Z_S. -/
theorem seed_fixer_normalizes_layerImage (h : Hypothesis611 κ P L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (a : (linearAction (P : Subgroup G) L R z).range)
    (hfix : ∀ v ∈ seedSubspace (P : Subgroup G) L R z, a.val v = v) :
    a ∈ normalizer (layerImage (P := P) (L := L) (R := R) (z := z) :
      Set (linearAction (P : Subgroup G) L R z).range) := by
  let f := linearAction (P : Subgroup G) L R z
  obtain ⟨b, rfl⟩ := f.rangeRestrict_surjective a
  have hSH : ZS (P : Subgroup G) L R ≤ Centralizer z := h.ZS_le_T.trans hP
  have hle : (ZS (P : Subgroup G) L R).map (MulAut.conj (b : G)).toMonoidHom ≤
      ZS (P : Subgroup G) L R := by
    rintro _ ⟨s, hs, rfl⟩
    let sH : Centralizer z := ⟨s, hSH hs⟩
    let w : space (P : Subgroup G) L R z :=
      ⟨projection z sH, le_normalClosure (mem_map_of_mem _ hs)⟩
    have hw : Additive.ofMul w ∈ seedSubspace (P : Subgroup G) L R z :=
      mem_map_of_mem _ hs
    have he := congrArg (fun v : Additive (space (P : Subgroup G) L R z) => v.toMul.val)
      (hfix (Additive.ofMul w) hw)
    change projection z b * projection z sH * (projection z b)⁻¹ = projection z sH at he
    rw [← map_inv, ← map_mul, ← map_mul] at he
    have hc := (QuotientGroup.eq_iff_div_mem.mp he)
    have hh := (ZS (P : Subgroup G) L R).mul_mem ((zpowers_le.mpr hz) hc) hs
    change ((b : G) * s * (b : G)⁻¹ / s) * s ∈ ZS (P : Subgroup G) L R at hh
    simpa only [div_mul_cancel, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply] using hh
  have hn : (b : G) ∈ normalizer (ZS (P : Subgroup G) L R : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hle
      (by rw [card_map_of_injective (MulAut.conj (b : G)).injective]))
  apply ((layer L R).subgroupOf (Centralizer z)).le_normalizer_map f.rangeRestrict
  apply mem_map_of_mem
  rw [← subgroupOf_normalizer_eq (layer_le_involution_centralizer h hz)]
  exact hplane hn

end PointControl

private theorem eq_radical_of_point_normalizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (x : W) (hx : x ≠ 0) (B : Subgroup (BinaryLinear.GL W))
    (hB : B ≤ radical (centerLine x)) (hne : B ≠ ⊥)
    (hn : ∀ c : BinaryLinear.GL W, c x = x → c ∈ normalizer (B : Set (BinaryLinear.GL W))) :
    B = radical (centerLine x) := by
  apply le_antisymm hB
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ha1 : (a : BinaryLinear.GL W) ≠ 1 := fun he => ha (Subtype.ext he)
  obtain ⟨f, hf, hfx, he⟩ := exists_transvection_of_mem_line_radical hx (hB a.property) ha1
  have hea : a.val = transvection x f hfx := LinearEquiv.ext he
  intro b hb
  by_cases hb1 : b = 1
  · exact hb1 ▸ B.one_mem
  obtain ⟨c, hc, hec⟩ := BinaryLinear.LineRadical.conjugate_fixing_center x hx f hf hfx hb hb1
  rw [← hea] at hec
  rw [← hec]
  exact (mem_normalizer_iff.mp (hn c hc) a.val).mp a.property

/-- The faithful image is the full binary three-space action, and the
original layer image is the entire radical of the marked line. The dimension
comes from the actual plane stabilizer normalizing that four-group. -/
theorem four_image_three_space (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    let := (reduced_space h hnatural hz ho hP).elementary
    let f := linearAction (P : Subgroup G) L R z
    f.range = ⊤ ∧ Module.finrank (ZMod 2) (Additive (space (P : Subgroup G) L R z)) = 3 ∧
      (layerImage (P := P) (L := L) (R := R) (z := z)).map f.range.subtype =
        radical (seedSubspace (P : Subgroup G) L R z) := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let f := linearAction (P : Subgroup G) L R z
  let A := f.range
  let B := (layerImage (P := P) (L := L) (R := R) (z := z)).map A.subtype
  have hfull := four_image_full_linear h hnatural hz ho hP hplane hcard
  obtain ⟨x, hx, hxs, _, _⟩ := four_image_G3 h hnatural hz ho hP hplane hcard
  have hline : centerLine x = seedSubspace (P : Subgroup G) L R z := by
    apply Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxs))
    rw [finrank_span_singleton hx, seedSubspace_finrank h hnatural hz ho hP]
  have hBcard : Nat.card B = 4 := by
    rw [card_map_of_injective A.subtype_injective]
    exact layerImage_card_four h hnatural hz ho hP hplane hcard
  have hBrad : B ≤ radical (centerLine x) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    have hm := (four_image_common_center h hnatural hz ho hP hplane hcard).2.2
      (action (P : Subgroup G) L R z b) (mem_map_of_mem _ hb)
    constructor
    · intro v hv
      exact congrArg Additive.ofMul (hm.1 v.toMul (show v ∈ seedSubspace (P : Subgroup G) L R z from hline ▸ hv))
    · intro v
      rw [hline]
      change action (P : Subgroup G) L R z b v.toMul / v.toMul ∈ seedLine (P : Subgroup G) L R z
      simpa only [div_eq_mul_inv] using hm.2 v.toMul
  have hBne : B ≠ ⊥ := by intro he; rw [he, card_bot] at hBcard; contradiction
  have heq : B = radical (centerLine x) := eq_radical_of_point_normalizer x hx B hBrad hBne (by
    intro c hc
    let a : A := ⟨c, hfull.ge (mem_top _)⟩
    have hn := seed_fixer_normalizes_layerImage h hz hP hplane a (by
      intro v hv
      rw [← hline] at hv
      rcases (mem_centerLine_iff x v).mp hv with rfl | rfl
      · exact c.map_zero
      · exact hc)
    exact (layerImage (P := P) (L := L) (R := R) (z := z)).le_normalizer_map A.subtype
      (mem_map_of_mem A.subtype hn))
  have hd := BinaryLinear.LineRadical.card x hx
  rw [← heq, hBcard] at hd
  have he : Module.finrank (ZMod 2) (Additive (space (P : Subgroup G) L R z)) - 1 = 2 :=
    Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hd.symm)
  exact ⟨hfull, by omega, heq.trans (congrArg radical hline)⟩


/-- An actual actor isomorphism and intertwining equivalence with GL₃(2)
on its natural module, on the original quotient action. -/
theorem four_image_natural_three (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    letI := (reduced_space h hnatural hz ho hP).elementary
    ChapterG.Section06.HasModelOn (representation (P : Subgroup G) L R z) ⊤ ⊤
      (ChapterG.Section06.binaryLinearAction 3) := by
  let := (reduced_space h hnatural hz ho hP).elementary
  obtain ⟨hfull, hdim, _⟩ := four_image_three_space h hnatural hz ho hP hplane hcard
  let W := Additive (space (P : Subgroup G) L R z)
  let f := linearAction (P : Subgroup G) L R z
  let e : W ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearEquiv.ofFinrankEq W (Fin 3 → ZMod 2) (by
    rw [hdim]
    simp)
  let eg : BinaryLinear.GL W ≃* BinaryLinear.GL (Fin 3 → ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)))
  let eA : f.range ≃* BinaryLinear.GL W := (MulEquiv.subgroupCongr hfull).trans topEquiv
  refine ⟨topEquiv.trans (eA.trans eg), Submodule.topEquiv.trans e, fun _ _ => Submodule.mem_top, ?_⟩
  intro a w
  change e (a.val.val w.val) = e (a.val.val (e.symm (e w.val)))
  rw [e.symm_apply_apply]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
