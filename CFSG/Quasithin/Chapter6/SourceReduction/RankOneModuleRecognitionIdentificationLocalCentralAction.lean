module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalTransvections
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# G.6 on the original quotient action in the order-four branch

The layer image is normal in the actual quotient Sylow subgroup, so it
contains a nonidentity Sylow-central involution. Its displacement is exactly
the marked line Z_S/⟨z⟩. The definition of U as the H-closure of Z_S proves
that the conjugate displacements span U/⟨z⟩. The literal involution centralizer
supplies the SQTK cover, and the earlier reduced-closure theorem supplies
trivial two-core for the faithful image.

These facts discharge all hypotheses of the proved G.6.4. Its central clause
makes this transvection normally generate the whole faithful image. No
LocalAnalysis, irreducibility premise, or later kernel equality is used.
The ThreeSpace extension combines this conclusion with genuine repaired G.3.

Source: Aschbacher--Smith, 6.2.11, printed pp.685--686, using G.6.4(4),
printed pp.345--346.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] {T L R : Subgroup G} {z : G}

theorem seedLine_generates (T L R : Subgroup G) (z : G) :
    closure {w : space T L R z | ∃ h : Centralizer z,
      ∃ s ∈ seedLine T L R z, action T L R z h s = w} = ⊤ := by
  let W := space T L R z
  let S := ((ZS T L R).subgroupOf (Centralizer z)).map (projection z)
  let C := closure {w : W | ∃ h : Centralizer z,
    ∃ s ∈ seedLine T L R z, action T L R z h s = w}
  let D := C.map W.subtype
  have hWD : W ≤ D := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨s, hs, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨a, rfl⟩ := isConj_iff.mp hconj
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (line z) a
    let sW : W := ⟨s, le_normalClosure hs⟩
    refine ⟨action T L R z h sW, ?_, rfl⟩
    exact subset_closure ⟨h, sW, hs, rfl⟩
  apply top_unique
  intro w _
  obtain ⟨v, hv, he⟩ := hWD w.property
  exact (Subtype.ext he : v = w) ▸ hv

section Linear
variable [IsElementaryAbelian 2 (space T L R z)]

def representation (T L R : Subgroup G) (z : G)
    [IsElementaryAbelian 2 (space T L R z)] :
    Representation (ZMod 2) (linearAction T L R z).range (Additive (space T L R z)) where
  toFun a := a.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

theorem representation_injective : Function.Injective (representation T L R z) := by
  intro a b he
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective he

def seedSubspace (T L R : Subgroup G) (z : G)
    [IsElementaryAbelian 2 (space T L R z)] : Submodule (ZMod 2) (Additive (space T L R z)) :=
  AddSubgroup.toZModSubmodule 2 (seedLine T L R z).toAddSubgroup

variable [Finite G] {κ : GroupClass} {P : Sylow 2 G} {M : Subgroup G} {n : ℕ}

end Linear

variable [Finite G] {κ : GroupClass} {P : Sylow 2 G} {M : Subgroup G} {n : ℕ}

theorem seedSubspace_finrank (h : Hypothesis611 κ P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    [IsElementaryAbelian 2 (space (P : Subgroup G) L R z)] :
    Module.finrank (ZMod 2) (seedSubspace (P : Subgroup G) L R z) = 1 := by
  let e : seedSubspace (P : Subgroup G) L R z ≃ seedLine (P : Subgroup G) L R z := {
    toFun w := ⟨w.val.toMul, w.property⟩
    invFun w := ⟨Additive.ofMul w.val, w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := (Nat.card_congr e).trans (seedLine_card h hnatural hz ho hP)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := seedSubspace (P : Subgroup G) L R z)
  rw [hc, Nat.card_zmod] at hh
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)


theorem linearAction_core (h : Hypothesis611 κ P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    [IsElementaryAbelian 2 (space (P : Subgroup G) L R z)] :
    pCore 2 (linearAction (P : Subgroup G) L R z).range = ⊥ := by
  let f := action (P : Subgroup G) L R z
  let e := linearize (P : Subgroup G) L R z
  let a := linearAction (P : Subgroup G) L R z
  let erange : f.range ≃* a.range := (e.subgroupMap f.range).trans
    (MulEquiv.subgroupCongr (show f.range.map (e : _ →* _) = a.range from
      (MonoidHom.range_comp e.toMonoidHom f).symm))
  have heq := pCore_map_iso 2 erange
  rw [action_range_core h hnatural hz ho hP, Subgroup.map_bot] at heq
  exact heq.symm

section Central
variable [IsElementaryAbelian 2 (space (P : Subgroup G) L R z)]

def layerImage : Subgroup (linearAction (P : Subgroup G) L R z).range :=
  ((layer L R).subgroupOf (Centralizer z)).map
    (linearAction (P : Subgroup G) L R z).rangeRestrict

theorem layerImage_card_four (h : Hypothesis611 κ P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Nat.card (layerImage (P := P) (L := L) (R := R) (z := z)) = 4 := by
  let a := linearAction (P : Subgroup G) L R z
  rw [← card_map_of_injective (f := a.range.subtype) (K := layerImage (P := P) (L := L) (R := R) (z := z))
    a.range.subtype_injective, layerImage, map_map]
  change Nat.card (((layer L R).subgroupOf (Centralizer z)).map (linearAction (P : Subgroup G) L R z)) = 4
  rw [linearAction, ← map_map, card_map_of_injective (linearize _ _ _ _).injective]
  exact (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.2.2.2

theorem exists_central_mark (h : Hypothesis611 κ P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    let Q := (P.subtype hP).mapSurjective (linearAction (P : Subgroup G) L R z).rangeRestrict_surjective
    ∃ a ∈ layerImage (P := P) (L := L) (R := R) (z := z), a ≠ 1 ∧
      a ∈ (center Q).map (Q : Subgroup (linearAction (P : Subgroup G) L R z).range).subtype := by
  let f := linearAction (P : Subgroup G) L R z
  let Q := (P.subtype hP).mapSurjective f.rangeRestrict_surjective
  let B := layerImage (P := P) (L := L) (R := R) (z := z)
  have hBQ : B ≤ (Q : Subgroup f.range) := map_mono (fun _ hv => h.layer_le_T hv)
  have hQN : (Q : Subgroup f.range) ≤ normalizer (B : Set f.range) := by
    rintro _ ⟨t, ht, rfl⟩
    apply ((layer L R).subgroupOf (Centralizer z)).le_normalizer_map f.rangeRestrict
    apply mem_map_of_mem
    rw [← subgroupOf_normalizer_eq (layer_le_involution_centralizer h hz)]
    exact h.sylow_normalizes_layer ht
  let N := B.subgroupOf (Q : Subgroup f.range)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hQN
  have hBne : B ≠ ⊥ := by
    intro hb
    have hc := layerImage_card_four h hnatural hz ho hP hplane hcard
    change Nat.card B = 4 at hc
    rw [hb, card_bot] at hc
    contradiction
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  let : Nontrivial N := (subgroupOfEquivOfLe hBQ).toEquiv.nontrivial
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  obtain ⟨x, hx, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  refine ⟨x.val.val, x.property, ?_, ⟨x.val, hc, rfl⟩⟩
  intro he
  exact hx (Subtype.ext (Subtype.ext he))

theorem displacement_eq_seed (h : Hypothesis611 κ P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    (a : (linearAction (P : Subgroup G) L R z).range)
    (ha : a ∈ layerImage (P := P) (L := L) (R := R) (z := z)) (hne : a ≠ 1) :
    LinearMap.range (representation (P : Subgroup G) L R z a - LinearMap.id) =
      seedSubspace (P : Subgroup G) L R z := by
  let ρ := representation (P : Subgroup G) L R z
  have hle : LinearMap.range (ρ a - LinearMap.id) ≤ seedSubspace (P : Subgroup G) L R z := by
    obtain ⟨v, hv, rfl⟩ := ha
    rintro _ ⟨w, rfl⟩
    have hm := (four_image_common_center h hnatural hz ho hP hplane hcard).2.2
      (action (P : Subgroup G) L R z v) (mem_map_of_mem _ hv)
    change action (P : Subgroup G) L R z v w.toMul / w.toMul ∈ seedLine (P : Subgroup G) L R z
    simpa only [div_eq_mul_inv] using hm.2 w.toMul
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hd := seedSubspace_finrank h hnatural hz ho hP
  have hm := Submodule.finrank_mono hle
  have hn : LinearMap.range (ρ a - LinearMap.id) ≠ ⊥ := by
    intro hh
    have he : ρ a = 1 := sub_eq_zero.mp (LinearMap.range_eq_bot.mp hh)
    exact hne (representation_injective (he.trans (map_one _).symm))
  have hp : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≠ 0 :=
    fun hh => hn (Submodule.finrank_eq_zero.mp hh)
  omega

omit [Finite G] in
theorem displacement_generates
    (a : (linearAction (P : Subgroup G) L R z).range)
    (he : LinearMap.range (representation (P : Subgroup G) L R z a - LinearMap.id) =
      seedSubspace (P : Subgroup G) L R z) :
    conjugateDisplacementSpan (representation (P : Subgroup G) L R z) a ⊤ = ⊤ := by
  let ρ := representation (P : Subgroup G) L R z
  let W := conjugateDisplacementSpan ρ a ⊤
  let D : Subgroup (space (P : Subgroup G) L R z) := W.toAddSubgroup.toSubgroup'
  have hg : closure {w : space (P : Subgroup G) L R z |
      ∃ h : Centralizer z, ∃ s ∈ seedLine (P : Subgroup G) L R z,
        action (P : Subgroup G) L R z h s = w} ≤ D := by
    apply (closure_le _).mpr
    rintro _ ⟨h, s, hs, rfl⟩
    have hs' : Additive.ofMul s ∈ LinearMap.range (ρ a - LinearMap.id) := by
      rw [he]
      exact hs
    obtain ⟨w, hw⟩ := hs'
    change ρ ((linearAction (P : Subgroup G) L R z).rangeRestrict h) (Additive.ofMul s) ∈ W
    rw [← hw]
    exact Submodule.subset_span ⟨_, mem_top _, w, rfl⟩
  rw [seedLine_generates] at hg
  apply top_unique
  intro w _
  exact hg (mem_top w.toMul)

end Central

/-- G.6.4 on the original quotient action in the contrary order-four branch,
with a Sylow-central transvection whose displacement is the marked line.
No LocalAnalysis or later kernel equality is used. -/
theorem four_image_G6 (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    let := (reduced_space h hnatural hz ho hP).elementary
    let ρ := representation (P : Subgroup G) L R z
    ∃ a ∈ layerImage (P := P) (L := L) (R := R) (z := z), a ≠ 1 ∧
      LinearMap.range (ρ a - LinearMap.id) = seedSubspace (P : Subgroup G) L R z ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 ∧
      normalClosure ({a} : Set (linearAction (P : Subgroup G) L R z).range) = ⊤ ∧
      ChapterG.Section06.CentralModel ρ := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let ρ := representation (P : Subgroup G) L R z
  let f := linearAction (P : Subgroup G) L R z
  obtain ⟨a, ha, hne, hc⟩ := exists_central_mark h hnatural hz ho hP hplane hcard
  have he := displacement_eq_seed h hnatural hz ho hP hplane hcard a ha hne
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 := by
    rw [he]
    exact seedSubspace_finrank h hnatural hz ho hP
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨v, hv, rfl⟩ := ha
    let := h.layer_elementary
    have hv2 : v ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := layer L R) (v : G) hv)
    rw [← map_pow, hv2, map_one]
  have hh : ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple ρ a f.rangeRestrict := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := h.simpleQTKE.involution_centralizer_sqtk ho
    quotient_surjective := f.rangeRestrict_surjective
    twoCore := linearAction_core h hnatural hz ho hP
    faithful := representation_injective
    involution := ha2
    nonidentity := hne
    displacement_rank := hr.le.trans (by decide)
    generated := displacement_generates a he }
  have hm := (ChapterG.Section06.lemma_G_6_4 hh hr).2
    ((P.subtype hP).mapSurjective f.rangeRestrict_surjective) hc
  exact ⟨a, ha, hne, he, hr, hm.1, hm.2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
