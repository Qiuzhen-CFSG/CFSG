module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceCriticalRadical


/-!
# The reciprocal core for the full critical actor

For the elementary-eight pencil actor, every element outside its derived
four-group has the same fixed space as that four-group. Consequently a
vector whose actor displacements all lie in one binary line is fixed.
Apply this to the image of the actual reciprocal core intersection. The
previous transvection bound gives the reverse inclusion, identifying that
intersection with the fixed preimage without either point noncontainment.

This proves the full-actor case of 14.7.61(3)--(4). The actor marking and
its reciprocal source construction remain to be discharged by this branch.
Source: Aschbacher--Smith 14.7.55(4), 14.7.60--61, pp.1066--1068.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open G2Exclusion.MarkedGeometry G2Exclusion.MarkedGeometry.MarkedPencil
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit

private theorem binary_line_eq_zero_or_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (S : Submodule (ZMod 2) W)
    (hd : Module.finrank (ZMod 2) S ≤ 1) (x y : W) (hx : x ∈ S) (hy : y ∈ S)
    (hx0 : x ≠ 0) : y = 0 ∨ y = x := by
  let xS : S := ⟨x,hx⟩
  have hxS : xS ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hn : Module.finrank (ZMod 2) S ≠ 0 := by
    intro hh
    have hb := Submodule.finrank_eq_zero.mp hh
    have hz : x ∈ (⊥ : Submodule (ZMod 2) W) := hb ▸ hx
    exact hx0 hz
  have hdim : Module.finrank (ZMod 2) S = 1 := by omega
  obtain ⟨a,ha⟩ := (finrank_eq_one_iff_of_nonzero' xS hxS).mp hdim (⟨y,hy⟩ : S)
  have he := congrArg Subtype.val ha
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · left
    simpa using he.symm
  · right
    simpa using he.symm

private theorem fixed_of_common_line {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A B : Subgroup D) (hBA : B ≤ A)
    (hout : ∃ a ∈ A, a ∉ B)
    (hspaces : ∀ a ∈ A, a ∉ B → fixedSpace ρ (zpowers a) = fixedSpace ρ B)
    (S : Submodule (ZMod 2) W) (hd : Module.finrank (ZMod 2) S ≤ 1)
    (v : W) (hv : ∀ a ∈ A, ρ a v - v ∈ S) : v ∈ fixedSpace ρ A := by
  obtain ⟨a,ha,haB⟩ := hout
  have hB : v ∈ fixedSpace ρ B := by
    by_contra hn
    have hmove : ρ a v ≠ v := by
      intro hh
      apply hn
      rw [← hspaces a ha haB,mem_fixedSpace_zpowers_iff]
      exact hh
    have hz : ρ a v - v ≠ 0 := sub_ne_zero.mpr hmove
    apply hn
    intro b
    have hh := binary_line_eq_zero_or_eq S hd (ρ a v-v) (ρ b v-v)
      (hv a ha) (hv b (hBA b.property)) hz
    rcases hh with hh | hh
    · exact sub_eq_zero.mp hh
    have hsame : ρ b v = ρ a v := sub_left_inj.mp hh
    have hab : a⁻¹*(b:D) ∈ A := A.mul_mem (A.inv_mem ha) (hBA b.property)
    have habB : a⁻¹*(b:D) ∉ B := by
      intro hh
      have hh' := B.mul_mem b.property (B.inv_mem hh)
      apply haB
      convert hh' using 1; group
    have hfix : ρ (a⁻¹*(b:D)) v = v := by
      rw [map_mul,Module.End.mul_apply,hsame]
      change (ρ a⁻¹ * ρ a) v = v
      rw [←map_mul,inv_mul_cancel,map_one]
      rfl
    have hf : v ∈ fixedSpace ρ B := by
      rw [← hspaces _ hab habB,mem_fixedSpace_zpowers_iff]
      exact hfix
    exact (hn hf).elim
  intro b
  by_cases hb : (b:D) ∈ B
  · exact hB ⟨b,hb⟩
  · have hh : v ∈ fixedSpace ρ (zpowers (b:D)) := (hspaces b b.property hb).symm ▸ hB
    exact (mem_fixedSpace_zpowers_iff ρ (b:D) v).mp hh

/-- A full pencil actor has no nontrivial orbit whose displacements lie in
one binary line, on either concrete model. -/
theorem model_full_actor_fixed_of_common_line (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) (S : Submodule (ZMod 2) m.Space)
    (hd : Module.finrank (ZMod 2) S ≤ 1) (v : m.Space)
    (hv : ∀ a ∈ fullCentralizer m.singularMap m.action p, m.action a v-v ∈ S) :
    v ∈ fixedSpace m.action (fullCentralizer m.singularMap m.action p) := by
  let : FiniteDimensional (ZMod 2) m.Space := by
    cases m with
    | natural => exact inferInstanceAs (FiniteDimensional (ZMod 2) (Atlas.G2.Natural.Space (ZMod 2)))
    | weyl => exact inferInstanceAs (FiniteDimensional (ZMod 2) (Atlas.G2.Natural.TraceZero (ZMod 2)))
  have hm : m.singularMap.Equivariant m.action := by
    cases m with
    | natural => exact naturalMap_equivariant
    | weyl => exact weylMap_equivariant
  obtain ⟨a,ha,hdout⟩ := SetLike.not_le_iff_exists.mp
    (fullCentralizer_not_le_derived m.singularMap m.action hm p)
  apply fixed_of_common_line m.action (fullCentralizer m.singularMap m.action p)
    (derivedCentralizer m.singularMap m.action p) inf_le_left
    ⟨a,ha,fun h => hdout h.2⟩ ?_ S hd v hv
  intro a ha hout
  cases m with
  | natural => exact (natural_full_spaces p a ha hout).2.1
  | weyl => exact (weyl_full_spaces p a ha hout).2.1

open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
include c

/-- The full critical actor forces the actual reciprocal core intersection
to have fixed image, even before either point noncontainment is known. -/
theorem source_full_actor_core_image_fixed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    c.imageSpace (F.U ⊓ path.Qα) ≤ fixedSpace σ (star F path.Uα) := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hh := (starSection c).critical_line_displacement_of_conjugate path.Uα
    path.conjugator⁻¹ (reciprocal_placement h path) (by simpa using F.card 1 (by decide))
  change Module.finrank (ZMod 2) (c.imageSpace path.Zα) ≤ 1 ∧
    ∀ a ∈ star F path.Uα, ∀ v ∈ c.imageSpace (commutatorPreimage F.U path.Uα path.Zα),
      σ a v-v ∈ c.imageSpace path.Zα at hh
  have hD : F.U ⊓ path.Qα ≤ commutatorPreimage F.U path.Uα path.Zα :=
    le_commutatorPreimage inf_le_left
      ((commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator c path))
  let S := (c.imageSpace path.Zα).map E.symm.toLinearMap
  have hdim : Module.finrank (ZMod 2) S ≤ 1 := by
    change Module.finrank (ZMod 2) ((c.imageSpace path.Zα).map E.symm.toLinearMap) ≤ 1
    rw [E.symm.finrank_map_eq]
    exact hh.1
  intro v hv
  have hfix := model_full_actor_fixed_of_common_line m p S hdim (E.symm v) (by
    intro a ha
    rw [←hA] at ha
    obtain ⟨a,ha,rfl⟩ := ha
    have hdelta := hh.2 a ha v (c.imageSpace_mono hD hv)
    have hcoord : m.action (i a) (E.symm v)-E.symm v = E.symm (σ a v-v) := by
      apply E.injective
      rw [map_sub,he,E.apply_symm_apply,E.apply_symm_apply]
    rw [hcoord]
    exact Submodule.mem_map_of_mem hdelta)
  intro a
  have hia : i a ∈ fullCentralizer m.singularMap m.action p :=
    hA ▸ mem_map_of_mem i a.property
  have hh := hfix ⟨i a,hia⟩
  change m.action (i a) (E.symm v) = E.symm v at hh
  have heq := congrArg E hh
  change σ (a : HStar F.H) v = v
  simpa only [he,E.apply_symm_apply] using heq

/-- Source 14.7.61(3) in the full-actor case, on the literal reciprocal core. -/
theorem source_full_actor_core_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    F.U ⊓ path.Qα = commutatorPreimage F.U path.Uα (F.Vi 1) := by
  apply le_antisymm ?_ (source_critical_fixed_preimage_le_reciprocal_core c h hab path m E i hi he)
  apply le_commutatorPreimage inf_le_left
  rw [commutator_comm]
  apply c.commutator_le_of_imageSpace_fixed path.Uα (F.U ⊓ path.Qα) hAH inf_le_left
  rw [fixedSpace_comp_map]
  exact source_full_actor_core_image_fixed c h path m E i he p hA

/-- Identify the actual reciprocal intersection and both quotient orders in
the full-actor branch, without assuming either point noncontainment. -/
theorem source_full_actor_core_and_orders
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i =
      G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer m.singularMap m.action p) :
    F.U ⊓ path.Qα = (F.U ⊓ path.Uα) ⊔ F.Vi 1 ∧
      (F.U ⊓ path.Qα).relIndex F.U = 8 ∧ Nat.card (star F path.Uα) = 8 := by
  let D := F.U ⊓ path.Qα
  have hD := source_full_actor_core_intersection c h hab path hAH m E i hi he p hA
  have hPD : F.Vi 1 ≤ D := by
    change F.Vi 1 ≤ F.U ⊓ path.Qα
    rw [hD]
    exact le_commutatorPreimage c.kernel_le
      (le_normalizer_iff_commutator_le_left.mp hAH)
  have hDi : c.imageSpace D = fixedSpace σ (star F path.Uα) := by
    rw [show D = commutatorPreimage F.U path.Uα (F.Vi 1) from hD,
      c.fixed_image_eq path.Uα hAH c.section_le,fixedSpace_comp_map]
    rfl
  have hIi := source_marked_intersection_image c h hab path hAH m E i he p hA
  have hEq : D = (F.U ⊓ path.Uα) ⊔ F.Vi 1 := by
    apply le_antisymm
    · intro x hx
      let u : F.U := ⟨x,hx.1⟩
      apply (c.coordinates_mem_imageSpace_iff (F.U ⊓ path.Uα) inf_le_left u).mp
      rw [hIi,← hDi]
      exact (c.mem_imageSpace_iff D _).mpr ⟨u,hx,rfl⟩
    · apply sup_le ?_ hPD
      intro x hx
      let u : F.U := ⟨x,hx.1⟩
      have hm : (c.coordinates u).toAdd ∈ c.imageSpace D := by
        rw [hDi,← hIi]
        exact (c.mem_imageSpace_iff _ _).mpr ⟨u,hx,rfl⟩
      have hh := (c.coordinates_mem_imageSpace_iff D inf_le_left u).mp hm
      simpa only [sup_eq_left.mpr hPD] using hh
  have hm : m.singularMap.Equivariant m.action := by
    cases m with
    | natural => exact G2Exclusion.MarkedGeometry.naturalMap_equivariant
    | weyl => exact G2Exclusion.MarkedGeometry.weylMap_equivariant
  have hc : Nat.card (star F path.Uα) = 8 := by
    rw [← card_map_of_injective (K := star F path.Uα) hi,hA]
    exact (G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer_structure
      m.singularMap m.action hm p).2
  refine ⟨hEq,?_,hc⟩
  rw [show F.U ⊓ path.Qα = (F.U ⊓ path.Uα) ⊔ F.Vi 1 from hEq,
    source_marked_intersection_index c h hab path hAH m E i hi he p hA,hc]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
