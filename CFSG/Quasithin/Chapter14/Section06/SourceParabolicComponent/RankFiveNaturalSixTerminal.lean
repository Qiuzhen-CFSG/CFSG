module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixModel
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The terminal full-core crossing contradiction

For the actual rank-five augmentation core, a permutation trivial modulo the
constant line is already trivial. A complementary transposition has displacement
in its duad line. Conjugating that displacement bound back across the source
module crossing puts it in the original constant line, forcing centralization.
The original ambient conjugation and the same full-core coordinates are retained.

Source: Aschbacher–Smith, 14.6.10(5), printed p.1030.
-/

public section
open Subgroup BinaryPermutation Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing
variable {G : Type*} [Group G] (C : Subgroup G)

private theorem zpowers_to_constant (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (u : sourceModule C) (hu : (E u).toAdd = oneWord)
    (v : sourceModule C) (hv : v.val ∈ zpowers (u : G)) :
    (E v).toAdd ∈ Submodule.span (ZMod 2) {oneWord} := by
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hv
  have he : u ^ n = v := Subtype.ext hn
  rw [←he,map_zpow]
  change n • (E u).toAdd ∈ _
  rw [hu]
  exact (Submodule.span (ZMod 2) {oneWord}).toAddSubgroup.zsmul_mem
    (Submodule.subset_span (Set.mem_singleton _)) n

/-- On the literal core hyperplane the central quotient has the same
centralizer as the hyperplane itself. -/
theorem source_hyperplane_kernel
    (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (C : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (C : Set G)) (v : sourceModule C)
      (hv : n.val * v.val * n.val⁻¹ ∈ sourceModule C),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (P : Subgroup G) (hPW : P ≤ sourceModule C)
    (hP : (P.subgroupOf (sourceModule C)).map E.toMonoidHom =
      hyperplane.toAddSubgroup.toSubgroup)
    (u : sourceModule C) (hu : (E u).toAdd = oneWord)
    (a : G) (ha : a ∈ normalizer (C : Set G))
    (hm : ∀ p ∈ P, ⁅a,p⁆ ∈ zpowers (u : G)) : a ∈ centralizer (P : Set G) := by
  let n : normalizer (C : Set G) := ⟨a,ha⟩
  have hnW := normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C) ha
  have hpres (v : sourceModule C) : a*v.val*a⁻¹ ∈ sourceModule C :=
    (mem_normalizer_iff.mp hnW v).mp v.property
  have hcoords (v : sourceModule C) :
      (E ⟨⁅a,v.val⁆,(sourceModule C).mul_mem (hpres v) ((sourceModule C).inv_mem v.property)⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd - (E v).toAdd := by
    have hc : (⟨⁅a,v.val⁆,(sourceModule C).mul_mem (hpres v) ((sourceModule C).inv_mem v.property)⟩ : sourceModule C) =
        ⟨a*v.val*a⁻¹,hpres v⟩ * v⁻¹ := rfl
    rw [hc,map_mul,map_inv]
    rw [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    exact congrArg (fun x => x - (E v).toAdd) (he n v (hpres v))
  have hdisp : ∀ v ∈ hyperplane,
      coreRepresentation (Fin 6) (f n) v - v ∈ Submodule.span (ZMod 2) {oneWord} := by
    intro v hv
    have hvE : Multiplicative.ofAdd v ∈ (P.subgroupOf (sourceModule C)).map E.toMonoidHom :=
      hP ▸ hv
    obtain ⟨w,hw,hew⟩ := hvE
    have hvw : (E w).toAdd = v := congrArg Multiplicative.toAdd hew
    rw [←hvw,←hcoords]
    exact zpowers_to_constant C E u hu _ (hm w hw)
  have hfix := fixes_hyperplane_of_constant_displacement (f n) hdisp
  intro p hp
  let v : sourceModule C := ⟨p,hPW hp⟩
  have hv : (E v).toAdd ∈ hyperplane := by
    have hh := mem_map_of_mem E.toMonoidHom (show v ∈ P.subgroupOf (sourceModule C) from hp)
    rw [hP] at hh
    exact hh
  have hh := (he n v (hpres v)).trans (hfix _ hv)
  have hval : a*p*a⁻¹=p := congrArg Subtype.val (E.injective (Multiplicative.toAdd.injective hh))
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private theorem fixes_core_of_constant_displacement (g : Equiv.Perm (Fin 6))
    (h : ∀ v : core (Fin 6), coreRepresentation (Fin 6) g v - v ∈
      Submodule.span (ZMod 2) {oneWord}) : g = 1 := by
  have hh := hyperplane_fixer g (fixes_hyperplane_of_constant_displacement g (fun v _ => h v))
  rcases hh with hh | rfl
  · exact hh
  have hx := h (pairWord 0 4)
  rw [swap45_displacement] at hx
  have hp : (pairWord 0 4).val 4 + (pairWord 0 4).val 5 = (1 : ZMod 2) := by decide
  rw [hp,one_smul] at hx
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  have hc0 := congrArg (fun x : core (Fin 6) => x.val 0) hc
  have hc4 := congrArg (fun x : core (Fin 6) => x.val 4) hc
  change c * 1 = 0 at hc0
  change c * 1 = 1 at hc4
  have : (0 : ZMod 2) = 1 := hc0.symm.trans hc4
  exact False.elim ((by decide : (0 : ZMod 2) ≠ 1) this)

variable {G : Type*} [Group G] (C : Subgroup G)

private theorem core_coordinate_displacement
    (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (C : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (C : Set G)) (v : sourceModule C)
      (hv : n.val * v.val * n.val⁻¹ ∈ sourceModule C),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (a : normalizer (C : Set G)) (v : sourceModule C)
    (hc : ⁅a.val,v.val⁆ ∈ sourceModule C) :
    (E ⟨⁅a.val,v.val⁆,hc⟩).toAdd =
      coreRepresentation (Fin 6) (f a) (E v).toAdd - (E v).toAdd := by
  have hnW := normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C) a.property
  have hp : a.val*v.val*a.val⁻¹ ∈ sourceModule C :=
    (mem_normalizer_iff.mp hnW v).mp v.property
  have hh : (⟨⁅a.val,v.val⁆,hc⟩ : sourceModule C) = ⟨a.val*v.val*a.val⁻¹,hp⟩ * v⁻¹ := rfl
  rw [hh,map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,he]

private theorem span_to_zpowers
    (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (u v : sourceModule C)
    (hv : (E v).toAdd ∈ Submodule.span (ZMod 2) {(E u).toAdd}) :
    v.val ∈ zpowers (u : G) := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
  fin_cases c
  · change (0 : ZMod 2) • (E u).toAdd = (E v).toAdd at hc
    have hh : (E v).toAdd = 0 := by simpa only [zero_smul] using hc.symm
    have hv1 : v = 1 := by
      apply E.injective
      apply Multiplicative.toAdd.injective
      simpa only [map_one,toAdd_one] using hh
    rw [hv1]
    exact one_mem _
  · change (1 : ZMod 2) • (E u).toAdd = (E v).toAdd at hc
    have hh : (E v).toAdd = (E u).toAdd := by simpa only [one_smul] using hc.symm
    have hvu : v = u := E.injective (Multiplicative.toAdd.injective hh)
    rw [hvu]
    exact mem_zpowers _

/-- Centralizing the literal full core modulo its constant line already
centralizes the full core. -/
theorem source_core_quotient_kernel
    (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (C : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (C : Set G)) (v : sourceModule C)
      (hv : n.val * v.val * n.val⁻¹ ∈ sourceModule C),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (u : sourceModule C) (hu : (E u).toAdd = oneWord)
    (a : G) (ha : a ∈ normalizer (C : Set G))
    (hm : ∀ p ∈ sourceModule C, ⁅a,p⁆ ∈ zpowers (u : G)) :
    a ∈ centralizer (sourceModule C : Set G) := by
  let n : normalizer (C : Set G) := ⟨a,ha⟩
  have hnW := normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C) ha
  have hpres (v : sourceModule C) : a*v.val*a⁻¹ ∈ sourceModule C :=
    (mem_normalizer_iff.mp hnW v).mp v.property
  have hdisp (v : core (Fin 6)) :
      coreRepresentation (Fin 6) (f n) v - v ∈ Submodule.span (ZMod 2) {oneWord} := by
    let p := E.symm (Multiplicative.ofAdd v)
    have hp : (E p).toAdd = v := by simp [p]
    have hc : ⁅a,p.val⁆ ∈ sourceModule C :=
      (sourceModule C).mul_mem (hpres p) ((sourceModule C).inv_mem p.property)
    rw [←hp,←core_coordinate_displacement C E f he n p hc]
    exact zpowers_to_constant C E u hu _ (hm p p.property)
  have hf := fixes_core_of_constant_displacement (f n) hdisp
  intro p hp
  let v : sourceModule C := ⟨p,hp⟩
  have hh := he n v (hpres v)
  rw [hf,map_one] at hh
  have hval : a*p*a⁻¹=p := congrArg Subtype.val (E.injective (Multiplicative.toAdd.injective hh))
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- A complementary-duad action has its commutators in the literal duad line. -/
theorem source_swap_commutator
    (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (C : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (C : Set G)) (v : sourceModule C)
      (hv : n.val * v.val * n.val⁻¹ ∈ sourceModule C),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (u : sourceModule C) (hu : (E u).toAdd = pairWord 4 5)
    (a : normalizer (C : Set G)) (ha : f a ∈ zpowers swap45)
    (v : sourceModule C) : ⁅a.val,v.val⁆ ∈ zpowers (u : G) := by
  have hnW := normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C) a.property
  have hc : ⁅a.val,v.val⁆ ∈ sourceModule C := (sourceModule C).mul_mem
    ((mem_normalizer_iff.mp hnW v).mp v.property) ((sourceModule C).inv_mem v.property)
  apply span_to_zpowers C E u ⟨_,hc⟩
  rw [core_coordinate_displacement C E f he a v hc,hu,←swap45_moved]
  apply Submodule.subset_span
  exact ⟨f a,ha,(E v).toAdd,Submodule.mem_top,rfl⟩

/-- The conjugate-module crossing is impossible once its literal image is
contained in the complementary transposition group and its central line is
transported to the complementary duad. -/
theorem source_crossing_centralizes
    (E : sourceModule C ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (C : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (C : Set G)) (v : sourceModule C)
      (hv : n.val * v.val * n.val⁻¹ ∈ sourceModule C),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (u : sourceModule C) (hu : (E u).toAdd = oneWord)
    (t : G)
    (hut : (MulAut.conj t) u.val ∈ sourceModule C)
    (hutcoord : (E ⟨(MulAut.conj t) u.val,hut⟩).toAdd = pairWord 4 5)
    (hBN : (sourceModule C).map (MulAut.conj t).toMonoidHom ≤ normalizer (C : Set G))
    (hpreN : (sourceModule C).map (MulAut.conj t⁻¹).toMonoidHom ≤ normalizer (C : Set G))
    (himage : ∀ (b : normalizer (C : Set G)),
      b.val ∈ (sourceModule C).map (MulAut.conj t).toMonoidHom →
      f b ∈ zpowers swap45) :
    (sourceModule C).map (MulAut.conj t).toMonoidHom ≤
      centralizer (sourceModule C : Set G) := by
  let W := sourceModule C
  let u' : W := ⟨(MulAut.conj t) u.val,hut⟩
  have hpre : W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (W : Set G) := by
    rintro a ⟨x,hx,rfl⟩
    apply source_core_quotient_kernel C E f he u hu _ (hpreN (mem_map_of_mem _ hx))
    intro p hp
    let b := (MulAut.conj t) p
    have hb : b ∈ W.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ hp
    have hcomm := source_swap_commutator C E f he u' hutcoord
      ⟨b,hBN hb⟩ (himage ⟨b,hBN hb⟩ hb) ⟨x,hx⟩
    have hcomm' : ⁅x,b⁆ ∈ zpowers (u' : G) := by
      rw [←commutatorElement_inv]
      exact (zpowers (u' : G)).inv_mem hcomm
    have hh := mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hcomm'
    rw [MonoidHom.map_zpowers] at hh
    have huinv : (MulAut.conj t⁻¹) (u' : G) = u.val := by
      change t⁻¹ * (t*u.val*t⁻¹) * (t⁻¹)⁻¹ = u.val
      group
    have hbi : (MulAut.conj t⁻¹) b = p := by
      change t⁻¹ * (t*p*t⁻¹) * (t⁻¹)⁻¹ = p
      group
    change (MulAut.conj t⁻¹) ⁅x,b⁆ ∈ zpowers ((MulAut.conj t⁻¹) (u' : G)) at hh
    rw [huinv,map_commutatorElement,hbi] at hh
    exact hh
  apply le_centralizer_iff.mpr
  intro x hx b hb
  obtain ⟨y,hy,rfl⟩ := hb
  have hh := hpre (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hx) y hy
  have hm := congrArg (MulAut.conj t) hh
  simp only [map_mul] at hm
  have hxinv : (MulAut.conj t) ((MulAut.conj t⁻¹) x) = x := by
    change t * (t⁻¹*x*(t⁻¹)⁻¹) * t⁻¹ = x
    group
  change (MulAut.conj t) y * (MulAut.conj t) ((MulAut.conj t⁻¹) x) =
    (MulAut.conj t) ((MulAut.conj t⁻¹) x) * (MulAut.conj t) y at hm
  rwa [hxinv] at hm

end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
