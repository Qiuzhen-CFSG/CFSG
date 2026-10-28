module

public import Theory.GroupTheory.PCoreCharacteristicCentralizer
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Embedded characteristic subgroups detecting ambient centralizers

An embedding identifying a model subgroup with the ambient two-core transports
characteristicity and either intrinsic centralizer-detection criterion. A separate
quotient lemma restricts a self-centralizing subgroup through its exact central
denominator. These provide the transport steps in Aschbacher--Smith 14.2.21,
printed pp.988--989, without assuming normality of the larger model subgroup.
-/

public section

open Subgroup
namespace Subgroup
variable {A B : Type*} [Group A] [Group B]

private theorem ambient_centralizer_map_equiv (e : A ≃* B) (D : Subgroup A) :
    (centralizer (D : Set A)).map e.toMonoidHom =
      centralizer (D.map e.toMonoidHom : Set B) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem ambient_characteristic_map_equiv (e : A ≃* B) (D : Subgroup A)
    [D.Characteristic] : (D.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y, hy, rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply _

/-- Transport intrinsic characteristic detection through a literal embedding of the core. -/
theorem ambient_centralizer_detection [Finite B]
    (f : A →* B) (hf : Function.Injective f) (R D : Subgroup A)
    (hD : D ≤ R) [(D.subgroupOf R).Characteristic]
    (hR : R.map f = pCore 2 B)
    (hcentral : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (hEC : D.subgroupOf R ≤ centralizer (D.subgroupOf R : Set R))
    (hdetect : centralizer (D.subgroupOf R : Set R) ≤ D.subgroupOf R ∨
      (D.subgroupOf R).relIndex (centralizer (D.subgroupOf R : Set R)) = 2) :
    (D.map f).Normal ∧ centralizer (D.map f : Set B) ≤ pCore 2 B := by
  let e : R ≃* pCore 2 B :=
    (R.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hR)
  let K := (D.subgroupOf R).map e.toMonoidHom
  let : K.Characteristic := ambient_characteristic_map_equiv e _
  have hK : K.map (pCore 2 B).subtype = D.map f := by
    rw [map_map]
    change (D.subgroupOf R).map (f.comp R.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hD]
  constructor
  · rw [← hK]
    infer_instance
  · rw [← hK]
    have hc : (centralizer (D.subgroupOf R : Set R)).map e.toMonoidHom =
        centralizer (K : Set (pCore 2 B)) := ambient_centralizer_map_equiv e _
    rcases hdetect with hs | hi
    · exact centralizer_le_pCore_of_characteristic_selfCentralizing 2 hcentral K
        (hc ▸ map_mono hs)
    · apply centralizer_le_twoCore_of_characteristic_centralizer_index_two hcentral K
      · exact hc ▸ map_mono hEC
      · rw [← hc, relIndex_map_map_of_injective _ _ e.injective]
        exact hi

/-- Restrict a self-centralizing quotient subgroup to an injectively embedded group
containing it, with its exact central denominator. -/
theorem ambient_quotient_centralizer_pullback
    (f : A →* B) (hf : Function.Injective f) (Z : Subgroup B) [Z.Normal]
    (C : Subgroup A) [C.Normal] (hC : C.map f = Z)
    (Q : Subgroup B) (hQ : Q ≤ f.range)
    (hself : centralizer (Q.map (QuotientGroup.mk' Z) : Set (B ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) :
    centralizer ((Q.comap f).map (QuotientGroup.mk' C) : Set (A ⧸ C)) ≤
      (Q.comap f).map (QuotientGroup.mk' C) := by
  have hpre : Z.comap f = C := by
    rw [← hC, comap_map_eq_self_of_injective hf]
  let j := QuotientGroup.map C Z f (le_of_eq hpre.symm)
  have hj : Function.Injective j := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, hpre]
    exact (map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' C).symm)
  have hmap : ((Q.comap f).map (QuotientGroup.mk' C)).map j =
      Q.map (QuotientGroup.mk' Z) := by
    rw [map_map]
    change (Q.comap f).map ((QuotientGroup.mk' Z).comp f) = _
    rw [← map_map, map_comap_eq_self hQ]
  intro a ha
  have hja : j a ∈ centralizer (Q.map (QuotientGroup.mk' Z) : Set (B ⧸ Z)) := by
    rw [← hmap]
    exact map_centralizer_le_centralizer_image _ j (mem_map_of_mem _ ha)
  have hm := hself hja
  rw [← hmap] at hm
  obtain ⟨b, hb, he⟩ := hm
  exact hj he ▸ hb
end Subgroup
