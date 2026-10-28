module
public import Theory.Representation.PSL3Two.DoubledOffenders
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# Transport of doubled natural Sylow geometry

A faithful action whose restriction to a normal component is two copies of
the natural binary three-space embeds the whole actor in the full doubled
linear normalizer. Coordinates transport the unique Sylow offender and its
pointwise-fixer calculation with the same component marking. Only the final
transport theorem is public; the coordinate implementation stays private.

Source: Aschbacher--Smith, the doubled-natural B.2.20 steps in 13.6.20 and
13.7.4(1), printed pp.931 and 938.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender BinaryLinearThree
noncomputable section
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

private def doubledLinearCoordinates (ρ : Representation (ZMod 2) A V) (C : Subgroup A)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2)) :
    V ≃ₗ[ZMod 2] (Vector × Vector) :=
  a.linearEquiv.trans (LinearEquiv.finTwoArrow (ZMod 2) Vector)

private def doubledActionCoordinates (ρ : Representation (ZMod 2) A V) (C : Subgroup A)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2)) :
    A →* DoubledOffenders.D :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv (doubledLinearCoordinates ρ C a)).toMonoidHom.comp
    ρ.asGroupHom

private theorem doubledActionCoordinates_intertwines
    (ρ : Representation (ZMod 2) A V) (C : Subgroup A)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2))
    (g : A) (v : V) :
    doubledLinearCoordinates ρ C a (ρ g v) =
      DoubledOffenders.τ (doubledActionCoordinates ρ C a g)
        (doubledLinearCoordinates ρ C a v) := by
  simp [doubledActionCoordinates, LinearMap.GeneralLinearGroup.congrLinearEquiv,
    Representation.asGroupHom, MonoidHom.toHomUnits]

private theorem doubledActionCoordinates_component
    (ρ : Representation (ZMod 2) A V) (C : Subgroup A)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2))
    (c : C) :
    doubledActionCoordinates ρ C a c = DoubledOffenders.δ (a.groupEquiv c) := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := (doubledLinearCoordinates ρ C a).surjective w
  change DoubledOffenders.τ (doubledActionCoordinates ρ C a c)
    (doubledLinearCoordinates ρ C a v) =
    (W.prod W) (a.groupEquiv c) (doubledLinearCoordinates ρ C a v)
  rw [← doubledActionCoordinates_intertwines]
  have he := a.intertwines c v
  change _ = _
  exact congrArg (LinearEquiv.finTwoArrow (ZMod 2) Vector) he

private theorem doubledActionCoordinates_image
    (ρ : Representation (ZMod 2) A V) (C : Subgroup A)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2)) :
    C.map (doubledActionCoordinates ρ C a) = DoubledOffenders.δ.range := by
  ext x
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨a.groupEquiv ⟨c,hc⟩, (doubledActionCoordinates_component ρ C a ⟨c,hc⟩).symm⟩
  · rintro ⟨g,rfl⟩
    exact ⟨a.groupEquiv.symm g,(a.groupEquiv.symm g).property,
      (doubledActionCoordinates_component ρ C a (a.groupEquiv.symm g)).trans
        (congrArg DoubledOffenders.δ (a.groupEquiv.apply_symm_apply g))⟩

private theorem doubledActionCoordinates_injective
    (ρ : Representation (ZMod 2) A V) (hρ : Function.Injective ρ) (C : Subgroup A)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2)) :
    Function.Injective (doubledActionCoordinates ρ C a) := by
  intro x y hxy
  apply hρ
  apply LinearMap.ext
  intro v
  apply (doubledLinearCoordinates ρ C a).injective
  rw [doubledActionCoordinates_intertwines, doubledActionCoordinates_intertwines, hxy]

private theorem doubledActionCoordinates_normalizes
    (ρ : Representation (ZMod 2) A V) (C : Subgroup A) [C.Normal]
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2)) :
    (doubledActionCoordinates ρ C a).range ≤ DoubledOffenders.N := by
  rw [DoubledOffenders.N, ← doubledActionCoordinates_image ρ C a]
  have hh := C.le_normalizer_map (doubledActionCoordinates ρ C a)
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using hh

variable [Finite A]
/-- Full doubled coordinates identify the unique Sylow offender and its pointwise fixer. -/
theorem doubled_sylow_geometry
    (ρ : Representation (ZMod 2) A V) (hρ : Function.Injective ρ)
    (C E : Subgroup A) [C.Normal] (hCE : C ≤ E)
    (a : ActionEquiv (ρ.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2))
    (P : Sylow 2 E) :
    ∃ g : BinaryLinearThree.Group,
    let j : BinaryLinearThree.Group →* A := C.subtype.comp a.groupEquiv.symm.toMonoidHom
    let B := (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j
    let S := (P : Subgroup E).map E.subtype
    B ≤ S ∧ B ≤ C ∧
    (∀ F : Subgroup A, F ≤ S → IsOffender ρ F → F = B) ∧
    (∀ x ∈ S, (∀ v ∈ fixedSpace ρ B, ρ x v = v) → x ∈ B) := by
  let ψ := doubledActionCoordinates ρ C a
  let b := doubledLinearCoordinates ρ C a
  have hi : Function.Injective ψ := doubledActionCoordinates_injective ρ hρ C a
  let H := E.map ψ
  have hdH : DoubledOffenders.δ.range ≤ H :=
    (doubledActionCoordinates_image ρ C a).symm ▸ map_mono hCE
  have hHN : H ≤ DoubledOffenders.N := (map_le_range _ _).trans
    (doubledActionCoordinates_normalizes ρ C a)
  let Q := P.mapSurjective (f := ψ.subgroupMap E) (ψ.subgroupMap_surjective E)
  have hQ : (Q : Subgroup H).map H.subtype =
      ((P : Subgroup E).map E.subtype).map ψ := by
    rw [Sylow.coe_mapSurjective,map_map,map_map]
    rfl
  obtain ⟨g,hBS,huniq,hfix⟩ := DoubledOffenders.sylow_offenders H hdH hHN Q
  let j : BinaryLinearThree.Group →* A := C.subtype.comp a.groupEquiv.symm.toMonoidHom
  let B := (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map j
  let S := (P : Subgroup E).map E.subtype
  have hj : ψ.comp j = DoubledOffenders.δ := by
    apply MonoidHom.ext
    intro z
    exact (doubledActionCoordinates_component ρ C a (a.groupEquiv.symm z)).trans
      (congrArg DoubledOffenders.δ (a.groupEquiv.apply_symm_apply z))
  have hB : B.map ψ =
      (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).map DoubledOffenders.δ := by
    rw [map_map,hj]
  have hBS' : B ≤ S := by
    intro z hz
    have hh : ψ z ∈ S.map ψ := by
      rw [←hQ]
      exact hBS (hB ▸ mem_map_of_mem ψ hz)
    obtain ⟨w,hw,he⟩ := hh
    exact hi he ▸ hw
  refine ⟨g,hBS',?_,?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact (a.groupEquiv.symm z).property
  · intro F hFS hF
    apply map_injective hi
    rw [hB]
    apply (huniq (F.map ψ) (by rw [hQ]; exact map_mono hFS)).mp
    exact hF.map_equivariant ρ DoubledOffenders.τ ψ hi b
        (doubledActionCoordinates_intertwines ρ C a)
  · intro x hx hf
    have hxf : ψ x ∈ B.map ψ := by
      rw [hB]
      apply (hfix (ψ x) ?_).mp
      · intro w hw
        have hw' : w ∈ fixedSpace DoubledOffenders.τ (B.map ψ) := hB.symm ▸ hw
        rw [←fixedSpace_map_equivariant ρ DoubledOffenders.τ ψ b
          (doubledActionCoordinates_intertwines ρ C a)] at hw'
        obtain ⟨v,hv,rfl⟩ := hw'
        exact (doubledActionCoordinates_intertwines ρ C a x v).symm.trans
          (congrArg b (hf v hv))
      · rw [hQ]
        exact mem_map_of_mem ψ hx
    obtain ⟨y,hy,he⟩ := hxf
    exact hi he ▸ hy
end CFSG.Quasithin.ChapterB.QuasisimpleSource
