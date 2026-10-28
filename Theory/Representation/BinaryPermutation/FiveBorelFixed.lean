module
public import Theory.Representation.BinaryAlternatingFiveFlag.Coordinates
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryPermutation.FiveCentralExtension

/-!
# Borel fixation in the binary deleted five-point module

The regular four-group has a unique nonzero fixed vector. Sylow conjugacy
therefore makes every A₅ Sylow normalizer fix its whole fixed space.
The class-sum section lifts this conclusion to any symmetric-five module
with the original core quotient and an A₅-fixed kernel; no splitting is
assumed.

Source application: Aschbacher–Smith 5.1.13, printed p.637, the symmetric-five
row in the local Cartan argument.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.FiveBorelFixed
open CubicFixedSpace.Five FiveCentralizerGeometry

private theorem fixed_points : ∀ v : core (Fin 5),
    coreRepresentation (Fin 5) first.val v = v →
    coreRepresentation (Fin 5) second.val v = v → v = 0 ∨ v = z := by
  decide +kernel

/-- A Sylow four-group has at most one nonzero fixed vector. -/
theorem sylow_fixed_unique (P : Sylow 2 (alternatingGroup (Fin 5)))
    (v w : core (Fin 5)) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hv : v ∈ fixedSpace (alternatingCoreRepresentation (Fin 5)) P)
    (hw : w ∈ fixedSpace (alternatingCoreRepresentation (Fin 5)) P) : v = w := by
  obtain ⟨Q,hQ⟩ := klein_isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) Q P
  have hP : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = P := by rw [←hg]; rfl
  let r := alternatingCoreRepresentation (Fin 5)
  have hfixed (x : core (Fin 5)) (hx : x ∈ fixedSpace r P)
      (a : alternatingGroup (Fin 5)) (ha : a ∈ klein) : r a (r g⁻¹ x) = r g⁻¹ x := by
    have hm : g * a * g⁻¹ ∈ (P : Subgroup _) := by
      rw [←hP]
      exact ⟨a,hQ ha,rfl⟩
    have hh₀ : r (g * a * g⁻¹) x = x := hx ⟨_,hm⟩
    have hh := congrArg (r g⁻¹) hh₀
    simpa only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left] using hh
  have hz (x : core (Fin 5)) (hx : x ∈ fixedSpace r P) (hx0 : x ≠ 0) : r g⁻¹ x = z := by
    apply (fixed_points _ (hfixed x hx first first_mem) (hfixed x hx second second_mem)).resolve_left
    intro he
    exact hx0 ((r.apply_bijective g⁻¹).1 (he.trans (map_zero _).symm))
  exact (r.apply_bijective g⁻¹).1 ((hz v hv hv0).trans (hz w hw hw0).symm)

/-- The A₅ Borel fixes the full fixed space of its Sylow four-group. -/
theorem normalizer_fixes (P : Sylow 2 (alternatingGroup (Fin 5)))
    (a : alternatingGroup (Fin 5)) (ha : a ∈ normalizer (P : Set _))
    (v : core (Fin 5)) (hv : v ∈ fixedSpace (alternatingCoreRepresentation (Fin 5)) P) :
    alternatingCoreRepresentation (Fin 5) a v = v := by
  by_cases hz : v = 0
  · rw [hz,map_zero]
  let r := alternatingCoreRepresentation (Fin 5)
  have hm : r a v ∈ fixedSpace r P :=
    (fixedSpace_stable_of_normalizes r (H := normalizer (P : Set _)) le_rfl ha v).2 hv
  exact sylow_fixed_unique P _ v
    (fun he => hz ((r.apply_bijective a).1 (he.trans (map_zero _).symm))) hz hm hv

/-- The same Borel fixation holds on a central extension of the core.
The actual quotient map and its A₅-fixed kernel are retained. -/
theorem normalizer_fixes_lift {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (r : Representation (ZMod 2) (Equiv.Perm (Fin 5)) V)
    (f : V →ₗ[ZMod 2] core (Fin 5)) (hf : Function.Surjective f)
    (he : ∀ g v, f (r g v) = coreRepresentation (Fin 5) g (f v))
    (hk : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5), r g v = v)
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (a : alternatingGroup (Fin 5)) (ha : a ∈ normalizer (P : Set _))
    (v : V) (hv : ∀ g ∈ P, r g.val v = v) : r a.val v = v := by
  obtain ⟨s,hs,hsr,_⟩ := FiveCentralExtension.exists_section r f hf he hk
  have hvf : f v ∈ fixedSpace (alternatingCoreRepresentation (Fin 5)) P := by
    intro g
    exact (he g.val.val v).symm.trans (congrArg f (hv g.val g.property))
  have hfix := normalizer_fixes P a ha (f v) hvf
  have hks : f (v - s (f v)) = 0 := by rw [map_sub,hs,sub_self]
  have hker := hk _ hks a.val a.property
  have hsfix : r a.val (s (f v)) = s (f v) := (hsr a.val (f v)).symm.trans (congrArg s hfix)
  rw [map_sub,hsfix] at hker
  exact sub_left_inj.mp hker
end BinaryPermutation.FiveBorelFixed
