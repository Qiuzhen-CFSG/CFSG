module
public import Theory.SpecificGroups.SU3.EvenBorelCubicAction
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Geometry
/-!
# Cubic displacement on an arbitrary marked unitary Borel

Transport the actual image Sylow and its full normalizer to the standard
Hermitian form. Semilinear rigidity then kills cubic displacement in even
degree. Pulling back through the supplied quotient recovers precisely the
original Sylow kernel; no Hall complement is assumed invariant.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus
namespace CFSG.Quasithin.Chapter12.Section06.UnitaryBorelField
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

theorem normalizer_displacement_mem_of_cube
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (q : G →* ProjectiveSpecialUnitaryMatrixGroup J) (hq : Function.Surjective q)
    (P : Sylow 2 G) (hk : q.ker ≤ (P : Subgroup G))
    (α : MulAut G) (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set G), (α x * x⁻¹)^3 ∈ (P : Subgroup G)) :
    ∀ x ∈ normalizer (P : Set G), α x * x⁻¹ ∈ (P : Subgroup G) := by
  let R := P.mapSurjective hq
  obtain ⟨e,hR,hN⟩ := psu_borel_model J n (by omega) hcard hconj R
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  let q' := e.toMonoidHom.comp q
  let β' := MulAut.congr e β
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hk' : q'.ker ≤ (P : Subgroup G) := by
    intro x hx
    exact hk (e.map_eq_one_iff.mp hx)
  have hPq : (P : Subgroup G).map q' = projectiveRoot J₀ rfl := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact hR
  have hNq : (normalizer (P : Set G)).map q' = projectiveBorel J₀ rfl := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map,
      P.normalizer_map_surjective q hq]
    exact hN
  have he' (x : G) : q' (α x) = β' (q' x) := by
    change e (q (α x)) = e (β (e.symm (e (q x))))
    rw [he,e.symm_apply_apply]
  have hr : (projectiveRoot J₀ rfl).map β'.toMonoidHom = projectiveRoot J₀ rfl := by
    have heq : β'.toMonoidHom.comp q' = q'.comp α.toMonoidHom :=
      MonoidHom.ext (fun x => (he' x).symm)
    rw [←hPq,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  have hcube : ∀ x ∈ projectiveBorel J₀ rfl,
      (β' x * x⁻¹)^3 ∈ projectiveRoot J₀ rfl := by
    intro x hx
    rw [←hNq] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem q' (hc y hy)
    rw [hPq] at hh
    simpa only [map_pow,map_mul,map_inv,he'] using hh
  have hstep := standard_borel_displacement_mem_of_cube J₀ rfl hn heven hcard hconj
    (projectiveBorel_twoCore J₀ n (by omega) hcard hconj rfl) β' hr hcube
  intro x hx
  have hm : q' x ∈ projectiveBorel J₀ rfl := hNq ▸ mem_map_of_mem q' hx
  have hh := hstep (q' x) hm
  rw [←hPq,←he',←map_inv,←map_mul] at hh
  change α x * x⁻¹ ∈ ((P : Subgroup G).map q').comap q' at hh
  rwa [comap_map_eq_self hk'] at hh
end CFSG.Quasithin.Chapter12.Section06.UnitaryBorelField
