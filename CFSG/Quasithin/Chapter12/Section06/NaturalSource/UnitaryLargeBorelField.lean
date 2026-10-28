module
public import Theory.SpecificGroups.SU3.LargeBorelCubicAction
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupAction.AutomorphismFixedTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Geometry
/-!
# Root-inner actors on an arbitrary marked unitary Borel

Transport the actual image Sylow and its full normalizer to the standard
Hermitian form. Above binary degree three, cubic Borel displacement makes
a two-power actor root inner. Both the original quotient map and the
supplied two-group of actors are retained.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus
namespace CFSG.Quasithin.Chapter12.Section06.UnitaryBorelField
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

theorem large_normalizer_actor_mem_root_inner
    (J : HermitianForm 3 F) {n : ℕ} (hn : 3 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (q : G →* ProjectiveSpecialUnitaryMatrixGroup J) (hq : Function.Surjective q)
    (P : Sylow 2 G) (hk : q.ker ≤ (P : Subgroup G))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : IsPGroup 2 A) (hPA : ((P : Subgroup G).map q).map MulAut.conj ≤ A)
    (α : MulAut G) (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hβ : β ∈ A) (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set G), (α x * x⁻¹)^3 ∈ (P : Subgroup G)) :
    β ∈ ((P : Subgroup G).map q).map MulAut.conj := by
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
  let A' := A.map (MulAut.congr e).toMonoidHom
  have hA' : IsPGroup 2 A' := hA.map _
  have hRA' : (projectiveRoot J₀ rfl).map MulAut.conj ≤ A' := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←hPq] at hx
    obtain ⟨g,hg,rfl⟩ := hx
    refine ⟨MulAut.conj (q g),hPA ⟨q g,⟨g,hg,rfl⟩,rfl⟩,?_⟩
    exact MulAut.congr_conj e (q g)
  have hstep := large_standard_borel_actor_mem_root_inner J₀ rfl hn hcard hconj
    (projectiveBorel_twoCore J₀ n (by omega) hcard hconj rfl) A' hA' hRA' β'
    (mem_map_of_mem (MulAut.congr e).toMonoidHom hβ) hr hcube
  obtain ⟨x,hx,hxβ⟩ := hstep
  rw [←hPq] at hx
  obtain ⟨g,hg,rfl⟩ := hx
  refine ⟨q g,⟨g,hg,rfl⟩,?_⟩
  apply (MulAut.congr e).injective
  exact (MulAut.congr_conj e (q g)).trans hxβ
end CFSG.Quasithin.Chapter12.Section06.UnitaryBorelField
