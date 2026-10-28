module
public import Theory.GroupTheory.AbelianConjugateSpan
public import Mathlib.Tactic.Group

/-!
# Escaping an overgroup by fusion across conjugate modules

If H controls fusion of u into A, a conjugate A^g containing u can be
reached by an element of C_G(u). If A and A^g do not commute, that element
escapes every M normalizing an abelian subgroup containing A.

Source: Aschbacher--Smith, A.1.7 and 14.6.17(4), printed p.1036.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A single matching pair of vectors suffices for the crossing argument. -/
theorem centralizer_not_le_of_crossing_match
    (A H U M : Subgroup G) [IsMulCommutative U]
    (hAU : A ≤ U) (hHA : H ≤ normalizer (A : Set G))
    (hMU : M ≤ normalizer (U : Set G))
    (u g : G)
    (hmatch : ∃ x ∈ H, (MulAut.conj x) u = (MulAut.conj g⁻¹) u)
    (hcross : ¬ A ≤ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)) :
    ¬ centralizer ({u} : Set G) ≤ M := by
  obtain ⟨x,hx,hxu⟩ := hmatch
  let c := g * x
  have hcu : c ∈ centralizer ({u} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) hxu
    have hfix : c * u * c⁻¹ = u := by
      simpa [c, MulAut.conj_apply, mul_assoc] using hh
    exact (mul_inv_eq_iff_eq_mul.mp hfix)
  intro hCM
  have himage : A.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro y ⟨b,hb,rfl⟩
    have hb' : x⁻¹ * b * x ∈ A := by
      simpa using (hHA (H.inv_mem hx) b).mp hb
    have hh := (hMU (hCM hcu) (x⁻¹ * b * x)).mp (hAU hb')
    simpa [c, MulAut.conj_apply, mul_assoc] using hh
  apply hcross
  intro a ha b hb
  exact setLike_mul_comm (himage hb) (hAU ha)

/-- Fusion control supplies the matching pair whenever the conjugate contains u. -/
theorem centralizer_not_le_of_crossing_fusion
    (A H U M : Subgroup G) [IsMulCommutative U]
    (hAU : A ≤ U) (hHA : H ≤ normalizer (A : Set G))
    (hMU : M ≤ normalizer (U : Set G))
    (u g : G) (hu : u ∈ A.map (MulAut.conj g).toMonoidHom)
    (hfusion : ∀ x : G, (MulAut.conj x) u ∈ A →
      ∃ h ∈ H, (MulAut.conj h) u = (MulAut.conj x) u)
    (hcross : ¬ A ≤ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)) :
    ¬ centralizer ({u} : Set G) ≤ M := by
  obtain ⟨a,ha,he⟩ := hu
  have hin : (MulAut.conj g⁻¹) u ∈ A := by
    rw [←he]
    simpa [MulAut.conj_apply, mul_assoc] using ha
  exact centralizer_not_le_of_crossing_match A H U M hAU hHA hMU u g
    (hfusion g⁻¹ hin) hcross

end Subgroup
