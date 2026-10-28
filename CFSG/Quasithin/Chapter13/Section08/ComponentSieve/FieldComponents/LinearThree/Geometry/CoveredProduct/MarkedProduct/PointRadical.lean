module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.MarkedProduct
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.PointRadical

/-!
# Comparison with the literal point shears

The core mark `pointV` is exactly the range of the point-shear matrices
used by the later tensor consumer. Comparing every matrix entry proves
this equality; the tensor radical is then precisely `pointV × 1`.
No module identification or critical-pair exclusion is used.

Source application: Aschbacher–Smith, 13.8.21(1), printed p.957.
-/

public section
open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.MarkedProduct
open ExternalModules.MarkedCritical

/-- The two independently defined concrete point four-groups coincide. -/
theorem pointV_eq_pointRadical : MarkedAutomorphisms.pointV = pointRadical := by
  ext g
  constructor
  · intro hg
    obtain ⟨h00,h10,h20,h11,h12,h21,h22⟩ := hg
    refine ⟨Multiplicative.ofAdd (g.val 0 1,g.val 0 2),?_⟩
    apply Subtype.ext
    change !![1,g.val 0 1,g.val 0 2; 0,1,0; 0,0,1] = g.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h10,h20,h11,h12,h21,h22]
  · rintro ⟨c,rfl⟩
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The literal tensor actor subgroup is the first-factor core mark. -/
theorem pointV_prod_eq_tensorPointRadical :
    MarkedAutomorphisms.pointV.prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) = tensorPointRadical := by
  rw [tensorPointRadical, ← pointV_eq_pointRadical]
  ext z
  constructor
  · rintro ⟨hz,hz'⟩
    refine ⟨z.1,hz,?_⟩
    exact Prod.ext rfl (mem_bot.mp hz').symm
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.MarkedProduct
