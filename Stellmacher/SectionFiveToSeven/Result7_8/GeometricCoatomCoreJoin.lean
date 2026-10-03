module
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction
/-!
# The geometric actor coatom lies in the incident cores

For the exact geometric extraction at d,l, with new vertex m, the actor
coatom A₀ lies in Q_d∨Q_m. The residual conjugator belongs to E, so its
commutator with A₀ lies in Q_d. The conjugate of A₀ belongs to the
conjugated actor module, hence to Q_m. Multiplying the inverse commutator
by that conjugate recovers the original element of A₀.

This gives containment of the normalized second coatom in the actual
chosen Sylow subgroup in (9.3): both incident cores lie in every incident
edge Sylow. It does not require that an entire edge stabilizer equal that
Sylow subgroup. The statement is a supplementary consequence of the
geometric data in Stellmacher (9.3)(i),(ii),(v), Journal of Algebra 190
(1997), pp.49–50, `refs/files/stellmacher-n-group.pdf`.
-/
namespace Stellmacher.SectionNine
open SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem geometric_coatom_le_core_join
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (d l : Γ.Vertex)
    (V E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ d l V E A0 actor) :
    A0 ≤ q Γ d ⊔ q Γ (Γ.act data.x⁻¹ l) := by
  have hxE : data.x ∈ E := Subgroup.map_subtype_le _ data.residual_mem
  have h0V : A0 ≤ V := data.coatom_eq.le.trans inf_le_left
  intro a ha
  have hc : ⁅data.x,a⁆ ∈ q Γ d :=
    data.coatom_commutator (Subgroup.commutator_mem_commutator hxE ha)
  have hxax : data.x*a*data.x⁻¹ ∈ q Γ (Γ.act data.x⁻¹ l) :=
    data.conjugate_core_le (Subgroup.mem_map_of_mem (MulAut.conj data.x).toMonoidHom (h0V ha))
  have hh := (q Γ d ⊔ q Γ (Γ.act data.x⁻¹ l)).mul_mem
    ((show q Γ d ≤ q Γ d ⊔ q Γ (Γ.act data.x⁻¹ l) from le_sup_left)
      ((q Γ d).inv_mem hc))
    ((show q Γ (Γ.act data.x⁻¹ l) ≤ q Γ d ⊔ q Γ (Γ.act data.x⁻¹ l) from le_sup_right) hxax)
  simpa [commutatorElement_def,mul_assoc] using hh

end Stellmacher.SectionNine
