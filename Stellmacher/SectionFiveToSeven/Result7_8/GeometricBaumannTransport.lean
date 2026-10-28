module
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction
public import Stellmacher.BaumannMap

/-!
# Transport the selected Baumann bound to the extracted edge

Keep a supplied geometric extraction, its exact generated subgroup E,
and a Sylow two-subgroup U of the original edge. A residual commutator
bound involving the Baumann subgroup of U transports to a Sylow subgroup
of the actual extracted edge. This produces one compatible new Sylow
choice and retains the same subgroup O²(E).

The extraction's conjugator x lies in O²(E), hence in E and the fixed
vertex stabilizer. Conjugation by x maps the original edge intersection
onto the new one and transports U through the resulting surjective
homomorphism. Since x lies in O²(E), it normalizes that residual subgroup.
Injective Baumann covariance and the commutator map formula therefore
transport the given bound to the selected new Sylow image.

This is the bridge needed for Stellmacher (9.3)(3), Journal of Algebra
190 (1997), p.49, from the prescribed-Sylow (7.8) configuration to its
geometric extracted edge. Source: `refs/files/stellmacher-n-group.pdf`.
The generic geometric data retain their established SectionNine namespace,
but this theorem belongs to the shared (7.8) layer. It asserts no uniform
bound over all Sylow subgroups and changes no extraction witness.
-/
namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext Stellmacher.SectionNine
universe u

public theorem geometric_extraction_baumann_transport
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex)
    (A E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ d l A E A0 actor)
    (U : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l))
    (hbound : twoResidualAmbient E ≤ ⁅twoResidualAmbient E,
      baumannIn (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) U)⁆) :
    ∃ Unew : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ (Γ.act data.x⁻¹ l)),
      twoResidualAmbient E ≤ ⁅twoResidualAmbient E,
        baumannIn (sylowTwoAmbient
          (stabilizer Γ d ⊓ stabilizer Γ (Γ.act data.x⁻¹ l)) Unew)⁆ := by
  let D := stabilizer Γ d ⊓ stabilizer Γ l
  let Dnew := stabilizer Γ d ⊓ stabilizer Γ (Γ.act data.x⁻¹ l)
  let c := MulAut.conj data.x
  have hxE : data.x ∈ E := Subgroup.map_subtype_le _ data.residual_mem
  have hxP : data.x ∈ stabilizer Γ d := data.group_le hxE
  have hPd : (stabilizer Γ d).map c.toMonoidHom = stabilizer Γ d :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((stabilizer Γ d).le_normalizer hxP)
  have hGnew : stabilizer Γ (Γ.act data.x⁻¹ l) =
      (stabilizer Γ l).map c.toMonoidHom := by
    rw [stabilizer_act,inv_inv]
    rfl
  have hDmap : D.map c.toMonoidHom = Dnew := by
    rw [show D = stabilizer Γ d ⊓ stabilizer Γ l from rfl,
      Subgroup.map_inf _ _ _ c.injective,hPd,← hGnew]
  let f : D →* Dnew := (c.toMonoidHom.comp D.subtype).codRestrict Dnew
    (fun a => hDmap ▸ Subgroup.mem_map_of_mem c.toMonoidHom a.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨a,ha,hab⟩ := Subgroup.mem_map.mp (hDmap.ge b.property)
    exact ⟨⟨a,ha⟩,Subtype.ext hab⟩
  let Unew := U.mapSurjective hf
  have hUmap : sylowTwoAmbient Dnew Unew =
      (sylowTwoAmbient D U).map c.toMonoidHom := by
    change ((U : Subgroup D).map f).map Dnew.subtype =
      ((U : Subgroup D).map D.subtype).map c.toMonoidHom
    rw [Subgroup.map_map,Subgroup.map_map]
    rfl
  have hRmap : (twoResidualAmbient E).map c.toMonoidHom = twoResidualAmbient E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((twoResidualAmbient E).le_normalizer data.residual_mem)
  have hBmap : (baumannIn (sylowTwoAmbient D U)).map c.toMonoidHom =
      baumannIn (sylowTwoAmbient Dnew Unew) := by
    rw [hUmap]
    exact baumann_map_injective c.toMonoidHom c.injective _
  refine ⟨Unew,?_⟩
  have hm := Subgroup.map_mono (f := c.toMonoidHom) hbound
  rw [Subgroup.map_commutator,hRmap,hBmap] at hm
  exact hm
end Stellmacher.SectionsFiveToSeven
