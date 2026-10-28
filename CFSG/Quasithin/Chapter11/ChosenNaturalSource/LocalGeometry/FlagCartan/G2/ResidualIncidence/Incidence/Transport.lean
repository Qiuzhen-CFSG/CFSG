module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Incidence transport through the original central quotient

The original coordinate preimage preserves intersection and sum. In the sum
argument, a lift of one summand leaves the other summand as an actual element
of V, so the entire common central kernel is retained. Conjugation by L
commutes with preimage under the literal marked quotient action. These lemmas
transport the two explicit G₂ planes to the original ambient subgroups.

Source: Aschbacher--Smith, opening §11.1 and 11.1.4, pp.760--761,765.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Coordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} (c : Coordinates D F)

/-- Intersections lift to intersections of full ambient preimages. -/
theorem preimage_inf (U W : Submodule F.Carrier c.Space) :
    c.preimage (U ⊓ W) = c.preimage U ⊓ c.preimage W := by
  apply le_antisymm
  · exact le_inf ((c.preimage_le_iff _ _).mpr inf_le_left)
      ((c.preimage_le_iff _ _).mpr inf_le_right)
  · intro x hx
    let v : V := ⟨x,D.centralQuotientPreimage_le _ hx.1⟩
    exact (c.mem_preimage _ v).mpr
      ⟨(c.mem_preimage _ v).mp hx.1,(c.mem_preimage _ v).mp hx.2⟩

/-- Sums lift to subgroup joins, including the common central kernel. -/
theorem preimage_sup (U W : Submodule F.Carrier c.Space) :
    c.preimage (U ⊔ W) = c.preimage U ⊔ c.preimage W := by
  apply le_antisymm
  · intro x hx
    let v : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
    have hv : (c.projection v).toAdd ∈ U ⊔ W := (c.mem_preimage _ v).mp hx
    obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp hv
    obtain ⟨y,hy⟩ := c.projection_surjective (Multiplicative.ofAdd u)
    have hyU : y.val ∈ c.preimage U := (c.mem_preimage _ y).mpr (by
      change (c.projection y).toAdd ∈ U
      rw [hy]
      exact hu)
    have hz : (y⁻¹*v).val ∈ c.preimage W := (c.mem_preimage _ (y⁻¹*v)).mpr (by
      change (c.projection (y⁻¹*v)).toAdd ∈ W
      rw [map_mul, map_inv, hy]
      change -u + (c.projection v).toAdd ∈ W
      rw [← he]
      simpa using hw)
    have hh := (c.preimage U ⊔ c.preimage W).mul_mem
      ((show c.preimage U ≤ c.preimage U ⊔ c.preimage W from le_sup_left) hyU)
      ((show c.preimage W ≤ c.preimage U ⊔ c.preimage W from le_sup_right) hz)
    simpa using hh
  · exact sup_le ((c.preimage_le_iff _ _).mpr le_sup_left)
      ((c.preimage_le_iff _ _).mpr le_sup_right)

private theorem preimage_conjugate_le (l : L) (U : Submodule F.Carrier c.Space) :
    (c.preimage U).map (MulAut.conj (l : G)).toMonoidHom ≤
      c.preimage (U.map (c.modelAction (c.quotientMap l))) := by
  rintro _ ⟨x,hx,rfl⟩
  let v : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
  let w := V.normalizerMonoidHom (inclusion D.normalizes l) v
  change (w : G) ∈ _
  apply (c.mem_preimage _ w).mpr
  change (c.projection w).toAdd ∈ _
  rw [show (c.projection w).toAdd = c.modelAction (c.quotientMap l) (c.projection v).toAdd from
    c.projection_component_conjugation l v]
  exact Submodule.mem_map.mpr ⟨_,(c.mem_preimage _ v).mp hx,rfl⟩

/-- Original ambient conjugation agrees with the marked quotient action. -/
theorem preimage_conjugate (l : L) (U : Submodule F.Carrier c.Space) :
    (c.preimage U).map (MulAut.conj (l : G)).toMonoidHom =
      c.preimage (U.map (c.modelAction (c.quotientMap l))) := by
  apply le_antisymm (preimage_conjugate_le c l U)
  intro x hx
  have hi := preimage_conjugate_le c l⁻¹ (U.map (c.modelAction (c.quotientMap l)))
  have he : (c.modelAction (c.quotientMap l⁻¹)).comp
      (c.modelAction (c.quotientMap l)) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, LinearMap.id_apply]
  rw [← Submodule.map_comp, he, Submodule.map_id] at hi
  refine ⟨(MulAut.conj (l : G)).symm x, hi ?_, ?_⟩
  · simpa using mem_map_of_mem (MulAut.conj ((l⁻¹ : L) : G)).toMonoidHom hx
  · exact (MulAut.conj (l : G)).apply_symm_apply x

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Coordinates
