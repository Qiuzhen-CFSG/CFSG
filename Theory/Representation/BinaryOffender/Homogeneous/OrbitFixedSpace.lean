module

public import Theory.Representation.BinaryOffender.Homogeneous.OrbitConsequences
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding

/-!
# Fixed vectors in an irreducible seed's orbit

Restricting the original action to the orbit span makes the seed generate
the whole module. The fixed-space orbit theorem then applies, and the
original inclusion maps its equality back to the ambient module.

Source: Aschbacher–Smith, D.3.4(4), combined manuscript of 1 March 2004,
printed p.193; applied to the original subgroups in 3.2.2(4), p.579.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender.Homogeneous
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

theorem orbitSpan_inf_fixedSpace (X : Subgroup D) [X.Normal]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    orbitSpan ρ ⊤ I ⊓ fixedSpace ρ X = orbitSpan ρ ⊤ (I ⊓ fixedSpace ρ X) := by
  let W := orbitSpan ρ ⊤ I
  have hW : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W := orbitSpan_invariant ρ ⊤ I
  let S : Subrepresentation ρ := ⟨W, fun d _ hv => (hW (mem_top d) _).mpr hv⟩
  let τ : Representation (ZMod 2) D W := S.toRepresentation
  have hi : IsIrrPlus τ X (I.comap W.subtype) := by
    apply hI.of_intertwining ρ τ (MonoidHom.id X) Function.surjective_id W.subtype
      W.subtype_injective (fun _ _ => rfl)
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (le_orbitSpan ρ ⊤ I)]
  have hg : orbitSpan τ ⊤ (I.comap W.subtype) = ⊤ := by
    apply Submodule.map_injective_of_injective W.subtype_injective
    rw [orbitSpan_map_equivariant τ ρ (MonoidHom.id D) W.subtype (fun _ _ => rfl),
      Subgroup.map_id, Submodule.map_comap_subtype,
      inf_eq_right.mpr (le_orbitSpan ρ ⊤ I), Submodule.map_top, Submodule.range_subtype]
  have hfix : fixedSpace τ X = (fixedSpace ρ X).comap W.subtype := by
    ext v
    exact ⟨fun h x => congrArg Subtype.val (h x), fun h x => Subtype.ext (h x)⟩
  have he := congrArg (Submodule.map W.subtype) (fixedSpace_eq_orbitSpan_inf τ X hi hg)
  rw [orbitSpan_map_equivariant τ ρ (MonoidHom.id D) W.subtype (fun _ _ => rfl),
    Subgroup.map_id, hfix, ← Submodule.comap_inf,
    Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    inf_eq_right.mpr (inf_le_left.trans (le_orbitSpan ρ ⊤ I))] at he
  simpa only [inf_comm] using he

end Representation.BinaryOffender.Homogeneous
