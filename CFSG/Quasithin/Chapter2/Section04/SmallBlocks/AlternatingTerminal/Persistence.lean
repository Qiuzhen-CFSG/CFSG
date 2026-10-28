module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPersistence
public import Theory.GroupTheory.PCoreOvergroup

/-!
# The guarded local overgroups in the paired alternating-five argument

For an actual characteristic-two overgroup X and a Sylow subgroup containing
SI, its join with the original block still has characteristic two. The proved
starred persistence statement applies to that join. Thus the same literal
block is a local C-component at every such Sylow subgroup of X. No replacement
of the half-Sylow SI by an ambient Sylow subgroup is made.

Source: Aschbacher–Smith 2.4.25, printed pp.542–543. The model-specific escaping
overgroup remains a separate producer; this module proves its exact source
consumer from the original minimal-block hypotheses.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual half-Sylow base retains the block in every guarded local family. -/
theorem MinimalBlockSetup.alternating_persistence_overgroup
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    {R X : Subgroup G}
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hi : R.relIndex ((d.S : Subgroup d.H).map d.H.subtype) = 2)
    (hR : R ∈ beta M)
    (hL : d.block.map d.H.subtype ∈ Chapter1.L G R)
    (hX : X ∈ Chapter1.He G) (hLX : d.block.map d.H.subtype ≤ X)
    (P : Sylow 2 X) (hRP : R ≤ (P : Subgroup X).map X.subtype) :
    d.block.map d.H.subtype ∈ ChapterA.Section03.localCComponents
      ((P : Subgroup X).map X.subtype) := by
  let L := d.block.map d.H.subtype
  let Y := L ⊔ (P : Subgroup X).map X.subtype
  have hYX : Y ≤ X := sup_le hLX (map_subtype_le _)
  have hPY : (P : Subgroup X) ≤ Y.subgroupOf X := by
    intro p hp
    exact (show (P : Subgroup X).map X.subtype ≤ Y from le_sup_right)
      (mem_map_of_mem X.subtype hp)
  let e : Y.subgroupOf X ≃* Y := subgroupOfEquivOfLe hYX
  let PY : Sylow 2 Y := (P.subtype hPY).mapSurjective (f := e.toMonoidHom) e.surjective
  have hPeq : (PY : Subgroup Y).map Y.subtype = (P : Subgroup X).map X.subtype := by
    change (((P : Subgroup X).subgroupOf (Y.subgroupOf X)).map e.toMonoidHom).map Y.subtype = _
    rw [map_map]
    ext g
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact mem_map_of_mem X.subtype hp
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,hPY hp⟩,hp,rfl⟩
  have hYe : Y ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    exact centralizer_pCore_le_of_sylow_le P (Y.subgroupOf X) hPY
      (Chapter1.mem_He_iff.mp hX)
  have hpersist := d.alternating_persistence hG T hTM hu hRS hi hR hL hYe PY
    (hPeq.symm ▸ hRP) (by change Y = L ⊔ _; rw [hPeq])
  exact hpersist

end CFSG.Quasithin.Chapter2