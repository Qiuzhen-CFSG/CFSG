module
public import Theory.GroupTheory.AmalgamGraph.SylowCenterSpan

/-!
# Sylow-center spans under an embedding

An injective homomorphism transports the whole Sylow-center span, with
all Sylows, omega-centers and subgroup inclusions carried by that same
map. The ambient groups need not be isomorphic or finite.

Source: DGS, Groups and Graphs (1985), notation p.81. The reduced-to-original
application is DGS85/LocalStructure/LinearNoncentralApplication.
-/

open Subgroup
public noncomputable section
namespace Theory.GroupTheory.AmalgamGraph
variable {G H : Type*} [Group G] [Group H]
private theorem sylow_image (f : G →* H) (hf : Function.Injective f) (P : Subgroup G) [Finite P]
    (T : Sylow 2 P) :
    let e := P.equivMapOfInjective f hf
    ((T.mapSurjective (f := e.toMonoidHom) e.surjective :
      Subgroup (P.map f)).map (P.map f).subtype) =
        ((T : Subgroup P).map P.subtype).map f := by
  dsimp only
  change ((T : Subgroup P).map _).map _ = _
  rw [map_map, map_map]
  rfl

/-- Every Sylow and its actual center embedding are transported by the same map. -/
theorem sylowCenterSpan_map_of_injective (f : G →* H) (hf : Function.Injective f) (P : Subgroup G) [Finite P] :
    sylowCenterSpan (P.map f) = (sylowCenterSpan P).map f := by
  let e := P.equivMapOfInjective f hf
  apply le_antisymm
  · apply iSup_le
    intro T'
    obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective
      (f := e.toMonoidHom) e.surjective 2 T'
    rw [sylow_image f hf P T, ← NilesRankOneKernel.omegaCenterIn_map_injective _ hf]
    exact map_mono (le_iSup (fun T : Sylow 2 P =>
      omegaCenterIn ((T : Subgroup P).map P.subtype)) T)
  · rw [sylowCenterSpan, Subgroup.map_iSup]
    apply iSup_le
    intro T
    rw [NilesRankOneKernel.omegaCenterIn_map_injective _ hf,
      ← sylow_image f hf P T]
    exact le_iSup (fun T' : Sylow 2 (P.map f) =>
      omegaCenterIn ((T' : Subgroup (P.map f)).map
        (P.map f).subtype)) _

end Theory.GroupTheory.AmalgamGraph
