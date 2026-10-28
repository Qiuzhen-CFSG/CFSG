module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Image
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeExtension
/-!
# The even hexacode action excludes minimal parabolicity

The checked normalizer of the actual even hexacode image is the full
hexacode image. Thus any ambient action with that normal restriction maps
into the full cover; its coordinate projection has image containing A6.
The two six-letter Sylow parabolics contradict minimal parabolicity. The
argument imposes no faithfulness or order condition on the ambient kernel.

Source: Aschbacher–Smith B.6.9 and K.1.3, printed pp.116 and 453.
-/

public section
open Subgroup Representation
open Atlas.Codes Representation.Hexacode.SixDimensional
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
/-- An actual normal even-hexacode restriction is incompatible with minimal parabolicity. -/
theorem not_minimalParabolic_of_even_hexacode
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (ρ : Representation (ZMod 2) G V)
    (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  classical
  let f := coordinateAction ρ e.linearEquiv
  have he (l : L) : f l = hexAction (e.groupEquiv l).val := by
    apply LinearEquiv.ext
    intro w
    change e.linearEquiv ((ρ.comp L.subtype) l (e.linearEquiv.symm w)) =
      Hexacode.evenAction (e.groupEquiv l) w
    rw [e.intertwines, e.linearEquiv.apply_symm_apply]
  have himage : L.map f = evenBinaryImage := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨e.groupEquiv ⟨l, hl⟩, (he ⟨l, hl⟩).symm⟩
    · rintro ⟨l, rfl⟩
      refine ⟨(e.groupEquiv.symm l).val, (e.groupEquiv.symm l).property, ?_⟩
      rw [he, e.groupEquiv.apply_symm_apply]
      rfl
  have hmem (g : G) : f g ∈ hexAction.range := by
    rw [← normalizer_evenBinaryImage, ← himage]
    apply Subgroup.le_normalizer_map f
    exact ⟨g, by rw [L.normalizer_eq_top]; trivial, rfl⟩
  let j := f.codRestrict hexAction.range hmem
  let a : G →* HexAutomorphisms :=
    (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have ha (g : G) : hexAction (a g) = f g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  have hal (l : L) : a l = (e.groupEquiv l).val := by
    apply hexAction_injective
    rw [ha, he]
  have hr : hexSign.ker ≤ a.range := by
    intro l hl
    refine ⟨(e.groupEquiv.symm ⟨l, hl⟩).val, ?_⟩
    rw [hal, e.groupEquiv.apply_symm_apply]
  have hA : alternatingGroup (Fin 6) ≤ (hexCoordinateSixHom.comp a).range := by
    intro x hx
    obtain ⟨y,hy⟩ := hexEvenCoordinate_surjective ⟨x,hx⟩
    obtain ⟨g,hg⟩ := hr y.property
    refine ⟨g,?_⟩
    change hexCoordinateSixHom (a g) = x
    rw [hg]
    exact congrArg Subtype.val hy
  exact not_minimalParabolic_of_six_image T _ hA
end CFSG.Quasithin.ChapterB
