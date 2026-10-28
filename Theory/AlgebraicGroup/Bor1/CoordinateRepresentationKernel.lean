module

public import Theory.AlgebraicGroup.RightTranslation.Representation

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! The faithful regular coordinate representation has trivial point kernel. -/

set_option linter.unusedSectionVars false in
public theorem Morphism.kernel_eq_bot_of_injective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hinj : Function.Injective f.onPoints) :
    f.kernel = (⊥ : Subgroup (Variety.Point G)) := by
  ext g
  change f.onPoints g = 1 ↔ g ∈ (⊥ : Subgroup (Variety.Point G))
  constructor
  · intro hg
    have hge : f.onPoints g = f.onPoints 1 := by
      simpa using hg
    have hgid : g = 1 := hinj hge
    simp [hgid]
  · intro hg
    have hgid : g = 1 := Subgroup.mem_bot.mp hg
    simp [hgid]

set_option linter.unusedSectionVars false in
public theorem Morphism.kernelClosedSubgroup_eq_bot_of_injective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hinj : Function.Injective f.onPoints) :
    f.kernelClosedSubgroup = (ClosedSubgroup.bot : ClosedSubgroup G) := by
  let f' := f
  change ClosedSubgroup.ofSubgroup f'.kernel _ =
    ClosedSubgroup.ofSubgroup (⊥ : Subgroup (Variety.Point G)) _
  congr 1
  exact Morphism.kernel_eq_bot_of_injective f hinj

public theorem coordinateTranslationRepresentationMorphism_kernel_eq_bot
    (G : Variety k) [AlgebraicGroup G] :
    (coordinateTranslationRepresentationMorphism G).kernel =
      (⊥ : Subgroup (Variety.Point G)) := by
  exact Morphism.kernel_eq_bot_of_injective
    (coordinateTranslationRepresentationMorphism G)
    (coordinateTranslationRepresentationMorphism_injective G)

public theorem coordinateTranslationRepresentationMorphism_kernelClosedSubgroup_eq_bot
    (G : Variety k) [AlgebraicGroup G] :
    (coordinateTranslationRepresentationMorphism G).kernelClosedSubgroup =
      (ClosedSubgroup.bot : ClosedSubgroup G) := by
  exact Morphism.kernelClosedSubgroup_eq_bot_of_injective
    (coordinateTranslationRepresentationMorphism G)
    (coordinateTranslationRepresentationMorphism_injective G)

end Theory.AlgebraicGroup
