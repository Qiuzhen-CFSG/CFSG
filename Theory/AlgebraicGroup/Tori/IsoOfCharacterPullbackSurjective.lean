module

public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Tori.Character.PullbackSurjective
public import Theory.AlgebraicGroup.Variety.InjectiveOfPullbackSurjective

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A point-surjective morphism of tori is an isomorphism when its pullback on
character lattices is surjective. -/
public theorem torusIso_of_surjective_of_character_pullback_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsTorus G) (hH : IsTorus H)
    (f : AlgebraicGroup.Morphism G H)
    (hsurjective : Function.Surjective f.onPoints)
    (hcharacters : Function.Surjective (TorusCharacter.pullback f)) :
    ∃ e : AlgebraicGroup.Iso G H, e.hom = f := by
  have hpull : Function.Surjective f.toVariety.pullbackRingHom :=
    torusMorphism_pullbackRingHom_surjective_of_character_pullback_surjective
      hG hH f hcharacters
  have hinjective : Function.Injective f.onPoints :=
    f.toVariety.injective_of_pullbackRingHom_surjective hpull
  exact algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
    f ⟨hinjective, hsurjective⟩ hpull

end Theory.AlgebraicGroup
