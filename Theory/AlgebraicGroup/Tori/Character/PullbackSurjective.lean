module

public import Theory.AlgebraicGroup.Tori.Character.Algebra
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Surjectivity on character lattices makes the pullback on coordinate rings
surjective for a morphism between tori. -/
public theorem torusMorphism_pullbackRingHom_surjective_of_character_pullback_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsTorus G) (hH : IsTorus H)
    (f : AlgebraicGroup.Morphism G H)
    (hcharacters : Function.Surjective (TorusCharacter.pullback f)) :
    Function.Surjective f.toVariety.pullbackRingHom := by
  let eG := torusCharacterAlgebraEquiv G
    hG.isMulCommutative (IsTorus.all_semisimple hG)
  let eH := torusCharacterAlgebraEquiv H
    hH.isMulCommutative (IsTorus.all_semisimple hH)
  intro q
  obtain ⟨bG, hbG⟩ := eG.surjective q
  obtain ⟨bHcoeff, hbH⟩ :=
    Finsupp.mapDomain_surjective (M := k) hcharacters bG.coeff
  let bH : MonoidAlgebra k (TorusCharacter H) :=
    MonoidAlgebra.ofCoeff bHcoeff
  have hbH' :
      (MonoidAlgebra.mapDomainAlgHom k k
        (TorusCharacter.pullback f)) bH = bG := by
    apply MonoidAlgebra.coeff_injective
    exact hbH
  refine ⟨eH bH, ?_⟩
  have hnatural := congrArg (fun F => F bH)
    (torusCharacterAlgebraEquiv_naturality
      hG.isMulCommutative (IsTorus.all_semisimple hG)
      hH.isMulCommutative (IsTorus.all_semisimple hH) f)
  calc
    f.toVariety.pullbackRingHom (eH bH) =
        eG ((MonoidAlgebra.mapDomainAlgHom k k
          (TorusCharacter.pullback f)) bH) := hnatural
    _ = eG bG := congrArg eG hbH'
    _ = q := hbG

end Theory.AlgebraicGroup
