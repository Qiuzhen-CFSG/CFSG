module

public import Theory.AlgebraicGroup.Tori.Character.Algebra
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Surjectivity of coordinate pullback between tori forces surjectivity on
character lattices. -/
public theorem torusCharacter_pullback_surjective_of_pullbackRingHom_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsTorus G) (hH : IsTorus H)
    (f : AlgebraicGroup.Morphism G H)
    (hpull : Function.Surjective f.toVariety.pullbackRingHom) :
    Function.Surjective (TorusCharacter.pullback f) := by
  let eG := torusCharacterAlgebraEquiv G
    hG.isMulCommutative (IsTorus.all_semisimple hG)
  let eH := torusCharacterAlgebraEquiv H
    hH.isMulCommutative (IsTorus.all_semisimple hH)
  let mapCharacters := MonoidAlgebra.mapDomainAlgHom k k
    (TorusCharacter.pullback f)
  have hmap : Function.Surjective mapCharacters := by
    intro bG
    obtain ⟨qH, hqH⟩ := hpull (eG bG)
    let bH := eH.symm qH
    refine ⟨bH, ?_⟩
    apply eG.injective
    have hnatural := congrArg (fun F => F bH)
      (torusCharacterAlgebraEquiv_naturality
        hG.isMulCommutative (IsTorus.all_semisimple hG)
        hH.isMulCommutative (IsTorus.all_semisimple hH) f)
    calc
      eG (mapCharacters bH) =
          f.toVariety.pullbackRingHom (eH bH) := hnatural.symm
      _ = f.toVariety.pullbackRingHom qH := by
        rw [show eH bH = qH from eH.apply_symm_apply qH]
      _ = eG bG := hqH
  intro χ
  obtain ⟨bH, hbH⟩ := hmap (MonoidAlgebra.single χ 1)
  by_contra hχ
  have hnot : χ ∉ Set.range (TorusCharacter.pullback f) := by
    simpa only [Set.mem_range, not_exists] using hχ
  have hzero : (mapCharacters bH).coeff χ = 0 := by
    exact Finsupp.mapDomain_of_notMem_range bH.coeff χ hnot
  rw [hbH] at hzero
  change (Finsupp.single χ (1 : k)) χ = 0 at hzero
  rw [Finsupp.single_eq_same] at hzero
  exact one_ne_zero hzero

end Theory.AlgebraicGroup
