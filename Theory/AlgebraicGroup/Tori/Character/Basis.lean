module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Theory.AlgebraicGroup.Dimension.Torus
public import Theory.AlgebraicGroup.Tori.Character.Duality
public import Theory.AlgebraicGroup.Tori.Character.FiniteGeneration
public import Theory.AlgebraicGroup.Tori.Character.Tuple

universe u

/-! Integral character bases and reconstruction of tori from characters. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def torusCharacterBasisData
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t)
    (hconnected : Variety.IsConnected T) :
    Σ n : ℕ, Module.Basis (Fin n) ℤ (Additive (TorusCharacter T)) := by
  let : Group.FG (TorusCharacter T) :=
    torusCharacter_finitelyGenerated T hcomm hsemi
  let : AddGroup.FG (Additive (TorusCharacter T)) := inferInstance
  let : Module.Finite ℤ (Additive (TorusCharacter T)) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  let : IsMulTorsionFree (TorusCharacter T) :=
    torusCharacter_isTorsionFree_of_isConnected T hconnected
  let : IsAddTorsionFree (Additive (TorusCharacter T)) := inferInstance
  let : Module.IsTorsionFree ℤ (Additive (TorusCharacter T)) :=
    inferInstance
  exact Module.basisOfFiniteTypeTorsionFree'

private noncomputable def torusCharacterBasisMulEquiv
    (T : Variety k) [AlgebraicGroup T] (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) :
    TorusCharacter (dVariety k n) ≃* TorusCharacter T :=
  MulEquiv.toAdditive.symm
    ((dLaurentCharacterAddEquiv (k := k) n).symm.trans
      b.equivFun.symm.toAddEquiv)

private noncomputable def torusCharacterBasisTupleMorphism
    (T : Variety k) [AlgebraicGroup T] (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) :
    AlgebraicGroup.Morphism T (dVariety k n) :=
  torusCharacterTupleMorphism T n (fun i => Additive.toMul (b i))

omit [IsAlgClosed k] in
private lemma pullback_tuple_coordinate
    (T : Variety k) [AlgebraicGroup T] (n : ℕ)
    (χ : Fin n → TorusCharacter T) (i : Fin n) :
    TorusCharacter.pullback (torusCharacterTupleMorphism T n χ)
        (dCoordinateCharacter n i) = χ i := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  apply (dPointEquiv 1).injective
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  change dPointEquiv n
      ((torusCharacterTupleMorphism T n χ).onPoints x) i =
    dPointEquiv 1 ((χ i).onPoints x) 0
  exact torusCharacterTupleMorphism_apply T n χ x i

private lemma basisMulEquiv_coordinate
    (T : Variety k) [AlgebraicGroup T] (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (Additive (TorusCharacter T)))
    (i : Fin n) :
    torusCharacterBasisMulEquiv T n b (dCoordinateCharacter n i) =
      Additive.toMul (b i) := by
  change Additive.toMul
      (b.equivFun.symm
        ((dLaurentCharacterAddEquiv (k := k) n).symm
          (Additive.ofMul (dCoordinateCharacter n i)))) =
    Additive.toMul (b i)
  congr 1
  rw [← b.equivFun.injective.eq_iff, b.equivFun.apply_symm_apply]
  have hb : b.equivFun (b i) = Pi.single i 1 := by
    ext j
    rw [b.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  rw [hb]
  apply (dLaurentCharacterAddEquiv (k := k) n).injective
  rw [(dLaurentCharacterAddEquiv (k := k) n).apply_symm_apply]
  change Additive.ofMul (dCoordinateCharacter n i) =
    Additive.ofMul (dLaurentCharacter n (Pi.single i 1))
  congr 1
  symm
  simp [dLaurentCharacter, Pi.single_apply]

private lemma torusCharacterBasisTupleMorphism_pullback
    (T : Variety k) [AlgebraicGroup T] (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) :
    TorusCharacter.pullback (torusCharacterBasisTupleMorphism T n b) =
      (torusCharacterBasisMulEquiv T n b).toMonoidHom := by
  ext δ
  obtain ⟨z, rfl⟩ := dLaurentCharacter_surjective (k := k) n δ
  simp only [dLaurentCharacter, map_prod, map_zpow]
  apply Finset.prod_congr rfl
  intro i hi
  change (TorusCharacter.pullback
      (torusCharacterTupleMorphism T n (fun q => Additive.toMul (b q))))
        (dCoordinateCharacter n i) ^ z i =
    torusCharacterBasisMulEquiv T n b (dCoordinateCharacter n i) ^ z i
  rw [pullback_tuple_coordinate, basisMulEquiv_coordinate]

private noncomputable def torusCharacterBasisPolynomialFunctionAlgEquiv
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t)
    (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) :
    Variety.PolynomialFunction (dVariety k n) ≃ₐ[k]
      Variety.PolynomialFunction T :=
  (torusCharacterAlgebraEquiv (dVariety k n)
      (dVariety_isMulCommutative n) (dVariety_all_semisimple n)).symm |>.trans
    ((MonoidAlgebra.domCongr k k
      (torusCharacterBasisMulEquiv T n b)).trans
        (torusCharacterAlgebraEquiv T hcomm hsemi))

private lemma torusCharacterBasisTupleMorphism_pullbackAlgHom
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t)
    (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) :
    (torusCharacterBasisTupleMorphism T n b).toVariety.pullbackAlgHom =
      (torusCharacterBasisPolynomialFunctionAlgEquiv
        T hcomm hsemi n b).toAlgHom := by
  let f := torusCharacterBasisTupleMorphism T n b
  let ED := torusCharacterAlgebraEquiv (dVariety k n)
    (dVariety_isMulCommutative n) (dVariety_all_semisimple n)
  let ET := torusCharacterAlgebraEquiv T hcomm hsemi
  let eχ := torusCharacterBasisMulEquiv T n b
  have hnat := torusCharacterAlgebraEquiv_naturality
    hcomm hsemi (dVariety_isMulCommutative n)
      (dVariety_all_semisimple n) f
  apply AlgHom.ext
  intro q
  let a := ED.symm q
  have ha := DFunLike.congr_fun hnat a
  change f.toVariety.pullbackAlgHom (ED a) =
    ET ((MonoidAlgebra.mapDomainAlgHom k k
      (TorusCharacter.pullback f)) a) at ha
  rw [show ED a = q from ED.apply_symm_apply q] at ha
  change f.toVariety.pullbackAlgHom q =
    ET ((MonoidAlgebra.mapDomainAlgHom k k eχ) a)
  have hp := torusCharacterBasisTupleMorphism_pullback T n b
  change TorusCharacter.pullback f = eχ.toMonoidHom at hp
  rw [hp] at ha
  exact ha

/-- A torus of dimension `n` has a character-lattice basis indexed by
`Fin n`. -/
public theorem torus_character_basis
    {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) (n : ℕ) (hn : Variety.dimension T = n) :
    Nonempty (Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) := by
  obtain ⟨m, ⟨e⟩⟩ := hT
  have hm : m = n := by
    have hdim := algebraicGroupIso_dimension_eq e
    rw [dVariety_dimension_eq, hn] at hdim
    exact_mod_cast hdim
  subst n
  exact torus_character_basis_of_iso m e

/-- A connected commutative algebraic group whose points are all semisimple
is a torus. -/
public theorem isTorus_of_isConnected_isMulCommutative_all_semisimple
    {T : Variety k} [AlgebraicGroup T]
    (hconnected : Variety.IsConnected T)
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t) :
    IsTorus T := by
  obtain ⟨n, b⟩ := torusCharacterBasisData T hcomm hsemi hconnected
  let f := torusCharacterBasisTupleMorphism T n b
  let e := torusCharacterBasisPolynomialFunctionAlgEquiv T hcomm hsemi n b
  have hpull : f.toVariety.pullbackAlgHom = e.toAlgHom :=
    torusCharacterBasisTupleMorphism_pullbackAlgHom T hcomm hsemi n b
  let isoTD : AlgebraicGroup.Iso T (dVariety k n) :=
    AlgebraicGroup.Iso.ofPullbackAlgEquiv f e hpull
  exact ⟨n, ⟨isoTD.symm⟩⟩

end Theory.AlgebraicGroup
