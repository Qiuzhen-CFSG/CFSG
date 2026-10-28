module

public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.CoordinateRing.FiniteTranslate
public import Theory.AlgebraicGroup.Tori.Character.Algebra

universe u

/-! Finite generation and connectedness properties of character groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private lemma conjugationPullbacks_mem_finiteSubmodule
    (G : Variety k) [AlgebraicGroup G]
    (q : Variety.PolynomialFunction G) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      ∀ g : Variety.Point G,
        (AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom q ∈ W := by
  obtain ⟨W, hWfg, hW⟩ :=
    AlgebraicGroup.exists_finite_twoSidedTranslate_submodule G q
  refine ⟨W, hWfg, ?_⟩
  intro g
  convert hW g g⁻¹ using 1
  apply Variety.PolynomialFunction.ext
  intro x
  rfl

/-- The algebraic-character group of a commutative algebraic group whose
points are all semisimple is finitely generated. -/
public theorem torusCharacter_finitelyGenerated
    [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t) :
    Group.FG (TorusCharacter T) := by
  let : Semiring k :=
    (inferInstance : CommRing k).toCommSemiring.toSemiring
  let equiv := torusCharacterAlgebraEquiv T hcomm hsemi
  let : Algebra.FiniteType k (MonoidAlgebra k (TorusCharacter T)) :=
    (polynomialFunction_finiteType T).equiv equiv.symm
  exact (MonoidAlgebra.finiteType_iff_group_fg
    (R := k) (G := TorusCharacter T)).mp inferInstance

private lemma torusCharacter_conjugationOrbit_finite
    {G : Variety k} [AlgebraicGroup G]
    (N : ClosedSubgroup G) (hNnormal : N.toSubgroup.Normal)
    (χ : TorusCharacter N.carrierVariety) :
    (Set.range fun g : Variety.Point G =>
      χ.comp (N.conjugationRestriction hNnormal g)).Finite := by
  let orbitCharacter (g : Variety.Point G) :
      TorusCharacter N.carrierVariety :=
    χ.comp (N.conjugationRestriction hNnormal g)
  obtain ⟨q, hq⟩ :=
    N.exists_polynomialFunction_extension χ.scalarPolynomialFunction
  obtain ⟨W, hWfg, hW⟩ :=
    conjugationPullbacks_mem_finiteSubmodule G q
  let res : Variety.PolynomialFunction G →ₗ[k]
      Variety.PolynomialFunction N.carrierVariety :=
    N.inclusion.toVariety.pullbackAlgHom.toLinearMap
  let WN : Submodule k (Variety.PolynomialFunction N.carrierVariety) :=
    W.map res
  have hWNfg : WN.FG := hWfg.map res
  have horbitMem (g : Variety.Point G) :
      (orbitCharacter g).scalarPolynomialFunction ∈ WN := by
    refine ⟨(AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom q,
      hW g, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    change q ((AlgebraicGroup.conjugationByMorphism G g).toFun
      (N.inclusion.onPoints x)) =
      χ.scalarPolynomialFunction
        ((N.conjugationRestriction hNnormal g).onPoints x)
    rw [AlgebraicGroup.conjugationByMorphism_apply]
    rw [← N.conjugationRestriction_inclusion_apply hNnormal]
    exact hq _
  let C : Set (TorusCharacter N.carrierVariety) := Set.range orbitCharacter
  let v : C → WN := fun c =>
    ⟨c.1.scalarPolynomialFunction, by
      rcases c.2 with ⟨g, hg⟩
      rw [← hg]
      exact horbitMem g⟩
  have hvAmbient : LinearIndependent k
      (fun c : C => c.1.scalarPolynomialFunction) :=
    (torusCharacter_scalarPolynomialFunction_linearIndependent
      N.carrierVariety).comp (fun c : C => c.1) Subtype.val_injective
  have hv : LinearIndependent k v := by
    apply LinearIndependent.of_comp WN.subtype
    exact hvAmbient
  let : Module.Finite k WN :=
    Module.Finite.of_fg_top ((Submodule.fg_top WN).mpr hWNfg)
  let : IsNoetherian k WN :=
    isNoetherian_of_isNoetherianRing_of_finite k WN
  let : Finite C := hv.finite_of_isNoetherian
  change C.Finite
  exact Set.finite_coe_iff.mp inferInstance

/-- Conjugation by a point of a connected algebraic group fixes every
character of a normal closed subgroup. -/
public theorem torusCharacter_comp_conjugationRestriction_eq_self_of_connected
    {G : Variety k} [AlgebraicGroup G]
    (hG : Variety.IsConnected G)
    (N : ClosedSubgroup G) (hNnormal : N.toSubgroup.Normal)
    (χ : TorusCharacter N.carrierVariety)
    (g : Variety.Point G) :
    χ.comp (N.conjugationRestriction hNnormal g) = χ := by
  let orbitCharacter (z : Variety.Point G) :
      TorusCharacter N.carrierVariety :=
    χ.comp (N.conjugationRestriction hNnormal z)
  have horbitFinite : (Set.range orbitCharacter).Finite :=
    torusCharacter_conjugationOrbit_finite N hNnormal χ
  apply AlgebraicGroup.Morphism.ext
  funext x
  have hmap (z : Variety.Point G) :
      (AlgebraicGroup.conjugateMorphism G (N.inclusion.onPoints x)).toFun z ∈
        N.toSubgroup := by
    rw [AlgebraicGroup.conjugateMorphism_apply]
    have hx : N.inclusion.onPoints x ∈ N.toSubgroup :=
      (N.pointEquiv x).property
    simpa using hNnormal.conj_mem' (N.inclusion.onPoints x) hx z⁻¹
  let ambientOrbit := AlgebraicGroup.conjugateMorphism G
    (N.inclusion.onPoints x)
  let orbitPoint : Variety.Morphism G N.carrierVariety :=
    { toFun := fun z => N.pointEquiv.symm ⟨ambientOrbit.toFun z, hmap z⟩
      regular := by
        intro i
        obtain ⟨p, hp⟩ := ambientOrbit.regular i
        refine ⟨p, ?_⟩
        intro z
        change (N.pointEquiv
          (N.pointEquiv.symm ⟨ambientOrbit.toFun z, hmap z⟩)).val.val i =
          evalPolynomial z.val p
        rw [N.pointEquiv.apply_symm_apply]
        exact hp z }
  let valueMorphism : Variety.Morphism G (KMult k) :=
    χ.toVariety.comp orbitPoint
  have hvalue (z : Variety.Point G) :
      valueMorphism.toFun z = (orbitCharacter z).onPoints x := by
    change χ.toVariety.toFun (orbitPoint.toFun z) =
      χ.toVariety.toFun ((N.conjugationRestriction hNnormal z).onPoints x)
    congr 1
  have hvalueFinite : (Set.range valueMorphism.toFun).Finite := by
    apply (horbitFinite.image fun ψ : TorusCharacter N.carrierVariety =>
      ψ.onPoints x).subset
    rintro y ⟨z, rfl⟩
    exact ⟨orbitCharacter z, ⟨z, rfl⟩, (hvalue z).symm⟩
  have hsub := connected_finite_morphism_range_subsingleton
    valueMorphism hG hvalueFinite
  have heq := hsub ⟨g, rfl⟩ ⟨1, rfl⟩
  rw [hvalue g, hvalue 1] at heq
  have hone : (orbitCharacter 1).onPoints x = χ.onPoints x := by
    change χ.onPoints ((N.conjugationRestriction hNnormal 1).onPoints x) =
      χ.onPoints x
    congr 1
    apply N.inclusion_injective
    rw [N.conjugationRestriction_inclusion_apply]
    simp
  exact heq.trans hone

/-- The character group of a connected algebraic group is torsion-free. -/
public theorem torusCharacter_isTorsionFree_of_isConnected
    (T : Variety k) [AlgebraicGroup T]
    (hconnected : Variety.IsConnected T) :
    IsMulTorsionFree (TorusCharacter T) := by
  have hchar_one (χ : TorusCharacter T) (n : ℕ) (hn : n ≠ 0)
      (hχ : χ ^ n = 1) : χ = 1 := by
    let q : Variety.Point (KMult k) → k := fun y =>
      (dPointEquiv 1 y 0 : k)
    have qinj : Function.Injective q := by
      intro y z hyz
      apply (dPointEquiv 1).injective
      funext i
      fin_cases i
      apply Units.ext
      exact hyz
    have hroot (x : Variety.Point T) :
        (q (χ.toVariety.toFun x)) ^ n = 1 := by
      have hfun := congrArg
        (TorusCharacter.scalarPolynomialFunctionMonoidHom T) hχ
      rw [map_pow, map_one] at hfun
      have hx := congrArg (polynomialFunctionPointAlgHom T x) hfun
      change (χ.scalarPolynomialFunction x) ^ n = 1 at hx
      rw [TorusCharacter.scalarPolynomialFunction_apply] at hx
      exact hx
    have himagefinite : (Set.range χ.toVariety.toFun).Finite := by
      apply Set.Finite.of_finite_image
        (f := q) (s := Set.range χ.toVariety.toFun)
      · apply (Finset.finite_toSet
          (Polynomial.nthRootsFinset n (1 : k))).subset
        rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
        exact (Polynomial.mem_nthRootsFinset
          (Nat.pos_of_ne_zero hn) (1 : k)).mpr (hroot x)
      · exact qinj.injOn
    have himagesub : (Set.range χ.toVariety.toFun).Subsingleton :=
      connected_finite_morphism_range_subsingleton
        χ.toVariety hconnected himagefinite
    apply AlgebraicGroup.Morphism.ext
    funext x
    have hx := himagesub (Set.mem_range_self x)
      (Set.mem_range_self (1 : Variety.Point T))
    change χ.toVariety.toFun x = χ.toVariety.toFun 1 at hx
    rw [χ.map_one] at hx
    exact hx
  refine ⟨?_⟩
  intro n hn χ ψ hpow
  change χ ^ n = ψ ^ n at hpow
  rw [← div_eq_one]
  apply hchar_one (χ / ψ) n hn
  rw [div_pow, hpow, div_self']

end Theory.AlgebraicGroup
