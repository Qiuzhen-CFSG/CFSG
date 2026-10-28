module

public import Theory.AlgebraicGroup.Tori.TriangularCharacterSupport

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- If a morphism from a torus to an upper-triangular group is a closed
embedding at the level of coordinate rings, then its diagonal projection has
the same property. -/
public theorem triangularMorphism_diagonal_pullbackRingHom_surjective
    {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) (n : ℕ)
    (f : AlgebraicGroup.Morphism T (tVariety k n))
    (hf : Function.Surjective f.toVariety.pullbackRingHom) :
    Function.Surjective
      (((tDiagonalMorphism n).comp f).toVariety.pullbackRingHom) := by
  classical
  let hD := dVariety_isTorus (k := k) n
  let eT := torusCharacterAlgebraEquiv T
    hT.isMulCommutative (IsTorus.all_semisimple hT)
  let eD := torusCharacterAlgebraEquiv (dVariety k n)
    hD.isMulCommutative (IsTorus.all_semisimple hD)
  let delta := (tDiagonalMorphism n).comp f
  let mapCharacters := MonoidAlgebra.mapDomainAlgHom k k
    (TorusCharacter.pullback delta)
  have hmatrix (r s : Fin n) :
      ∃ qD : Variety.PolynomialFunction (dVariety k n),
        delta.toVariety.pullbackRingHom qD =
          f.toVariety.pullbackRingHom
            (triangularMatrixCoordinate (k := k) n r s) := by
    let c := f.toVariety.pullbackRingHom
      (triangularMatrixCoordinate (k := k) n r s)
    let b : MonoidAlgebra k (TorusCharacter T) := eT.symm c
    have hsupport : (b.coeff.support : Set (TorusCharacter T)) ⊆
        Set.range (TorusCharacter.pullback delta) := by
      simpa only [b, c, eT, delta] using
        (triangularMorphism_characterSupport_subset_diagonalPullback
          hT n f r s)
    let liftCharacter (eta : TorusCharacter T) :
        TorusCharacter (dVariety k n) :=
      if h : eta ∈ b.coeff.support then
        Classical.choose (hsupport h)
      else 1
    have hlift (eta : TorusCharacter T) (heta : eta ∈ b.coeff.support) :
        TorusCharacter.pullback delta (liftCharacter eta) = eta := by
      simp only [liftCharacter, heta, ↓reduceDIte]
      exact Classical.choose_spec (hsupport heta)
    let aD : MonoidAlgebra k (TorusCharacter (dVariety k n)) :=
      b.coeff.sum fun eta coeff =>
        MonoidAlgebra.single (liftCharacter eta) coeff
    have hmap : mapCharacters aD = b := by
      dsimp only [aD]
      rw [map_finsuppSum]
      calc
        b.coeff.sum (fun eta coeff =>
            mapCharacters
              (MonoidAlgebra.single (liftCharacter eta) coeff)) =
            b.coeff.sum (fun eta coeff =>
              MonoidAlgebra.single eta coeff) := by
          apply Finsupp.sum_congr
          intro eta heta
          change MonoidAlgebra.mapDomain (TorusCharacter.pullback delta)
              (MonoidAlgebra.single (liftCharacter eta) (b.coeff eta)) =
            MonoidAlgebra.single eta (b.coeff eta)
          rw [MonoidAlgebra.mapDomain_single, hlift eta heta]
        _ = b := MonoidAlgebra.sum_coeff_single b
    refine ⟨eD aD, ?_⟩
    have hnatural := congrArg (fun F => F aD)
      (torusCharacterAlgebraEquiv_naturality
        hT.isMulCommutative (IsTorus.all_semisimple hT)
        hD.isMulCommutative (IsTorus.all_semisimple hD) delta)
    change delta.toVariety.pullbackAlgHom (eD aD) = c
    calc
      delta.toVariety.pullbackAlgHom (eD aD) =
          eT (mapCharacters aD) := hnatural
      _ = eT b := by rw [hmap]
      _ = c := eT.apply_symm_apply c
  have hinverse (r : Fin n) :
      delta.toVariety.pullbackRingHom
          (Variety.PolynomialFunction.ofPolynomial (dVariety k n)
            (MvPolynomial.X (Sum.inr (ULift.up r)))) =
        f.toVariety.pullbackRingHom
          (Variety.PolynomialFunction.ofPolynomial (tVariety k n)
            (MvPolynomial.X (Sum.inr (ULift.up r)))) := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial
        ((tDiagonalMorphism n).onPoints (f.onPoints x)).val
          (MvPolynomial.X (Sum.inr (ULift.up r))) =
      evalPolynomial (f.onPoints x).val
        (MvPolynomial.X (Sum.inr (ULift.up r)))
    rw [evalPolynomial_X, evalPolynomial_X]
    change (tDiagonalHom n (tPointEquiv k n (f.onPoints x)) r).inv =
      tPointD n (f.onPoints x) r
    exact tDiagonalHom_inv n (f.onPoints x) r
  have hcoordinate (q : (tVariety k n).Coordinates) :
      ∃ qD : Variety.PolynomialFunction (dVariety k n),
        delta.toVariety.pullbackRingHom qD =
          f.toVariety.pullbackRingHom
            (Variety.PolynomialFunction.ofPolynomial (tVariety k n)
              (MvPolynomial.X q)) := by
    cases q with
    | inl q =>
        rcases q with ⟨r, s⟩
        simpa only [triangularMatrixCoordinate] using hmatrix r s
    | inr q =>
        rcases q with ⟨r⟩
        exact ⟨Variety.PolynomialFunction.ofPolynomial (dVariety k n)
          (MvPolynomial.X (Sum.inr (ULift.up r))), hinverse r⟩
  have hof_add (p q : MvPolynomial (tVariety k n).Coordinates k) :
      Variety.PolynomialFunction.ofPolynomial (tVariety k n) (p + q) =
        Variety.PolynomialFunction.ofPolynomial (tVariety k n) p +
          Variety.PolynomialFunction.ofPolynomial (tVariety k n) q := by
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]
  have hof_mul_X (p : MvPolynomial (tVariety k n).Coordinates k)
      (q : (tVariety k n).Coordinates) :
      Variety.PolynomialFunction.ofPolynomial (tVariety k n)
          (p * MvPolynomial.X q) =
        Variety.PolynomialFunction.ofPolynomial (tVariety k n) p *
          Variety.PolynomialFunction.ofPolynomial (tVariety k n)
            (MvPolynomial.X q) := by
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial]
  have hpoly (p : MvPolynomial (tVariety k n).Coordinates k) :
      ∃ qD : Variety.PolynomialFunction (dVariety k n),
        delta.toVariety.pullbackRingHom qD =
          f.toVariety.pullbackRingHom
            (Variety.PolynomialFunction.ofPolynomial (tVariety k n) p) := by
    induction p using MvPolynomial.induction_on with
    | C a =>
        refine ⟨Variety.PolynomialFunction.ofPolynomial (dVariety k n)
          (MvPolynomial.C a), ?_⟩
        apply Variety.PolynomialFunction.ext
        intro x
        rw [Variety.Morphism.pullbackRingHom_apply,
          Variety.Morphism.pullbackRingHom_apply]
        simp [Variety.PolynomialFunction.pullback,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, evalPolynomial]
    | add p q hp hq =>
        obtain ⟨pD, hpD⟩ := hp
        obtain ⟨qD, hqD⟩ := hq
        refine ⟨pD + qD, ?_⟩
        calc
          delta.toVariety.pullbackRingHom (pD + qD) =
              delta.toVariety.pullbackRingHom pD +
                delta.toVariety.pullbackRingHom qD :=
            map_add delta.toVariety.pullbackRingHom pD qD
          _ = f.toVariety.pullbackRingHom
                (Variety.PolynomialFunction.ofPolynomial (tVariety k n) p) +
              f.toVariety.pullbackRingHom
                (Variety.PolynomialFunction.ofPolynomial (tVariety k n) q) := by
            rw [hpD, hqD]
          _ = f.toVariety.pullbackRingHom
              (Variety.PolynomialFunction.ofPolynomial (tVariety k n)
                (p + q)) := by rw [hof_add, map_add]
    | mul_X p q hp =>
        obtain ⟨pD, hpD⟩ := hp
        obtain ⟨qD, hqD⟩ := hcoordinate q
        refine ⟨pD * qD, ?_⟩
        calc
          delta.toVariety.pullbackRingHom (pD * qD) =
              delta.toVariety.pullbackRingHom pD *
                delta.toVariety.pullbackRingHom qD :=
            map_mul delta.toVariety.pullbackRingHom pD qD
          _ = f.toVariety.pullbackRingHom
                (Variety.PolynomialFunction.ofPolynomial (tVariety k n) p) *
              f.toVariety.pullbackRingHom
                (Variety.PolynomialFunction.ofPolynomial (tVariety k n)
                  (MvPolynomial.X q)) := by rw [hpD, hqD]
          _ = f.toVariety.pullbackRingHom
              (Variety.PolynomialFunction.ofPolynomial (tVariety k n)
                (p * MvPolynomial.X q)) := by rw [hof_mul_X, map_mul]
  intro qT
  obtain ⟨qTri, hqTri⟩ := hf qT
  obtain ⟨p, hp⟩ := qTri.representedBy
  have hrepresented : qTri =
      Variety.PolynomialFunction.ofPolynomial (tVariety k n) p := by
    apply Variety.PolynomialFunction.ext
    exact hp
  obtain ⟨qD, hqD⟩ := hpoly p
  refine ⟨qD, ?_⟩
  calc
    delta.toVariety.pullbackRingHom qD =
        f.toVariety.pullbackRingHom
          (Variety.PolynomialFunction.ofPolynomial (tVariety k n) p) := hqD
    _ = f.toVariety.pullbackRingHom qTri := by rw [hrepresented]
    _ = qT := hqTri

end Theory.AlgebraicGroup
