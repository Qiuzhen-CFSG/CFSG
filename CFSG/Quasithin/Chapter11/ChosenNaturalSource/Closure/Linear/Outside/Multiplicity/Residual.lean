module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Residual.Complement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Residual.Image

/-!
# The odd residual complement in the original outside subgroup

B.6.8(2) supplies a prime core in H/O₂(H). A Sylow lift constructs an
actual nontrivial odd prime subgroup P of O²(H), complementary to its
two-core. The original quotient map transports the Frattini subgroup,
giving P∩M=Φ(P) and H=PT. Coprimality from Y kills the determinant of
the actual multiplicity image; its SL₂ embedding gives cyclicity and
order dividing q+1. Its centralization of X₁ uses the same original action.

This is the conditional residual step of Aschbacher--Smith 11.5.7,
printed p.782, using B.6.8(2), printed pp.113--114. Solvability of the
original H, residual containment in Y, the coprimality of Y, the compatible
multiplicity embedding and the odd abelian C-image remain inputs for the
parent source assembly. No alternative selected subgroup or field is used.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The complement and literal action-image clauses in the linear-three
branch of 11.5.7, under the independent multiplicity and source inputs. -/
theorem residual_structure (m : NaturalPair E)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (hs : Group.IsSolvable E.H) (hRY : outsideResidual E ≤ E.Y)
    (hY : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hemb : let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
      ∃ ι : ((C E) ⧸ actionCentralizer E (C E) hCG) →* GL (Fin 2) E.input.field.Carrier,
        Function.Injective ι ∧ ∀ (a : C E) (c v : Fin 2 → E.input.field.Carrier),
          m.action (C E) hCG a (fun i => c i • v) =
            fun i => Representation.generalLinearNatural 2
              (ι (QuotientGroup.mk' (actionCentralizer E (C E) hCG) a)) c i • v)
    (himage : let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
      Odd (Nat.card ((C E) ⧸ actionCentralizer E (C E) hCG)) ∧
        IsMulCommutative (quotientAction E (C E) hCG).range) :
    let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
    ∃ (p : ℕ) (P : Subgroup G), p.Prime ∧ Odd p ∧ IsPGroup p P ∧
      P ≤ outsideResidual E ∧ P ≠ ⊥ ∧
      outsideResidual E = (outsideResidual E).pCoreIn 2 ⊔ P ∧
      Disjoint ((outsideResidual E).pCoreIn 2) P ∧
      P ⊔ (T : Subgroup G) = E.H ∧
      P ⊓ E.M = (frattini P).map P.subtype ∧
      Nat.Coprime p (2 ^ E.input.field.degree - 1) ∧
      IsCyclic ((P.subgroupOf (C E)).map (quotientAction E (C E) hCG)) ∧
      Nat.card ((P.subgroupOf (C E)).map (quotientAction E (C E) hCG)) ∣
        2 ^ E.input.field.degree + 1 ∧
      (P.subgroupOf (C E)).map (quotientAction E (C E) hCG) ≤
        centralizer (((X₁ E).subgroupOf (C E)).map (quotientAction E (C E) hCG) :
          Set (MulAut (E.W ⧸ E.V₁.subgroupOf E.W))) := by
  dsimp only at hemb himage ⊢
  let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
  obtain ⟨ι,hι,_⟩ := hemb
  obtain ⟨p,P,hp,ho,hP,hPR,hne,hcover,hdis,hgen,hPhi⟩ :=
    exists_residual_complement E hH hNT hs
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpn,hcyc,hdiv⟩ :=
    residual_subgroup_image_cyclic E hCG ι hι hY ho P hP hPR hRY hne
  exact ⟨p,P,hp,ho,hP,hPR,hne,hcover,hdis,hgen,hPhi,hpn,hcyc,hdiv,
    residual_subgroup_image_centralizes_X₁ E hCG himage.2 P hPR⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
