module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage.InitialCover
public import Theory.Representation.CentralCoverCoordinates

/-!
# The initial natural cover on a literal amalgam subgroup

The central cover of the initial layer is transported onto the additive group
of the actual vertex subgroup `U R a`. The actor is the literal subgroup
`Ltilde R a`, and the mapped projection kernel is its centralizer in `U R a`.
This is the subgroup-coordinate form of the initial part of MS93 (3.2)(vi),
used by the later quadratic-cover and local-package arguments.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem initial_subgroup_cover_at_vertex
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {a : Vertex R} (ha : color R a = false) [IsElementaryAbelian 2 (U R a)] :
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ σ : Representation (ZMod 2)
          (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)) (Additive (U R a)),
      ∃ p : σ.IntertwiningMap (binaryNatural (K := F.Carrier)), IsCover p ∧
      ∃ f : Ltilde R a →* commutator (Matrix.symplecticGroup (Fin 2) F.Carrier),
        Function.Surjective f ∧
        (∀ (k : Ltilde R a) (u : U R a),
          ((σ (f k) (Additive.ofMul u)).toMul : FreeAmalgam R) =
            (k:FreeAmalgam R)*u*(k:FreeAmalgam R)⁻¹) ∧
        p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U R a).subtype =
          U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
  obtain ⟨F,hF,e,he,j,hj,hjU,f,hf,hact,hker⟩ := initial_cover_at_vertex R hms hp hne hQR
    hself hfaith q hq hcore hc hC hsq ha
  obtain ⟨σ,p,hp',hact',hker'⟩ := exists_subgroup_cover _ _ _ he
    (U R a) (Ltilde R a) j hj hjU f hact hker
  exact ⟨F,hF,σ,p,hp',f,hf,hact',hker'⟩
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
