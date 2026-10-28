module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerMS
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex

/-!
# The literal initial Sp₄(4) cover

The initial MS natural recognition gives an action equivalence for the moved
section modulo its fixed central layer. Over a field of order four the full
symplectic group is perfect, so the equivalence is transported to its literal
derived actor. The original projection from the moved section to the fixed
quotient is then an `IsCover`, with no split extension or new quotient action.

Source: MS93 (3.2)(vi), (1.5)(ii), and Aschbacher--Smith I.1.5.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover

variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Transport a full symplectic natural action to the literal derived actor.
The underlying binary action is definitionally the same restricted-scalar
representation as `binaryNatural`. -/
noncomputable def derivedNaturalActionEquiv
    {F : BinaryField} (hF : 2 < Nat.card F.Carrier)
    {D : Type*} [Group D]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (e : ActionEquiv ρ (binarySymplectic F)) :
    ActionEquiv ρ (binaryNatural (K := F.Carrier)) := by
  let d : commutator (Matrix.symplecticGroup (Fin 2) F.Carrier) ≃*
      Matrix.symplecticGroup (Fin 2) F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans
      Subgroup.topEquiv
  refine ⟨e.groupEquiv.trans d.symm, e.linearEquiv, ?_⟩
  intro g v
  have he := e.intertwines g v
  change e.linearEquiv (ρ g v) =
    (binarySymplectic F) (e.groupEquiv g) (e.linearEquiv v) at he
  change e.linearEquiv (ρ g v) =
    (binaryNatural (K := F.Carrier)) (d.symm (e.groupEquiv g))
      (e.linearEquiv v)
  have hd := d.apply_symm_apply (e.groupEquiv g)
  change e.linearEquiv (ρ g v) =
    Matrix.mulVec (d.symm (e.groupEquiv g)).val.val (e.linearEquiv v)
  rw [show (d.symm (e.groupEquiv g)).val = e.groupEquiv g by exact hd]
  exact he

/-- The actual moved projection is a cover for the derived Sp₄(4) action. -/
theorem centralOmega_initial_cover
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    (C : Subgroup J) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hc : Nat.card C = 979200) (hC : centralizer (C : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C) :
    letI : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) :=
      omegaCenterIn_elementary _
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) q hq
      (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)
    let s := MovedSection.ofNormal ρ C
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype)
          (binaryNatural (K := F.Carrier)),
        IsCover (MovedSection.coverProjection s e) := by
  dsimp only
  obtain ⟨hi,F,hF,⟨e⟩⟩ := centralOmega_moved_natural R hms hp hne hQR hself hfaith
    q hq hcore C hc hC hsq
  let s := MovedSection.ofNormal
    (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) q hq
      (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)) C
  let e' : ActionEquiv (s.action.comp C.subtype)
      (binaryNatural (K := F.Carrier)) :=
    derivedNaturalActionEquiv (F := F) (by
      rw [show Nat.card F.Carrier = 2 ^ F.degree from F.card_eq, hF]
      norm_num) (s.action.comp C.subtype) e
  exact ⟨F,hF, e', MovedSection.coverProjection_isCover s
      hi e'⟩

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
