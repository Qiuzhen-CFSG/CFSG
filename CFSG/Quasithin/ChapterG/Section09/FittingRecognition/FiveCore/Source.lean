module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.NilpotentSource
public import Theory.Representation.SmallBinaryPrimeNormalizer.NormalClosure

/-!
# The actual four-dimensional five-normalizer in G.9.4

The given linear subgroup acts faithfully on the additive group of its
binary four-space. The normal-closure theorem for this action supplies the
precise five-normalizer contract, and transport through the original faithful
representation identifies the normal closure of its elementary actor.

The final consumer supplies the completed G.9.2 theorem internally. It retains
only the independent assertion that the five-core fixes the ordinary factor
spaces; no linear-normalizer or nilpotent-rigidity callback remains.
Source: Aschbacher--Smith G.9.4(2), printed pp.354--355.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
open Subgroup NilpotentRigidity
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The five-normalizer contract follows from the literal binary action in
four dimensions, without choosing coordinates or classifying linear subgroups. -/
theorem FiveCore.linearNormalizerRecognition (hd : Module.finrank (ZMod 2) V = 4) :
    FiveCore.LinearNormalizerRecognition V := by
  intro L X E hXn hX hE hEne
  let _ := hXn
  let _ := hE
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let ρ : Representation (ZMod 2) L V := (Units.coeHom _).comp L.subtype
  have hf : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact hab
  let : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : Finite L := Finite.of_injective ρ hf
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ hf
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  exact SmallBinaryPrimeNormalizer.normalClosure_dihedral hV X E hX hEne

/-- The actual faithful representation's five-core now supplies the dihedral
normal closure in G.9.4(2). -/
theorem FiveCore.normalClosure_dihedral_from_source
    {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}
    (h : Setup ρ A m) (hm : 0 < m) (hd : Module.finrank (ZMod 2) V = 4)
    (hcard : Nat.card (pCore 5 G) = 5) :
    Nonempty (normalClosure (A : Set G) ≃* DihedralGroup 5) :=
  FiveCore.normalClosure_dihedral_of_linearNormalizer h hm hcard
    (FiveCore.linearNormalizerRecognition hd)

/-- G.9.4(2) with its linear normalizer premise discharged. The independent
ordinary-factor fixed-space assertion is retained for its source producer. -/
theorem caseTwo_of_ordinaryFactorsFixed
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (ordinary : FiveCore.OrdinaryFactorsFixed ρ A) : CaseTwo ρ A m :=
  caseTwo_of_fiveCore_inputs h hm (nilpotentRigidityInput ρ) hn ordinary FiveCore.linearNormalizerRecognition

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
