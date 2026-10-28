module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
public import Mathlib.GroupTheory.Frattini

/-!
# The full linear-three alternatives of C.1.34

The module assertions below concern actual sections of Q=[O₂(KR),K]. They
identify these sections equivariantly, with one common identification of
K/O₂(K) with SL₃(F). Thus the duals and repeated summands in (3) and (4)
refer to the same natural module. The MS-pair hypotheses retain both
alternatives of (MS2), including its exceptional G₂ parabolic, and (MS3)
uses characteristic subgroups inside R and normality inside KR.

This is the SL₃ specialization of the definition of an MS-pair: the full
SL₃ core-quotient identification supplies the rank-two condition of (MS1).
No classification theorem is proved or assumed by these definitions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31 and
C.1.34, printed pp.135–137; C.2.7(3)(g), printed p.145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Subgroup Theory.GroupTheory ChapterC
universe u
variable {G : Type u} [Group G]

/-- A section D/E with its actual conjugation action, identified with a
specified linear representation. The normalizing conditions make the
intertwining equation an action on all of D/E. -/
def HasSectionModel {B V F : Type*} [Group B] [AddCommGroup V]
    [Field F] [Module F V] (L D E : Subgroup G)
    (actor : L →* B) (rho : Representation F B V) : Prop :=
  E ≤ D ∧ L ≤ normalizer D ∧ L ≤ normalizer E ∧
    ∃ hn : (E.subgroupOf D).Normal,
      letI := hn
      ∃ e : (D ⧸ E.subgroupOf D) ≃* Multiplicative V,
        ∀ (l : L) (d d' : D), (d' : G) = l * (d : G) * (l : G)⁻¹ →
          Multiplicative.toAdd (e (QuotientGroup.mk' _ d')) =
            rho (actor l) (Multiplicative.toAdd (e (QuotientGroup.mk' _ d)))

/-- The actual commutator subgroup in C.1.34, embedded in the ambient group. -/
def msQ (K R : Subgroup G) : Subgroup G := ⁅(K ⊔ R).pCoreIn 2, K⁆

/-- Intrinsic centers and Frattini subgroups, mapped back to the ambient group. -/
def centerIn (D : Subgroup G) : Subgroup G := (center D).map D.subtype

def frattiniIn (D : Subgroup G) : Subgroup G := (frattini D).map D.subtype

def omegaCenterIn (D : Subgroup G) : Subgroup G :=
  ((omega₁ (center D) (p := 2)).map (center D).subtype).map D.subtype

/-- (MS2)(a), with index and two-core relative to KR. -/
def MSOddIndex (K R : Subgroup G) : Prop :=
  ∃ A : Subgroup G, A < K ⊔ R ∧ Odd (A.subgroupOf (K ⊔ R)).index ∧
    A.pCoreIn 2 = R

/-- (MS2)(b), retaining the actual exceptional quotient and a normal
E₈ in one of its maximal parabolics. -/
def MSExceptional (K R : Subgroup G) : Prop :=
  (K ⊔ R).pCoreIn 2 ≤ R ∧
    ∃ e : ((K ⊔ R : Subgroup G) ⧸ pCore 2 (K ⊔ R : Subgroup G)) ≃*
      Atlas.G2.Model (ZMod 2),
      let Rbar := ((R.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' _)).map e.toMonoidHom
      ∃ P : Subgroup (Atlas.G2.Model (ZMod 2)),
        IsG2MaximalParabolic P ∧ Rbar ≤ P ∧ (Rbar.subgroupOf P).Normal ∧
          IsElementaryAbelian 2 Rbar ∧ Nat.card Rbar = 8

/-- (MS3), with both relative subgroup conventions made explicit. -/
def MSNoCharacteristicNormal (K R : Subgroup G) : Prop :=
  ∀ C : Subgroup R, C.Characteristic →
    ((C.map R.subtype).subgroupOf (K ⊔ R)).Normal → C = ⊥

/-- C.1.31 specialized to a full SL₃ core quotient. The isomorphism and
field size are included, so the rank-two clause is genuine mathematics. -/
structure LinearThreeMSPair (κ : GroupClass.{u}) (K R : Subgroup G)
    (n : ℕ) (F : Type) [Field F] [Finite F] : Prop where
  positive : 1 ≤ n
  field_card : Nat.card F = 2 ^ n
  model : Nonempty (XiQuotient K ≃* Matrix.SpecialLinearGroup (Fin 3) F)
  sqtk : IsSQTK κ (K ⊔ R : Subgroup G)
  fitting : generalizedFitting (K ⊔ R : Subgroup G) = pCore 2 (K ⊔ R : Subgroup G)
  component : K ∈ cComponentsIn (K ⊔ R)
  radical : MSOddIndex K R ∨ MSExceptional K R
  characteristic : MSNoCharacteristicNormal K R

/-- The core-quotient action used in every module clause of C.1.34. -/
def linearThreeActor {K : Subgroup G} {F : Type*} [Field F]
    (e : XiQuotient K ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    K →* Matrix.SpecialLinearGroup (Fin 3) F :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

/-- The assertion R ≠ O₂(C_KR(Ω₁(Z(S)))) in C.1.34(2)–(4). -/
def MSNotCentralizerCore (K R S : Subgroup G) : Prop :=
  R ≠ ((K ⊔ R) ⊓ centralizer (omegaCenterIn S : Set G)).pCoreIn 2

/-- Case (5)'s specified index-seven point stabilizer, expressed through
conjugation on Q/C_Q(K); no arbitrary action on a seven-point set is used. -/
def MSPointStabilizer (K R S : Subgroup G) : Prop :=
  let Q := msQ K R
  let C := Q ⊓ centralizer (K : Set G)
  ∃ (G₁ : Subgroup G) (q : Q), (q : G) ∉ C ∧ G₁ ≤ K ⊔ R ∧
    S ≤ G₁ ∧ (G₁.subgroupOf (K ⊔ R)).index = 7 ∧ G₁.pCoreIn 2 = R ∧
    ∀ g ∈ K ⊔ R, g ∈ G₁ ↔ g * (q : G) * g⁻¹ * (q : G)⁻¹ ∈ C

/-- All five alternatives of C.1.34 for the chosen Sylow subgroup S.
The single parameter e fixes the natural module and its dual throughout. -/
def MSModuleAlternatives (K R S : Subgroup G) (n : ℕ) (F : Type)
    [Field F] (e : XiQuotient K ≃* Matrix.SpecialLinearGroup (Fin 3) F) : Prop :=
  let Q := msQ K R
  let Z := centerIn Q
  let C := Q ⊓ centralizer (K : Set G)
  let U := ⁅Z, K⁆
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let a := linearThreeActor e
  let v := Representation.specialLinearNatural (k := F) 3
  (IsBlock (K.subgroupOf (K ⊔ R)) ∧ IsSL3EvenBlock K n ∧
    HasSectionModel K Q ⊥ a v) ∨
  (HasSectionModel K Q ⊥ a (v.prod v) ∧ MSNotCentralizerCore K R S) ∨
  (HasSectionModel K Z ⊥ a v ∧ HasSectionModel K Q Z a (v.dual.prod v.dual) ∧
    MSNotCentralizerCore K R S) ∨
  (IsElementaryAbelian 2 C ∧ Nat.card C = 2 ^ (2 * n) ∧
    C ≤ centerIn (K ⊔ R) ∧ Z = C ⊔ U ∧ C ⊓ U = ⊥ ∧
    HasSectionModel K U ⊥ a v ∧ HasSectionModel K Phi Z a v.dual ∧
    HasSectionModel K D Phi a (v.dual.prod v.dual) ∧
    HasSectionModel K Q D a (v.prod v) ∧ MSNotCentralizerCore K R S) ∨
  (Nonempty (XiQuotient K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    Nonempty (C ≃* Multiplicative (ZMod 2)) ∧
    HasSectionModel K Q C a v ∧ omegaCenterIn S ≤ centerIn (K ⊔ R) ∧
    MSPointStabilizer K R S)

/-- The full MS-pair assertion and all the module alternatives referenced
by C.2.7(3)(g), for every choice of the Sylow overgroup in C.1.34. -/
def MSDescription (κ : GroupClass.{u}) (K R : Subgroup G) (n : ℕ)
    (F : Type) [Field F] [Finite F] : Prop :=
  LinearThreeMSPair κ K R n F ∧
    ∀ S : Subgroup G, IsSylowIn 2 S (K ⊔ R) → R ≤ S →
      ∃ e : XiQuotient K ≃* Matrix.SpecialLinearGroup (Fin 3) F,
        MSModuleAlternatives K R S n F e

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
