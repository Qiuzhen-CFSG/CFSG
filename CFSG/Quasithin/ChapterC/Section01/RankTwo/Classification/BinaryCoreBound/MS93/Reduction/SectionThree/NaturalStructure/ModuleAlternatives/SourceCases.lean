module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Quotients

/-!
# The four binary source alternatives

These predicates retain the actual fixed part C of X and U = [Z,Ltilde].
Natural maps intertwine ambient conjugation through the source projection.
The doubled case has one marking on both copies. The central extension has
kernel C ∩ U of order two, and the outer extension retains the index [X:Z].
These are output specifications, not a classification theorem.

Source: Meierfrankenfeld–Stellmacher (1993), (3.2)(i),(iii),(iv),(v),
printed p.863. The other printed families need exclusion for this quotient.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Actual isomorphic natural copies with one common quotient marking. -/
structure MovingCopies (source : LocalSource L R) (m : ℕ) where
  marking : SL ≃* SL
  equiv : U R (alpha R) ≃* Multiplicative (Fin m → Fin 3 → ZMod 2)
  action : ∀ (g : M) (u v : U R (alpha R)),
    (v : FreeAmalgam R) = embedM R g * (u : FreeAmalgam R) * (embedM R g)⁻¹ →
    ∀ i : Fin m, (equiv v).toAdd i =
      (marking (source.projection g)).val.mulVec ((equiv u).toAdd i)

/-- Printed case (i). -/
def SplitNatural (source : LocalSource L R) : Prop :=
  Nonempty (NaturalU R source.projection) ∧
    X R (alpha R) = fixedPart R ⊔ U R (alpha R) ∧
    Disjoint (fixedPart R) (U R (alpha R))

/-- Printed case (iii). -/
def SplitDouble (source : LocalSource L R) : Prop :=
  Nonempty (MovingCopies source 2) ∧
    X R (alpha R) = fixedPart R ⊔ U R (alpha R) ∧
    Disjoint (fixedPart R) (U R (alpha R))

/-- Printed case (iv); the natural quotient need not split over its kernel. -/
def CentralExtension (source : LocalSource L R) : Prop :=
  Nonempty (MovingQuotient source 1) ∧
    X R (alpha R) = fixedPart R ⊔ U R (alpha R) ∧
    Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) = 2

/-- Printed case (v); the natural direct sum is Z, and its index in X is two. -/
def OuterExtension (source : LocalSource L R) : Prop :=
  Nonempty (NaturalU R source.projection) ∧
    Z R (alpha R) = fixedPart R ⊔ U R (alpha R) ∧
    Disjoint (fixedPart R) (U R (alpha R)) ∧
    (Z R (alpha R)).relIndex (X R (alpha R)) = 2

/-- The three binary branches requiring the later source 3.8 exclusion. -/
def BadCase (source : LocalSource L R) : Prop :=
  SplitDouble source ∨ CentralExtension source ∨ OuterExtension source

/-- Exact binary specialization to be proved, rather than assumed by assembly. -/
def Alternatives (source : LocalSource L R) : Prop :=
  SplitNatural source ∨ BadCase source

/-- The actual edge kernel's image in the specified local quotient. -/
noncomputable def edgeActor (source : LocalSource L R) (t : Vertex R) : Subgroup SL :=
  ((Q R t).subgroupOf (stabilizer R (alpha R))).map (baseProjection source)

/-- The precise uniqueness and equality assertions used on printed p.877.
This is an output to be proved in the bad cases, not a source hypothesis. -/
def EdgeOffenderUniqueness [Finite M] (source : LocalSource L R) : Prop :=
  letI := X_elementary R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  ∀ t, Adjacent R (alpha R) t → ∃ A : Subgroup SL,
    A ≤ edgeActor source t ∧ Representation.BinaryOffender.IsOffender ρ A ∧
    (∀ B ≤ edgeActor source t, Representation.BinaryOffender.IsOffender ρ B → B = A) ∧
    Representation.BinaryOffender.fixedCodim ρ A = Representation.BinaryOffender.rank A ∧
    edgeActor source t ⊓ centralizer (A : Set SL) = A

/-- The binary bad-case output required by source 2.3(c,d).
The selected Z lies at the critical endpoint. Nonnormality is relative to
G_a; every auxiliary subgroup is already central in Q_a. -/
structure BadCaseEstimates (R : Subgroup M) (geometry : Geometry R) : Prop where
  commutator_bound : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ t, Adjacent R a' t →
    (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a' →
    ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Q R t →
    frattini (Y ⊔ X R a : Subgroup (FreeAmalgam R)) = ⊥ →
    ⁅Y, Z R a'⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅Y, X R a' ⊓ Q R a⁆
  auxiliary_normal : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ t, Adjacent R a t →
    (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' →
    ((⁅X R a, X R a'⁆).subgroupOf (Q R t)).Normal
  auxiliary_not_normal : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ¬ ((⁅X R a, X R a'⁆).subgroupOf (stabilizer R a)).Normal
  auxiliary_common : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ t, Adjacent R a t →
    (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' →
    ∀ c, CriticalPair R a c (geometry.exists_critical a ha) →
    (cosetGraph R).dist t c + 1 = (cosetGraph R).dist a c →
    ⁅X R a, X R a'⁆ ≤ ⁅X R a, X R c⁆

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
