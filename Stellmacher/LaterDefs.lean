module

public import Stellmacher.SectionFiveToSeven
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
open Theory.ElementaryAbelian


open scoped BigOperators Pointwise

universe u v

namespace Stellmacher
namespace Later

/-!  Concrete models used by the paper's local structure statements.  The
notation is kept in one interface file so that the numbered statements do
not depend on ad-hoc model choices. -/

public abbrev SL2Two := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
public abbrev L3Two := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
public abbrev S4 := Equiv.Perm (Fin 4)
public abbrev C2 := Multiplicative (ZMod 2)
public abbrev C3 := Multiplicative (ZMod 3)
public abbrev C4 := Multiplicative (ZMod 4)
public abbrev C5 := Multiplicative (ZMod 5)
public abbrev Q8 := QuaternionGroup 2

@[expose] public def IsModel
    {G : Type u} [Group G] (A : Subgroup G) (X : Type v) [Group X] : Prop :=
  Nonempty ((A : Type u) ≃* X)

@[expose] public def QuotientCardEq
    {G : Type u} [Group G] (A B : Subgroup G) (n : ℕ) : Prop :=
  Nat.card A = n * Nat.card B

@[expose] public def QuotientCardEqual
    {G : Type u} [Group G] (A B C D : Subgroup G) : Prop :=
  Nat.card A * Nat.card D = Nat.card C * Nat.card B

/- A surjective homomorphism with the indicated kernel is the invariant
   content of the notation `A/B ≅ X`; it avoids forcing a normality instance
   for every subgroup expression occurring in the scan. -/
@[expose] public def QuotientIsModel
    {G : Type u} [Group G] (A B : Subgroup G) (X : Type v) [Group X] : Prop :=
  ∃ f : A →* X, Function.Surjective f ∧ f.ker = B.subgroupOf A

public structure QuotientWitness
    {G : Type u} [Group G] (A B : Subgroup G) where
  X : Type u
  [groupX : Group X]
  [finiteX : Finite X]
  projection : A →* X
  surjective : Function.Surjective projection
  kernel_eq : projection.ker = B.subgroupOf A

/- A quotient witness together with the conjugation action on an ambient
module.  This is used when the source writes a barred local group acting on
an unbarred subgroup (as in (8.1)); mapping the module itself through the
quotient would incorrectly collapse it into the kernel. -/
public structure QuotientModuleWitness
    {G : Type u} [Group G] (A B V : Subgroup G) where
  X : Type u
  [groupX : Group X]
  [finiteX : Finite X]
  projection : A →* X
  surjective : Function.Surjective projection
  kernel_eq : projection.ker = B.subgroupOf A
  module_le : V ≤ A
  action : X →* MulAut (↥V)
  action_compatible :
    ∀ a : A, ∀ v : V,
      ((action (projection a)) v : G) =
        (a : G) * (v : G) * (a : G)⁻¹

@[expose] public def QuotientElementaryAbelian
    {G : Type u} [Group G] (A B : Subgroup G) (p n : ℕ) : Prop :=
  ∃ w : QuotientWitness A B,
    (let _ := w.groupX
     let _ := w.finiteX
     IsElementaryAbelian p w.X ∧ Nat.card w.X = p ^ n)

@[expose] public def QuotientIsElementaryAbelian
    {G : Type u} [Group G] (A B : Subgroup G) (p : ℕ) : Prop :=
  ∃ w : QuotientWitness A B,
    (let _ := w.groupX
     let _ := w.finiteX
     IsElementaryAbelian p w.X)

@[expose] public def QuotientExtraspecial
    {G : Type u} [Group G] (A B : Subgroup G) (p n : ℕ) : Prop :=
  ∃ w : QuotientWitness A B,
    (let _ := w.groupX
     let _ := w.finiteX
     IsExtraspecial p w.X ∧ Nat.card w.X = p ^ n)

@[expose] public def IsSpecialTwo
    {G : Type u} [Group G] (A : Subgroup G) : Prop :=
  Subgroup.center (↥A) = commutator (↥A) ∧
    commutator (↥A) = frattini (↥A)

@[expose] public def IsSemidirectModel
    {G : Type u} [Group G] (A : Subgroup G)
    (N K : Type v) [Group N] [Group K] : Prop :=
  ∃ φ : K →* MulAut N, Nonempty ((A : Type u) ≃* SemidirectProduct N K φ)

@[expose] public def QuotientIsSemidirectModel
    {G : Type u} [Group G] (A B : Subgroup G)
    (N K : Type v) [Group N] [Group K] : Prop :=
  ∃ φ : K →* MulAut N,
    QuotientIsModel A B (SemidirectProduct N K φ)

@[expose] public def IsFrobenius20
    {G : Type u} [Group G] (A : Subgroup G) : Prop :=
  ∃ φ : C4 →* MulAut C5,
    Function.Injective φ ∧ Nonempty ((A : Type u) ≃* SemidirectProduct C5 C4 φ)

@[expose] public def QuotientIsFrobenius20
    {G : Type u} [Group G] (A B : Subgroup G) : Prop :=
  ∃ φ : C4 →* MulAut C5,
    Function.Injective φ ∧
      QuotientIsModel A B (SemidirectProduct C5 C4 φ)

@[expose] public def IsCentralProductQ8Q8
    {G : Type u} [Group G] (A : Subgroup G) : Prop :=
  ∃ B C : Subgroup G,
    IsModel B Q8 ∧ IsModel C Q8 ∧
    A = B ⊔ C ∧
    Nat.card (B ⊓ C : Subgroup G) = 2 ∧
    (∀ b : G, b ∈ B → ∀ c : G, c ∈ C → b * c = c * b) ∧
    (B ⊓ C : Subgroup G) ≤ (Subgroup.center (↥A)).map A.subtype

@[expose] public def IsCentralProductModel
    {G : Type u} [Group G] (A : Subgroup G)
    (N K : Type v) [Group N] [Group K] : Prop :=
  ∃ B C : Subgroup G,
    IsModel B N ∧ IsModel C K ∧ A = B ⊔ C ∧
    Nat.card (B ⊓ C : Subgroup G) = 2 ∧
    (∀ b : G, b ∈ B → ∀ c : G, c ∈ C → b * c = c * b) ∧
    (B ⊓ C : Subgroup G) ≤ (Subgroup.center (↥A)).map A.subtype

@[expose] public def IsSylowIn
    {G : Type u} [Group G] (p : ℕ) (T A : Subgroup G) : Prop :=
  ∃ P : Sylow p A, (P : Subgroup A).map A.subtype = T

@[expose] public def FrattiniAmbient
    {G : Type u} [Group G] (A : Subgroup G) : Subgroup G :=
  (frattini (↥A)).map A.subtype

@[expose] public def DerivedAmbient
    {G : Type u} [Group G] (A : Subgroup G) : Subgroup G :=
  (derivedSubgroup (↥A)).map A.subtype

@[expose] public def CenterAmbient
    {G : Type u} [Group G] (A : Subgroup G) : Subgroup G :=
  (Subgroup.center (↥A)).map A.subtype

@[expose] public def GeneratedWith
    {G : Type u} [Group G] (A : Subgroup G) (x : G) : Subgroup G :=
  A ⊔ Subgroup.zpowers x

@[expose] public def IsInvertingOn
    {G : Type u} [Group G] (t : G) (A : Subgroup G) : Prop :=
  ∀ x : G, x ∈ A → t * x * t⁻¹ = x⁻¹

@[expose] public def IsInternalDirectProductTwo
    {G : Type u} [Group G] (D A B : Subgroup G) : Prop :=
  D = A ⊔ B ∧ Disjoint A B ∧
    ∀ a : G, a ∈ A → ∀ b : G, b ∈ B → a * b = b * a

@[expose] public def QuotientFixedPointFree
    {G : Type u} [Group G] (Q Z R : Subgroup G) : Prop :=
  Q ⊓ Subgroup.centralizer (R : Set G) ≤ Z

/-! Quotient-level action conditions used in the three-case alternative of
Section 8.  The paper quantifies subgroups in a quotient, while the local
interfaces in this development keep all concrete subgroups in the ambient
group.  The first predicate therefore uses the full preimage `R` of an
order-three subgroup and records its `Q`-invariance explicitly. -/

@[expose] public def QuotientQInvariantOrderThreeFixedPointFree
    {G : Type u} [Group G]
    (E O Q Z Qnext : Subgroup G) : Prop :=
  ∀ R : Subgroup G,
    R ≤ E → O ≤ R → QuotientCardEq R O 3 →
      (∀ q : Q, SectionsFiveToSeven.conjugateBy R (q : G) = R) →
      QuotientFixedPointFree Qnext Z R

/- The second predicate expresses an involution in the quotient
`Q Qnext / Qnext`: a representative is outside `Qnext` and has square in
`Qnext`. -/
@[expose] public def QuotientInvolutionCentralizes
    {G : Type u} [Group G]
    (Q Qnext : Subgroup G) : Prop :=
  ∀ x : G, x ∈ Q ⊔ Qnext → x ∉ Qnext → x ^ 2 ∈ Qnext →
    ∃ U : Subgroup G,
      U ≤ Qnext ∧ Nat.card U = 2 ^ 5 ∧
        U ≤ Subgroup.centralizer ({x} : Set G)

@[expose] public def IsInvolution
    {G : Type u} [Group G] (x : G) : Prop := x ≠ 1 ∧ x ^ 2 = 1

@[expose] public def IsConjugateVertex
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d e : Γ.Vertex) : Prop := ∃ g : G, Γ.act g d = e

@[expose] public def Neighborhood
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Set Γ.Vertex :=
  SectionsFiveToSeven.CosetGraphContext.neighborhood Γ d

@[expose] public noncomputable def NeighborhoodQIntersection
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (X : Set Γ.Vertex) : Subgroup G :=
  sInf {K : Subgroup G | ∃ d : Γ.Vertex, d ∈ X ∧ K = Γ.q d}

/- The source's `W_d` notation is the subgroup generated by the `V`-groups
at the relevant neighboring vertices.  At the statement level we use the
uniform neighborhood form; the specialized path cases in Sections 9--10
are then expressed by choosing the corresponding vertex. -/
@[expose] public noncomputable def GeneratedNeighborhoodV
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G :=
  sSup {K : Subgroup G | ∃ l : Γ.Vertex, l ∈ Γ.neighbors d ∧ K = Γ.vAt l}

/-! Local notation for the graph fields. -/

public abbrev GAt
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.stabilizer d

public abbrev QAt
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.q d

public abbrev EAt
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.e d

public abbrev ZAt
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.z d

public abbrev VAt
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Subgroup G := Γ.v d

public abbrev DAt
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : Set Γ.Vertex := Neighborhood Γ d

@[expose] public def IsNonsolvableNormalizer
    {G : Type u} [Group G] (W : Subgroup G) : Prop :=
  ¬ Group.IsSolvable (Subgroup.normalizer (W : Set G))

@[expose] public def IsElementaryAbelianSubgroup
    {G : Type u} [Group G] (p : ℕ) (A : Subgroup G) : Prop :=
  IsElementaryAbelian p (↥A)

/-! A quotient-free version of the Section 1 `m` and `J` notation.  It is
used when a quotient witness presents a barred local group as an ordinary
group. -/
@[expose] public noncomputable def LocalModuleMeasure
    {G : Type u} [Group G] [Finite G]
    (V A : Subgroup G) : ℚ :=
  (Nat.card V : ℚ) /
    ((Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : ℚ) *
      (Nat.card A : ℚ))

@[expose] public noncomputable def LocalJ
    {G : Type u} [Group G] [Finite G]
    (V S : Subgroup G) : Subgroup G :=
  sSup {A : Subgroup G |
    A ≤ S ∧ IsElementaryAbelian 2 (↥A) ∧ LocalModuleMeasure V A ≤ 1}

@[expose] public def QuotientOrderLe
    {G : Type u} [Group G] (A B : Subgroup G) (n : ℕ) : Prop :=
  Nat.card A ≤ n * Nat.card B

/-! The standing graph data used in Sections 8--10.  The fields are exactly
the global hypotheses and the critical pair/graph notation introduced before
the corresponding section; conclusions are deliberately not packaged here. -/

public structure SectionEightContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H) where
  hypothesisTwo : SectionsFiveToSeven.HypothesisTwo H S0 S P1 P2
  generated : P1 ⊔ P2 = ⊤
  Γ : SectionsFiveToSeven.CosetGraphContext H S P1 P2
  criticalPath : SectionsFiveToSeven.CriticalPath Γ
  commutator_ne : ⁅Γ.z criticalPath.a, Γ.z criticalPath.a'⁆ ≠ ⊥

public structure SectionNineContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H) where
  hypothesisTwo : SectionsFiveToSeven.HypothesisTwo H S0 S P1 P2
  generated : P1 ⊔ P2 = ⊤
  Γ : SectionsFiveToSeven.CosetGraphContext H S P1 P2
  criticalPath : SectionsFiveToSeven.CriticalPath Γ
  commutator_eq : ⁅Γ.z criticalPath.a, Γ.z criticalPath.a'⁆ = ⊥

public structure SectionTenContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H) where
  hypothesisTwo : SectionsFiveToSeven.HypothesisTwo H S0 S P1 P2
  generated : P1 ⊔ P2 = ⊤
  Γ : SectionsFiveToSeven.CosetGraphContext H S P1 P2
  criticalPath : SectionsFiveToSeven.CriticalPath Γ
  commutator_eq : ⁅Γ.z criticalPath.a, Γ.z criticalPath.a'⁆ = ⊥
  critical_length : criticalPath.length = 3

public abbrev StartVertex
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.a

public abbrev EndVertex
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.a'

public abbrev FirstStepVertex
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.firstStep

public abbrev StartVertexNine
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.a

public abbrev EndVertexNine
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.a'

public abbrev FirstStepVertexNine
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.firstStep

public abbrev StartVertexTen
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.a

public abbrev EndVertexTen
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.a'

public abbrev FirstStepVertexTen
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) : ctx.Γ.Vertex :=
  ctx.criticalPath.firstStep

/- A path-offset witness makes the paper's shorthand `a+k` (and
`a'-k`) explicit instead of allowing an unrelated graph vertex to be
substituted for the named path vertex. -/
@[expose] public def IsCriticalPathOffset
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : SectionsFiveToSeven.CosetGraphContext G S P1 P2)
    (cp : SectionsFiveToSeven.CriticalPath Γ)
    (k : ℕ) (d : Γ.Vertex) : Prop :=
  ∃ i : Fin (cp.length + 1), i.1 = k ∧ cp.path i = d

end Later
end Stellmacher
