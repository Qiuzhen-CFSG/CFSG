module
public import Stellmacher.SectionEight.GeneratedContext

/-!
# Source-(9) data on the actual local graph

Both records retain the selected four-group, generated terminal subgroup,
conjugators, adjacent vertex, and the same equivariant fixed-subgroup family.
Their fields are the exact source-(9) containments and alternatives used by
the later intersection and commutator arguments in (8.4).

The canonical record is retained verbatim and re-exported from its original
configuration module. The local record has the same fields on the actual
SectionEightLocalContext; field-preserving conversions are inverse and keep
all selected mathematical objects definitionally unchanged. Moving the
records below their producer permits the generated configuration proof to
share this data without changing canonical constructors or projections.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4)(9), printed
pp.39–40, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public structure EightFourSourceNineData
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H) where
  A : Subgroup H
  L0 : Subgroup H
  x : H
  d : ctx.Γ.Vertex
  y : H
  Ltilde : Subgroup H
  hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a
  hcard : Nat.card A = 4
  hAnot : ¬ A ≤ QAt ctx.Γ ctx.criticalPath.a'
  hAprev : A ≤ QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩)
  hcontrol : ∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
    ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ → ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a'
  hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a'
  hLgen : L0 = A ⊔ A.conjBy x
  hx : x ∈ L0
  hfirstfull : L0 ⊔ (GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩) ⊓
    GAt ctx.Γ ctx.criticalPath.a') = GAt ctx.Γ ctx.criticalPath.a'
  hd : d = ctx.Γ.act x⁻¹ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩)
  hy : y ∈ Ltilde
  hLtilde : Ltilde ≤ GAt ctx.Γ d
  hadj : ctx.Γ.adjacent d (ctx.Γ.act y⁻¹ ctx.criticalPath.a')
  hfull : Ltilde ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) = GAt ctx.Γ d
  hcase :
    ((Ltilde = (⨆k,F k ctx.criticalPath.firstStep) ⊔ QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) ∧
      Nat.card ↥(⨆k,F k ctx.criticalPath.firstStep) = 2 * Nat.card
        ↥((⨆k,F k ctx.criticalPath.firstStep) ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))) ∨
    ((Ltilde = twoCoreIn (twoResidualIn (L0 ⊔ QAt ctx.Γ ctx.criticalPath.a')) ⊔
      QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) ∧
      (⨆k,F k ctx.criticalPath.firstStep) ≤ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))
  source_seven : ∀ D : Subgroup H, D ≤ F (ctx.Γ.act y⁻¹ ctx.criticalPath.a') d →
    ⁅D,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a' → D ≤ ZAt ctx.Γ d
  forward : F (ctx.Γ.act y⁻¹ ctx.criticalPath.a') d ⊓ GAt ctx.Γ ctx.criticalPath.a ≤ ZAt ctx.Γ d

public structure EightFourSourceNineLocalData
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H) where
  A : Subgroup H
  L0 : Subgroup H
  x : H
  d : ctx.Γ.Vertex
  y : H
  Ltilde : Subgroup H
  hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a
  hcard : Nat.card A = 4
  hAnot : ¬ A ≤ QAt ctx.Γ ctx.criticalPath.a'
  hAprev : A ≤ QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩)
  hcontrol : ∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
    ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ → ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a'
  hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a'
  hLgen : L0 = A ⊔ A.conjBy x
  hx : x ∈ L0
  hfirstfull : L0 ⊔ (GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩) ⊓
    GAt ctx.Γ ctx.criticalPath.a') = GAt ctx.Γ ctx.criticalPath.a'
  hd : d = ctx.Γ.act x⁻¹ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩)
  hy : y ∈ Ltilde
  hLtilde : Ltilde ≤ GAt ctx.Γ d
  hadj : ctx.Γ.adjacent d (ctx.Γ.act y⁻¹ ctx.criticalPath.a')
  hfull : Ltilde ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) = GAt ctx.Γ d
  hcase :
    ((Ltilde = (⨆k,F k ctx.criticalPath.firstStep) ⊔ QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) ∧
      Nat.card ↥(⨆k,F k ctx.criticalPath.firstStep) = 2 * Nat.card
        ↥((⨆k,F k ctx.criticalPath.firstStep) ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))) ∨
    ((Ltilde = twoCoreIn (twoResidualIn (L0 ⊔ QAt ctx.Γ ctx.criticalPath.a')) ⊔
      QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) ∧
      (⨆k,F k ctx.criticalPath.firstStep) ≤ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))
  source_seven : ∀ D : Subgroup H, D ≤ F (ctx.Γ.act y⁻¹ ctx.criticalPath.a') d →
    ⁅D,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a' → D ≤ ZAt ctx.Γ d
  forward : F (ctx.Γ.act y⁻¹ ctx.criticalPath.a') d ⊓ GAt ctx.Γ ctx.criticalPath.a ≤ ZAt ctx.Γ d

@[expose] public def EightFourSourceNineData.toLocal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {ctx : SectionEightContext H S0 S P1 P2}
    {F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H}
    (data : EightFourSourceNineData ctx F) :
    EightFourSourceNineLocalData ctx.toLocalContext F where
  A := data.A
  L0 := data.L0
  x := data.x
  d := data.d
  y := data.y
  Ltilde := data.Ltilde
  hA := data.hA
  hcard := data.hcard
  hAnot := data.hAnot
  hAprev := data.hAprev
  hcontrol := data.hcontrol
  hL0 := data.hL0
  hLgen := data.hLgen
  hx := data.hx
  hfirstfull := data.hfirstfull
  hd := data.hd
  hy := data.hy
  hLtilde := data.hLtilde
  hadj := data.hadj
  hfull := data.hfull
  hcase := data.hcase
  source_seven := data.source_seven
  forward := data.forward

@[expose] public def EightFourSourceNineData.ofLocal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {ctx : SectionEightContext H S0 S P1 P2}
    {F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H}
    (data : EightFourSourceNineLocalData ctx.toLocalContext F) :
    EightFourSourceNineData ctx F where
  A := data.A
  L0 := data.L0
  x := data.x
  d := data.d
  y := data.y
  Ltilde := data.Ltilde
  hA := data.hA
  hcard := data.hcard
  hAnot := data.hAnot
  hAprev := data.hAprev
  hcontrol := data.hcontrol
  hL0 := data.hL0
  hLgen := data.hLgen
  hx := data.hx
  hfirstfull := data.hfirstfull
  hd := data.hd
  hy := data.hy
  hLtilde := data.hLtilde
  hadj := data.hadj
  hfull := data.hfull
  hcase := data.hcase
  source_seven := data.source_seven
  forward := data.forward

@[expose] public def EightFourSourceNineData.localEquiv
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H) :
    EightFourSourceNineData ctx F ≃ EightFourSourceNineLocalData ctx.toLocalContext F where
  toFun := EightFourSourceNineData.toLocal
  invFun := EightFourSourceNineData.ofLocal
  left_inv data := by cases data; rfl
  right_inv data := by cases data; rfl

end Stellmacher.SectionEight
