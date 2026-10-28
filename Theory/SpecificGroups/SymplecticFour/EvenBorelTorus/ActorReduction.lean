module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Graph
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Transport
public import Theory.GroupTheory.SylowInnerAction
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Conditional transfer from the Sp₄ torus to intrinsic two-power actors

For the actual Sp₄(F), a two-group of automorphisms containing the inner
Sylow subgroup and stabilizing that Sylow acts on the rank-two Borel torus.
The action lies in the exceptional graph-generated group, and its kernel is
exactly the inner Sylow subgroup. The three-residual fixer and the cyclic
commutator quotient transfer through the actual Borel character map and
actual Sylow conjugation, without replacing an actor by an involution power.

Two arithmetic implications for nonidentity two-power graph-torus actors are
kept explicit: fixing the three-residual forces degree two or six, and those
degrees give displacement image larger than three. Together with precisely
the diagram-preserving semilinear classification, they imply both intrinsic
conclusions used in Aschbacher–Smith, proof of 13.8.20, printed p.954.
There is no Sp₄(4) exception. Arithmetic instantiation and the surrounding
source-theorem assembly are separate from this conditional transfer.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Graph-power membership at the specified Sylow, with the exact classification input. -/
theorem torusActionAt_mem_graph {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (S : Sylow 2 (Sp F)) (a : stabilizerAt S) :
    torusActionAt hF hn.le S a ∈ zpowers (graphTorus (F := F)) :=
  torusAction_mem_graph hF hn hclass (alignActorHom hF hn.le S a)

/-- Alignment does not change whether an actor is inner. -/
theorem torusActionAt_eq_one_iff_inner {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (S : Sylow 2 (Sp F)) (a : stabilizerAt S) :
    torusActionAt hF hn.le S a = 1 ↔ a.val ∈ MulAut.innerSubgroup (Sp F) := by
  change torusAction hF (alignActorHom hF hn.le S a) = 1 ↔ _
  rw [torusAction_eq_one_iff_inner hF hn hclass]
  change MulAut.congr (alignment hF hn.le S).symm a.val ∈ MulAut.innerSubgroup (Sp F) ↔ _
  conv_lhs => rw [← MulAut.map_innerSubgroup_congr (alignment hF hn.le S).symm]
  exact mem_map_iff_mem (MulAut.congr (alignment hF hn.le S).symm).injective

omit [Finite F] in
/-- Within the acting two-group, the inner actors are exactly those induced by S. -/
theorem inner_iff_mem_innerSylow (S : Sylow 2 (Sp F))
    (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hI : (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ A)
    {a : MulAut (Sp F)} (ha : a ∈ A) :
    a ∈ MulAut.innerSubgroup (Sp F) ↔
      a ∈ (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact mem_map_of_mem _ (MulAut.inner_mem_image_sylow EvenProjective.center_eq_bot S A hA hI ha)
  · rintro ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩

omit [CharP F 2] in
/-- Restriction of the actual actor inclusion, without discarding its kernel. -/
def actorsAt (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F)))
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S) :
    A →* stabilizerAt S where
  toFun a := ⟨a.val, hS a.val a.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [CharP F 2] in
theorem torusActionAt_isPGroup {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    (a : A) : IsPGroup 2 (zpowers (torusActionAt hF hn S (actorsAt S A hS a))) := by
  let f := (torusActionAt hF hn S).comp (actorsAt S A hS)
  have h := (hA.to_subgroup (zpowers a)).map f
  rw [MonoidHom.map_zpowers] at h
  exact h

/-- The kernel on the given acting two-group is precisely the inner Sylow subgroup. -/
theorem actor_torus_kernel {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hI : (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S) :
    ((torusActionAt hF hn.le S).comp (actorsAt S A hS)).ker =
      ((S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F))).subgroupOf A := by
  ext a
  exact (torusActionAt_eq_one_iff_inner hF hn hclass S (actorsAt S A hS a)).trans
    (inner_iff_mem_innerSylow S A hA hI a.property)

/-- The intrinsic source fixer, conditional only on semilinear coverage and torus arithmetic. -/
theorem fixes_residualAt_iff_mem_innerSylow {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hdegree : ∀ τ ∈ zpowers (graphTorus (F := F)), IsPGroup 2 (zpowers τ) → τ ≠ 1 →
      (∀ x ∈ pResidual 3 (Fˣ × Fˣ), τ x = x) → n = 2 ∨ n = 6)
    (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hI : (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    {a : MulAut (Sp F)} (ha : a ∈ A) :
    (∀ b ∈ (pResidual 3 (residualAt S)).map (residualAt S).subtype ⊔ (residualAt S).pCoreIn 2,
      b⁻¹ * a b ∈ (residualAt S).pCoreIn 2) ↔
    a ∈ (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) := by
  let aS := actorsAt S A hS ⟨a, ha⟩
  change (∀ b ∈ (pResidual 3 (residualAt S)).map (residualAt S).subtype ⊔ (residualAt S).pCoreIn 2,
      b⁻¹ * aS.val b ∈ (residualAt S).pCoreIn 2) ↔ _
  rw [fixes_residualAt_iff hF hn.le S aS]
  have hi : torusActionAt hF hn.le S aS = 1 ↔
      a ∈ (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) :=
    (torusActionAt_eq_one_iff_inner hF hn hclass S aS).trans
      (inner_iff_mem_innerSylow S A hA hI ha)
  constructor
  · intro hfix
    apply hi.mp
    by_contra hne
    rcases hdegree _ (torusActionAt_mem_graph hF hn hclass S aS)
      (torusActionAt_isPGroup hF hn.le S A hA hS ⟨a, ha⟩) hne hfix with h | h
    · exact hn2 h
    · exact hn6 h
  · intro haI
    rw [hi.mpr haI]
    intro x _
    rfl

/-- Every outer two-power actor has the source commutator bound, including over F₄. -/
theorem three_lt_commutator_quotient {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hbound : ∀ τ ∈ zpowers (graphTorus (F := F)), IsPGroup 2 (zpowers τ) → τ ≠ 1 →
      (n = 2 ∨ n = 6) → 3 < Nat.card (torusDisplacement τ).range)
    (hsmall : n = 2 ∨ n = 6)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    {a : MulAut (Sp F)} (ha : a ∈ A) (houter : a ∉ MulAut.innerSubgroup (Sp F)) :
    3 < Nat.card (commutatorSubgroup (zpowers a) (Sp F) (residualAt S) ⧸
      pCore 2 (commutatorSubgroup (zpowers a) (Sp F) (residualAt S))) := by
  let aS := actorsAt S A hS ⟨a, ha⟩
  have hne : torusActionAt hF hn.le S aS ≠ 1 :=
    fun h => houter ((torusActionAt_eq_one_iff_inner hF hn hclass S aS).mp h)
  exact (hbound _ (torusActionAt_mem_graph hF hn hclass S aS)
    (torusActionAt_isPGroup hF hn.le S A hA hS ⟨a, ha⟩) hne hsmall).trans_le
      (displacementAt_card_le hF hn.le S aS)

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
