module
public import Theory.SpecificGroups.LieType.F4RootSL2
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootSubsystemResidual

/-!
# The orthogonal-root candidate for the F4 residual centralizer

Fix the actual long root used by `F4RootSL2.hom`. Generate a subgroup of the
52-dimensional elementary matrix group by all root curves orthogonal to
that root, and take its image under the defining central projection of F4.
These are literal subgroups, with no symplectic identification assumed.

Root generation proves both candidates equal to their own prime-to-p
residual in characteristic p. If the projected candidate centralizes the
specified SL2, its elementary subgroup therefore maps into the source's
residual centralizer. This map is surjective once that residual is contained
in the projected candidate. Its kernel is exactly the relative intersection
with the elementary group's center; no centerlessness is asserted here.

Source: Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`,
referencing Asc80, Theorem 1, p.402; GLS3 §2.6 for the literal subsystem
construction. `F4RootCentralizer` consumes the maps below, while the
symplectic realization and residual containment are independent obligations.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootCentralizer
open F4RootSL2
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
variable {F : Type*} [Field F]

/-- The roots orthogonal to the marked long simple root, using the actual F4 pairing. -/
def complementaryRoots : Set typeF4Roots :=
  {r | typeF4RootPairing.pairing r fundamentalRoot = 0}

/-- The literal orthogonal-root subgroup before taking the central quotient. -/
abbrev elementaryComplement (F : Type*) [Field F] : Subgroup (Elementary F) :=
  elementaryRootSubgroup (P := typeF4RootPairing) (b := typeF4RootPairing_base)
    (F := F) complementaryRoots

/-- Its image under the central projection defining the concrete F4 carrier. -/
abbrev projectedComplement (F : Type*) [Field F] : Subgroup (F4 F) :=
  projectedRootSubgroup (P := typeF4RootPairing) (b := typeF4RootPairing_base)
    (F := F) complementaryRoots

/-- The centralizer of the fixed fundamental root-pair subgroup in F4. -/
abbrev Centralizer (F : Type*) [Field F] :=
  f4FundamentalCentralizer (F := F) fundamentalRoot

/-- The source residual O^{p′} inside that literal centralizer. -/
abbrev Residual (p : ℕ) (F : Type*) [Field F] :=
  f4FundamentalResidual (F := F) p fundamentalRoot

/-- The root-pair centralizer is exactly the centralizer of the proved SL2 range. -/
theorem centralizer_eq_range_centralizer :
    Centralizer F = Subgroup.centralizer ((hom (F := F)).range : Set (F4 F)) := by
  rw [hom_range]

/-- The actual central projection restricted to the orthogonal-root subgroup. -/
def complementProjection : elementaryComplement F →* projectedComplement F :=
  rootSubgroupProjection complementaryRoots

/-- The restricted projection covers the projected candidate. -/
theorem complementProjection_surjective :
    Function.Surjective (complementProjection (F := F)) :=
  rootSubgroupProjection_surjective complementaryRoots

/-- Only the relative ambient center is killed by the projection. -/
theorem complementProjection_ker :
    (complementProjection (F := F)).ker =
      (Subgroup.center (Elementary F)).subgroupOf (elementaryComplement F) :=
  rootSubgroupProjection_ker complementaryRoots

/-- The precise central-kernel qualification for faithfulness after projection. -/
theorem complementProjection_injective_iff :
    Function.Injective (complementProjection (F := F)) ↔
      Disjoint (elementaryComplement F) (Subgroup.center (Elementary F)) :=
  rootSubgroupProjection_injective_iff complementaryRoots

/-- The elementary candidate is its own defining-characteristic residual. -/
theorem elementaryComplement_primeToResidual (p : ℕ) [CharP F p] :
    Subgroup.primeToResidual p (elementaryComplement F) = ⊤ :=
  elementaryRootSubgroup_primeToResidual p complementaryRoots

/-- The same residual calculation holds in the actual F4 quotient. -/
theorem projectedComplement_primeToResidual (p : ℕ) [CharP F p] :
    Subgroup.primeToResidual p (projectedComplement F) = ⊤ :=
  projectedRootSubgroup_primeToResidual p complementaryRoots

/-- The candidate maps to the literal centralizer once commutation is proved. -/
def complementToCentralizer (hcomm : projectedComplement F ≤ Centralizer F) :
    elementaryComplement F →* Centralizer F :=
  (Subgroup.inclusion hcomm).comp complementProjection

/-- Defining-characteristic generation places every candidate element in the residual. -/
theorem complementToCentralizer_mem_residual (p : ℕ) [CharP F p]
    (hcomm : projectedComplement F ≤ Centralizer F) (x : elementaryComplement F) :
    complementToCentralizer hcomm x ∈ Subgroup.primeToResidual p (Centralizer F) := by
  apply Subgroup.map_primeToResidual_le_of_hom p (complementToCentralizer hcomm)
  exact ⟨x, by rw [elementaryComplement_primeToResidual]; trivial, rfl⟩

/-- The concrete map through the elementary group and the F4 central quotient into O^{p′}. -/
def complementToResidual (p : ℕ) [CharP F p]
    (hcomm : projectedComplement F ≤ Centralizer F) :
    elementaryComplement F →* Residual p F :=
  (complementToCentralizer hcomm).codRestrict _
    (complementToCentralizer_mem_residual p hcomm)

/-- The composite to F4 is exactly the prescribed central projection. -/
@[simp] theorem complementToResidual_val (p : ℕ) [CharP F p]
    (hcomm : projectedComplement F ≤ Centralizer F) (x : elementaryComplement F) :
    ((complementToResidual p hcomm x).val : F4 F) =
      projection typeF4RootPairing typeF4RootPairing_base F x.val := rfl

/-- Restriction to the residual introduces no extra kernel. -/
theorem complementToResidual_ker (p : ℕ) [CharP F p]
    (hcomm : projectedComplement F ≤ Centralizer F) :
    (complementToResidual p hcomm).ker =
      (Subgroup.center (Elementary F)).subgroupOf (elementaryComplement F) := by
  ext x
  change (complementToResidual p hcomm x = 1) ↔ _
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact projection_eq_one_iff _ _ F x.val

/-- Residual containment suffices for surjectivity; full centralizer containment is unnecessary. -/
theorem complementToResidual_surjective (p : ℕ) [CharP F p]
    (hcomm : projectedComplement F ≤ Centralizer F)
    (hcover : (Subgroup.primeToResidual p (Centralizer F)).map
      (Centralizer F).subtype ≤ projectedComplement F) :
    Function.Surjective (complementToResidual p hcomm) := by
  intro x
  obtain ⟨y, hy⟩ := complementProjection_surjective
    (⟨x.val.val, hcover ⟨x.val, x.property, rfl⟩⟩ : projectedComplement F)
  refine ⟨y, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : projectedComplement F => (z : F4 F)) hy

end ExceptionalSplit.F4RootCentralizer
end
