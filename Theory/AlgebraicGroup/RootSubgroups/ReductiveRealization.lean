module

public import Theory.AlgebraicGroup.RootSubgroups.CharacterRootGeometry
public import Theory.AlgebraicGroup.RootSubgroups.CocharacterExistence

/-!
# Constructing root-group data from actual character geometry

Starting from a reduced crystallographic root pairing embedded in the actual
torus character lattice, choose a base and its usual integral height. Roots
are indexed by their original characters, addition tests whether the character
product is a root, and negation and reflection are transported through the
faithful character embedding. Root subgroups are chosen from the definition
of an actual root. Integral coroot functionals on the whole character lattice
are realized by algebraic cocharacters using the Laurent-character theorem.

The two geometric inputs remain explicit. This is the assembly step of GLS3,
Theorem 1.9.5(d) and Remarks 1.9.6, not a proof that reductivity supplies those
inputs. In particular, no numbered placeholder theorem is used. The positive
system and simple roots come from a genuine root-system base, including its
nonzero heights and characterization by indecomposable positive roots.

Source: GLS3 §§1.8--1.9; Borel, *Linear Algebraic Groups*, §§14.7--14.8.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- The partial sum on actual roots, defined precisely when the character
product is again an actual root. -/
@[expose]
public noncomputable def torusRootIndexAdd (α β : TorusRootIndex T) :
    Option (TorusRootIndex T) := by
  classical
  exact if h : IsTorusRoot T (α.val * β.val) then some ⟨α.val * β.val, h⟩ else none

omit [IsAlgClosed k] in
/-- The partial sum contains every actual root sum and no other sums. -/
public theorem torusRootIndexAdd_eq_some_iff (α β γ : TorusRootIndex T) :
    torusRootIndexAdd α β = some γ ↔ γ.val = α.val * β.val := by
  classical
  unfold torusRootIndexAdd
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun h => (congrArg Subtype.val h).symm,
      fun h => Subtype.ext h.symm⟩
  · constructor
    · simp
    · intro heq
      exact (h (heq ▸ γ.property)).elim

namespace TorusCharacterRootGeometry

variable (R : TorusCharacterRootGeometry T)

private noncomputable def corootFunctional (hR : R.HasIntegralCoroots)
    (β : TorusRootIndex T) : Additive (TorusWeight T) →+ ℤ :=
  (hR β).choose

omit [IsAlgClosed k] in
private theorem corootFunctional_spec (hR : R.HasIntegralCoroots)
    (α β : TorusRootIndex T) :
    (R.corootFunctional hR β (Additive.ofMul α.val) : ℝ) =
      R.pairing.pairing α β :=
  (hR β).choose_spec α

private noncomputable def algebraicCoroot (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (β : TorusRootIndex T) :
    ClosedSubgroupTorusCocharacter T :=
  (exists_cocharacter_realizing_characterFunctional T hT
    (R.corootFunctional hR β)).choose

private theorem algebraicCoroot_spec (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (χ : TorusWeight T) (β : TorusRootIndex T) :
    WeightCocharacterEquation T χ (R.algebraicCoroot hT hR β)
      (R.corootFunctional hR β (Additive.ofMul χ)) :=
  (exists_cocharacter_realizing_characterFunctional T hT
    (R.corootFunctional hR β)).choose_spec χ

/-- Complete root data using the actual characters, actual root subgroups,
algebraic coroots, and a chosen base of their real root pairing. -/
public noncomputable def rootGroupData (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (b : R.pairing.Base) : RootGroupData G T where
  Root := TorusRootIndex T
  rootWeight := Subtype.val
  rootSubgroup α := α.property.choose
  neg α := R.pairing.reflectionPerm α α
  add := torusRootIndexAdd
  pairing α β := R.corootFunctional hR β (Additive.ofMul α.val)
  weightPairing χ β := R.corootFunctional hR β (Additive.ofMul χ)
  rootCocharacter := R.algebraicCoroot hT hR
  reflect α β := R.pairing.reflectionPerm α β
  positive := {α | b.IsPos α}
  simple := b.support
  height := b.height

private theorem simple_iff_indecomposable (b : R.pairing.Base)
    (α : TorusRootIndex T) :
    α ∈ b.support ↔ b.IsPos α ∧
      ∀ β γ, torusRootIndexAdd β γ = some α → ¬ (b.IsPos β ∧ b.IsPos γ) := by
  constructor
  · intro hα
    refine ⟨b.isPos_of_mem_support hα, ?_⟩
    intro β γ hadd hpos
    have hsum := b.height_add ((R.root_add_iff β γ α).mpr
      ((torusRootIndexAdd_eq_some_iff β γ α).mp hadd))
    have hone := b.height_one_of_mem_support hα
    change 0 < b.height β ∧ 0 < b.height γ at hpos
    omega
  · rintro ⟨hα, hind⟩
    have hdecomp : α ∈ b.support ∨
        ∃ β γ, R.pairing.root α = R.pairing.root β + R.pairing.root γ ∧
          b.IsPos β ∧ b.IsPos γ := by
      apply hα.induction_on_add
        (p := fun δ => b.IsPos δ ∧ (δ ∈ b.support ∨
          ∃ β γ, R.pairing.root δ = R.pairing.root β + R.pairing.root γ ∧
            b.IsPos β ∧ b.IsPos γ)) ?_ ?_ |>.2
      · intro δ hδ
        exact ⟨b.isPos_of_mem_support hδ, Or.inl hδ⟩
      · intro β γ δ hsum hβ hγ
        have hγpos := b.isPos_of_mem_support hγ
        exact ⟨hβ.1.add hγpos hsum, Or.inr ⟨β, γ, hsum, hβ.1, hγpos⟩⟩
    rcases hdecomp with h | ⟨β, γ, hsum, hβ, hγ⟩
    · exact h
    · exact (hind β γ ((torusRootIndexAdd_eq_some_iff β γ α).mpr
        ((R.root_add_iff β γ α).mp hsum)) ⟨hβ, hγ⟩).elim

/-- Every realization clause is supplied by the actual character geometry,
the chosen root groups, and the algebraic character--cocharacter equation. -/
public theorem rootGroupData_isRealization (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (b : R.pairing.Base) :
    (R.rootGroupData hT hR b).IsRealization := by
  refine ⟨Subtype.val_injective, ?_, ?_, R.root_neg, ?_, ?_, ?_,
    (fun _ _ => rfl), ?_, ?_, rfl, ?_, R.algebraicCoroot_spec hT hR⟩
  · ext χ
    exact ⟨fun ⟨α, hα⟩ => hα ▸ α.property, fun hχ => ⟨⟨χ, hχ⟩, rfl⟩⟩
  · intro α
    exact α.property.choose_spec
  · intro α β γ hadd
    exact (torusRootIndexAdd_eq_some_iff α β γ).mp hadd
  · intro α β
    exact R.root_reflect α β _ (R.corootFunctional_spec hR β α)
  · intro α
    have h : (R.corootFunctional hR α (Additive.ofMul α.val) : ℝ) = 2 :=
      (R.corootFunctional_spec hR α α).trans (R.pairing.pairing_same α)
    exact_mod_cast h
  · intro α
    exact b.height_reflectionPerm_self α
  · intro α β γ hadd
    exact b.height_add ((R.root_add_iff α β γ).mpr
      ((torusRootIndexAdd_eq_some_iff α β γ).mp hadd))
  · intro α
    exact R.simple_iff_indecomposable b α

/-- Addition is complete, including all roots appearing as sums. -/
public theorem rootGroupData_isRootAdditionComplete (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (b : R.pairing.Base) :
    (R.rootGroupData hT hR b).IsRootAdditionComplete := by
  intro α β γ hsum
  exact (torusRootIndexAdd_eq_some_iff α β γ).mpr hsum

/-- Heights are the nonzero integral heights of the chosen root-system base. -/
public theorem rootGroupData_height_ne_zero (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (b : R.pairing.Base)
    (α : (R.rootGroupData hT hR b).Root) :
    (R.rootGroupData hT hR b).height α ≠ 0 :=
  b.height_ne_zero α

/-- The chosen positive roots satisfy the full positive-system axioms. -/
public theorem rootGroupData_isPositiveSystem (hT : IsSubtorus T)
    (hR : R.HasIntegralCoroots) (b : R.pairing.Base) :
    IsPositiveSystem (R.rootGroupData hT hR b)
      (R.rootGroupData hT hR b).positive := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro α hα
    change 0 < b.height α ∧ 0 < b.height (R.pairing.reflectionPerm α α) at hα
    have hneg := b.height_reflectionPerm_self α
    change b.height (R.pairing.reflectionPerm α α) = -b.height α at hneg
    omega
  · apply Set.eq_univ_of_forall
    intro α
    exact RootPairing.Base.IsPos.or_neg b α
  · intro α hα β hβ γ hadd
    exact hα.add hβ ((R.root_add_iff α β γ).mpr
      ((torusRootIndexAdd_eq_some_iff α β γ).mp hadd))

end TorusCharacterRootGeometry

/-- Conditional assembly of GLS3 §1.9: character root geometry and integral
coroots give complete realized root data, with genuine positive-root heights.
The reductive existence of the two geometric inputs is a separate theorem. -/
public theorem exists_complete_rootGroupData_of_characterRootGeometry
    (hT : IsSubtorus T) (R : TorusCharacterRootGeometry T)
    (hR : R.HasIntegralCoroots) :
    ∃ D : RootGroupData G T, D.IsRealization ∧ D.IsRootAdditionComplete ∧
      IsPositiveSystem D D.positive ∧ ∀ α, D.height α ≠ 0 := by
  obtain ⟨b⟩ := R.pairing.nonempty_base
  exact ⟨R.rootGroupData hT hR b, R.rootGroupData_isRealization hT hR b,
    R.rootGroupData_isRootAdditionComplete hT hR b,
    R.rootGroupData_isPositiveSystem hT hR b,
    R.rootGroupData_height_ne_zero hT hR b⟩

end Theory.AlgebraicGroup
