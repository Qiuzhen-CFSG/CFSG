module

public import Theory.AlgebraicGroup.Borel.PositiveRootSupportGeometry.RegularCocharacter.RootCurves

/-!
Regular cocharacters detecting the root support of a Borel: the root-curve step.

If a cocharacter has centralizer equal to the torus and its limit subgroup is
`B`, every realized root has nonzero pairing and lies in `B` exactly when its
pairing is positive. The root-curve test proves nonnegativity, and the diagonal
Cartan equation excludes trivial root characters and hence zero pairings.

The geometric construction of such a cocharacter from reductivity, maximality
of the torus and the Borel hypotheses remains to be supplied. These conditional
results do not assert that existence or use the stored root height. Source:
Borel, *Linear Algebraic Groups*, IV, 13.1--13.10 and 13.18(5)(b--d); GLS3,
Theorem 1.11.2. The raw inverse-conjugation convention is preserved throughout.
-/

universe u

namespace Theory.AlgebraicGroup.BorelCocharacter

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- The diagonal Cartan value two and the actual cocharacter equations force
every realized root character to be nontrivial. -/
public theorem rootWeight_ne_one_of_realization
    {D : RootGroupData G T} (hD : D.IsRealization) (a : D.Root) :
    D.rootWeight a ≠ 1 := by
  intro hone
  have hp := hD.characterCorootPairing_rootWeight a a
  rw [hone] at hp
  have hz : D.characterCorootPairing a (Additive.ofMul (1 : TorusWeight T)) = 0 :=
    map_zero _
  rw [hz] at hp
  have hself : D.pairing a a = 2 := hD.2.2.2.2.2.2.1 a
  omega

/-- The geometric centralizer condition implies regularity on every actual
root of a supplied realization. -/
public theorem regular_of_centralizesOnlyTorus
    (hT : IsSubtorus T) {D : RootGroupData G T} (hD : D.IsRealization)
    (c : ClosedSubgroupTorusCocharacter T) (hc : CentralizesOnlyTorus c) :
    ∀ a, characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a)) ≠ 0 := by
  intro a
  exact pairing_ne_zero_of_centralizesOnlyTorus hT
    (hD.2.2.1 a).1 (hD.2.2.1 a).2 (rootWeight_ne_one_of_realization hD a) c hc

/-- The limit description of a Borel supplies both precise premises consumed
by `RootGroupData.isPositiveSystem_borelRootSupport_of_cocharacter`. The two
geometric assumptions on the cocharacter remain explicit here. -/
public theorem regular_detects_roots_of_limit_description
    (hT : IsSubtorus T) {D : RootGroupData G T} (hD : D.IsRealization)
    (B : ClosedSubgroup G) (c : ClosedSubgroupTorusCocharacter T)
    (hc : CentralizesOnlyTorus c)
    (hB : ∀ g : Variety.Point G, g ∈ B ↔ HasLimit c g) :
    (∀ a, characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a)) ≠ 0) ∧
      (∀ a, D.rootSubgroup a ≤ B ↔
        0 < characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a))) := by
  have hregular := regular_of_centralizesOnlyTorus hT hD c hc
  refine ⟨hregular, ?_⟩
  intro a
  have hroot := rootSubgroup_hasLimit_iff_nonneg
    (hD.2.2.1 a).1 (hD.2.2.1 a).2 c
  have hle : D.rootSubgroup a ≤ B ↔
      ∀ g, g ∈ D.rootSubgroup a → HasLimit c g := by
    constructor
    · intro h g hg
      exact (hB g).mp (h hg)
    · intro h g hg
      exact (hB g).mpr (h g hg)
  rw [hle, hroot]
  have hne := hregular a
  omega

/-- Apply the root-curve criterion to a literal equality between a closed
subgroup and the cocharacter limit subgroup. Construction of the cocharacter
and this equality from the Borel hypotheses is a separate geometric input. -/
public theorem regular_detects_roots_of_limitSubgroup
    (hT : IsSubtorus T) {D : RootGroupData G T} (hD : D.IsRealization)
    (B : ClosedSubgroup G) (c : ClosedSubgroupTorusCocharacter T)
    (hc : CentralizesOnlyTorus c) (hB : B.toSubgroup = limitSubgroup c) :
    (∀ a, characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a)) ≠ 0) ∧
      (∀ a, D.rootSubgroup a ≤ B ↔
        0 < characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a))) := by
  apply regular_detects_roots_of_limit_description hT hD B c hc
  intro g
  change g ∈ B.toSubgroup ↔ g ∈ limitSubgroup c
  rw [hB]
end Theory.AlgebraicGroup.BorelCocharacter
