module
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Roots
public import Theory.SpecificGroups.LieType.ExceptionalSplitModels

/-!
# The folded simple root subgroup in the concrete E6 cover

The diagram orbits are {0,5}, {1,4}, {2}, {3}. Products on the two
orthogonal pairs and the two singleton root curves are additive, for either
sign. The pinned diagram automorphism fixes every generator, hence their
whole generated subgroup. A moved simple root proves this subgroup proper
in the split matrix cover, over every field.

This constructs the subgroup used for F4 folding. Its identification with
`ExceptionalSplit.F4`, and survival and properness after central quotients,
are separate assertions and are not assumed here. The existing binary
root-normalizer module supplies the characteristic-independent E6
irreducibility proof; no characteristic-two hypothesis is used below.

Sources: GLS3, §§2.3 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), and the
exceptional inclusions in Aschbacher--Smith A.2.17, printed p.39 of
`refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace TwistedE6.FoldedSubsystem
attribute [local instance] Classical.decEq
local instance : Pairing.IsIrreducible := TheoremDRootNormalizer.pairing_irreducible
abbrev simpleIndex (i : Fin 6) : Base.support := typeE6RootPairing_baseEquiv i
variable (F : Type*) [Field F]

def simpleRoot (s : Bool) (i : Fin 6) (t : F) :
    splitCarrier F :=
  let := Pairing.indexNeg
  if s then rootElement (F) (simpleIndex i) t else rootElement (F) (-(simpleIndex i) : typeE6Roots) t

@[simp] theorem simpleRoot_val (s : Bool) (i : Fin 6) (t : F) :
    (simpleRoot F s i t).val =
      (RootPairing.SimpleGeckGroup.simpleFamily (b := Base)).unit (s, simpleIndex i) t := by
  let := Pairing.indexNeg
  cases s
  · exact rootCurveUnit_neg_simple (simpleIndex i) t
  · exact rootCurveUnit_simple (simpleIndex i) t

@[simp] theorem simpleRoot_zero (s : Bool) (i : Fin 6) : simpleRoot F s i 0 = 1 := by
  apply Subtype.ext
  simp [simpleRoot_val]

theorem simpleRoot_add (s : Bool) (i : Fin 6) (t u : F) :
    simpleRoot F s i (t + u) = simpleRoot F s i t * simpleRoot F s i u := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, simpleRoot_val]
  exact (RootPairing.SimpleGeckGroup.simpleFamily (b := Base)).unit_add _ t u

theorem simpleRoot_commute (s : Bool) (i j : Fin 6)
    (hij : i ≠ j) (hc : typeE6CartanMatrix j i = 0) (t u : F) :
    Commute (simpleRoot F s i t) (simpleRoot F s j u) := by
  have hn : simpleIndex i ≠ simpleIndex j := fun h => hij (typeE6RootPairing_baseEquiv.injective h)
  have hz : Base.cartanMatrix (simpleIndex j) (simpleIndex i) = 0 :=
    (typeE6RootPairing_base_cartan_apply j i).trans hc
  apply Subtype.ext
  simp only [Subgroup.coe_mul, simpleRoot_val]
  cases s
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero
        (simpleIndex i) (simpleIndex j) hn hz t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero
        (simpleIndex i) (simpleIndex j) hn hz t u).eq

theorem simpleRoot_opposite_commute (i j : Fin 6)
    (hij : i ≠ j) (t u : F) :
    Commute (simpleRoot F true i t) (simpleRoot F false j u) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, simpleRoot_val]
  exact congrArg Subtype.val (RootPairing.SimpleGeckGroup.commute_positive_negative
    (simpleIndex i) (simpleIndex j)
    (fun h => hij (typeE6RootPairing_baseEquiv.injective h)) t u).eq

def foldedSimple (s : Bool) (i : Fin 4) (t : F) :
    splitCarrier F :=
  ![simpleRoot F s 0 t * simpleRoot F s 5 t,
    simpleRoot F s 1 t * simpleRoot F s 4 t,
    simpleRoot F s 2 t, simpleRoot F s 3 t] i

theorem foldedSimple_add (s : Bool) (i : Fin 4) (t u : F) :
    foldedSimple F s i (t + u) = foldedSimple F s i t * foldedSimple F s i u := by
  have h (a b : Fin 6) (hne : a ≠ b) (hc : typeE6CartanMatrix b a = 0) :
      simpleRoot F s a (t + u) *
        simpleRoot F s b (t + u) =
      (simpleRoot F s a t * simpleRoot F s b t) *
        (simpleRoot F s a u * simpleRoot F s b u) := by
    simp only [simpleRoot_add]
    exact (simpleRoot_commute F s a b hne hc u t).mul_mul_mul_comm _ _
  fin_cases i
  · exact h 0 5 (by decide) (by decide)
  · exact h 1 4 (by decide) (by decide)
  · exact simpleRoot_add F s 2 t u
  · exact simpleRoot_add F s 3 t u

@[simp] theorem foldedSimple_zero (s : Bool) (i : Fin 4) : foldedSimple F s i 0 = 1 := by
  fin_cases i <;> simp [foldedSimple]

theorem simpleRoot_diagram (s : Bool) (i : Fin 6) (t : F) :
    pinnedDiagram F (simpleRoot F s i t) =
      simpleRoot F s (typeE6DiagramPermutation i) t := by
  let := Pairing.indexNeg
  cases s
  · change pinnedDiagram F (rootElement F (-(simpleIndex i) : typeE6Roots) t) =
      rootElement F (-(simpleIndex (typeE6DiagramPermutation i)) : typeE6Roots) t
    rw [pinnedDiagram_negative]
    congr 2
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)
  · change pinnedDiagram F (rootElement F (simpleIndex i) t) =
      rootElement F (simpleIndex (typeE6DiagramPermutation i)) t
    rw [pinnedDiagram_positive]
    congr 1
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)

theorem foldedSimple_fixed (s : Bool) (i : Fin 4) (t : F) :
    pinnedDiagram F (foldedSimple F s i t) = foldedSimple F s i t := by
  fin_cases i
  · change pinnedDiagram F (simpleRoot F s 0 t * simpleRoot F s 5 t) = _
    rw [map_mul, simpleRoot_diagram, simpleRoot_diagram]
    exact (simpleRoot_commute F s 5 0 (by decide) (by decide) t t).eq
  · change pinnedDiagram F (simpleRoot F s 1 t * simpleRoot F s 4 t) = _
    rw [map_mul, simpleRoot_diagram, simpleRoot_diagram]
    exact (simpleRoot_commute F s 4 1 (by decide) (by decide) t t).eq
  · simp [foldedSimple, simpleRoot_diagram, typeE6DiagramPermutation]
  · simp [foldedSimple, simpleRoot_diagram, typeE6DiagramPermutation]

/-- The subgroup generated by the eight folded simple root curves. -/
def splitSubgroup : Subgroup (splitCarrier F) :=
  Subgroup.closure (Set.range fun x : Bool × Fin 4 × F => foldedSimple F x.1 x.2.1 x.2.2)

theorem foldedSimple_mem (s : Bool) (i : Fin 4) (t : F) :
    foldedSimple F s i t ∈ splitSubgroup F := Subgroup.subset_closure ⟨(s, i, t), rfl⟩

theorem splitSubgroup_fixed {g : splitCarrier F} (hg : g ∈ splitSubgroup F) :
    pinnedDiagram F g = g := by
  have h : splitSubgroup F ≤ (pinnedDiagram F).toMonoidHom.eqLocus (MonoidHom.id _) := by
    rw [splitSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨s, i, t⟩, rfl⟩
    exact foldedSimple_fixed F s i t
  exact h hg

/-- Properness is established in the cover, before any central quotient. -/
theorem splitSubgroup_ne_top : splitSubgroup F ≠ ⊤ := by
  intro htop
  apply pinnedDiagram_moves_positive_zero F
  apply splitSubgroup_fixed F
  rw [htop]
  trivial

/-- The E6 diagram orbit associated to each folded node. -/
def diagramOrbit (i : Fin 4) : Finset (Fin 6) := ![{0, 5}, {1, 4}, {2}, {3}] i

/-- Pair a chosen orbit representative with the sum of the coroots in an orbit. -/
def foldedCartan (i j : Fin 4) : ℤ :=
  let r : Fin 6 := ![0, 1, 2, 3] i
  ![typeE6CartanMatrix r 0 + typeE6CartanMatrix r 5,
    typeE6CartanMatrix r 1 + typeE6CartanMatrix r 4,
    typeE6CartanMatrix r 2, typeE6CartanMatrix r 3] j

/-- The library's F4 numbering reverses the order of the four E6 diagram orbits. -/
theorem foldedCartan_f4 : ∀ i j : Fin 4,
    foldedCartan i.rev j.rev = typeF4CartanMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [foldedCartan, typeF4CartanMatrix, typeE6CartanMatrix, Fin.rev, Fin.ext_iff]

/-- A folded simple root in the existing F4 node order, with both signs. -/
def f4Simple (s : Bool) (i : Fin 4) (t : F) : splitSubgroup F :=
  ⟨foldedSimple F s i.rev t, foldedSimple_mem F s i.rev t⟩

/-- The literal map from the folded matrix subgroup to the split E6 central quotient.
Its injectivity and properness do not follow from properness in the cover alone. -/
def splitModelMap : splitSubgroup F →* ExceptionalSplit.E6 F :=
  (ExceptionalSplit.projection Pairing Base F).comp (splitSubgroup F).subtype

@[simp] theorem splitModelMap_eq_one_iff (g : splitSubgroup F) :
    splitModelMap F g = 1 ↔ g.val ∈ Subgroup.center (splitCarrier F) :=
  ExceptionalSplit.projection_eq_one_iff Pairing Base F g.val

section FieldMap
variable {F K : Type*} [Field F] [Field K]

/-- Entrywise field change on the literal split E6 matrix carrier. -/
def splitFieldMap (f : F →+* K) : splitCarrier F →* splitCarrier K where
  toFun g := ⟨RootPairing.SimpleGeckGroup.IntegralCubicFamily.mapUnits f g.val, by
    have hg : g.val ∈ RootPairing.SimpleGeckGroup.subgroup Base F := by
      simpa only [splitCarrier_eq_simple] using g.property
    simpa only [splitCarrier_eq_simple, RootPairing.SimpleGeckGroup.subgroup] using
      (RootPairing.SimpleGeckGroup.simpleFamily (b := Base)).mapUnits_mem f hg⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem splitFieldMap_injective (f : F →+* K) : Function.Injective (splitFieldMap f) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun x : splitCarrier K => x.val.val i j) he

@[simp] theorem splitFieldMap_simpleRoot (f : F →+* K) (s : Bool) (i : Fin 6) (t : F) :
    splitFieldMap f (simpleRoot F s i t) = simpleRoot K s i (f t) := by
  apply Subtype.ext
  change RootPairing.SimpleGeckGroup.IntegralCubicFamily.mapUnits f
    (simpleRoot F s i t).val = (simpleRoot K s i (f t)).val
  rw [simpleRoot_val, simpleRoot_val]
  exact (RootPairing.SimpleGeckGroup.simpleFamily (b := Base)).mapUnits_unit f (s, simpleIndex i) t

@[simp] theorem splitFieldMap_foldedSimple (f : F →+* K) (s : Bool) (i : Fin 4) (t : F) :
    splitFieldMap f (foldedSimple F s i t) = foldedSimple K s i (f t) := by
  fin_cases i <;> simp [foldedSimple]

end FieldMap

end TwistedE6.FoldedSubsystem
