module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.RootProducts
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel

/-!
# Fixed and descended coordinates on the triality radical root products

Removing the Levi orbit leaves two GF(q³) and three GF(q) parameters for the
arms node, or three GF(q³) and two GF(q) parameters for the central node.
The proved Geck normal form and its graph-field equivariance give the fixed
root products orders q^9 and q^11. Their two-group property puts every fixed
element in the elementary subgroup. The actual central quotient is injective
in characteristic two, so these counts survive descent to the genuine carrier.

These are results about the root products. Their equality with the original
parabolic normal-closure candidates still requires relative normalization.
All results include q = 2.

Source: GLS3 §§2.3–2.4, Definition 2.6.4
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.11–12
(`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates
open Parabolics

/-- Fixed supported coordinates, before elementary restriction or central quotient. -/
abbrev FixedSupportedCoordinates (P : Parameters) (a : Node) :=
  {v : FixedCoordinates P // ∀ i, ¬ rootSupport a i → v.val i = 0}

/-- The actual independent fields on the two sets of root orbits. -/
abbrev RootOrbitParameters (P : Parameters) : Node → Type
  | .arms => (Fin 2 → ExtensionField P) × (Fin 3 → fixedField P)
  | .central => (Fin 3 → ExtensionField P) × (Fin 2 → fixedField P)

def extendOrbit (P : Parameters) : (a : Node) → RootOrbitParameters P a → OrbitParameters P
  | .arms, v => (![0, v.1 0, v.1 1], v.2)
  | .central, v => (v.1, ![0, v.2 0, v.2 1])

def restrictOrbit (P : Parameters) : (a : Node) → FixedSupportedCoordinates P a →
    RootOrbitParameters P a
  | .arms, v => (![v.val.val 4, v.val.val 7], (restrict P v.val).2)
  | .central, v => ((restrict P v.val).1, ![(restrict P v.val).2 1, (restrict P v.val).2 2])

theorem expand_extendOrbit_supported (P : Parameters) (a : Node) (v : RootOrbitParameters P a) :
    ∀ i, ¬ rootSupport a i → expand P (extendOrbit P a v) i = 0 := by
  cases a <;> intro i hi <;> fin_cases i <;>
    simp_all [rootSupport, expand, extendOrbit, -fieldFrobenius_apply]

/-- Removing the chosen Levi orbit leaves two cubic and three fixed parameters,
or three cubic and two fixed parameters. -/
def rootOrbitEquiv (P : Parameters) (a : Node) :
    RootOrbitParameters P a ≃ FixedSupportedCoordinates P a where
  toFun v := ⟨⟨expand P (extendOrbit P a v), expand_fixed P _⟩,
    expand_extendOrbit_supported P a v⟩
  invFun := restrictOrbit P a
  left_inv v := by
    cases a <;> apply Prod.ext
    all_goals
      funext i
      fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    have he : extendOrbit P a (restrictOrbit P a v) = restrict P v.val := by
      cases a
      · apply Prod.ext
        · funext i
          fin_cases i
          · exact (v.property 0 (by decide)).symm
          · rfl
          · rfl
        · rfl
      · apply Prod.ext
        · rfl
        · funext i
          fin_cases i
          · exact Subtype.ext (v.property 3 (by decide)).symm
          · rfl
          · rfl
    change fixedCoordinatesEquiv P (extendOrbit P a (restrictOrbit P a v)) = v.val
    rw [he]
    exact (fixedCoordinatesEquiv P).apply_symm_apply v.val

/-- Faithful fixed coordinates on the actual positive-root subgroup. -/
def fixedRootEquiv (P : Parameters) (hp : P.prime = 2) (a : Node) :
    FixedSupportedCoordinates P a ≃ (rootSubgroup P a).comap (fixedSubgroup P).subtype := by
  have hi : Function.Injective (orderedProduct P) := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact orderedProduct_injective_binary n hn
  have ht (v : Coordinates P) :
      graphFieldAutomorphism P (orderedProduct P v) = orderedProduct P (twist P v) := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact graphField_orderedProduct_binary n hn v
  let f : FixedSupportedCoordinates P a →
      (rootSubgroup P a).comap (fixedSubgroup P).subtype := fun v =>
    ⟨⟨orderedProduct P v.val.val, by rw [mem_fixedSubgroup, ht, v.val.property]⟩,
      orderedProduct_mem_rootSubgroup P a ⟨v.val.val, v.property⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w h
    exact Subtype.ext (Subtype.ext (hi (congrArg (fun g => g.val.val) h)))
  · intro g
    obtain ⟨v, hv⟩ := (mem_rootSubgroup_iff P hp a g.val.val).mp g.property
    have hfix : twist P v.val = v.val := by
      apply hi
      calc
        orderedProduct P (twist P v.val) =
            graphFieldAutomorphism P (orderedProduct P v.val) := (ht v.val).symm
        _ = graphFieldAutomorphism P g.val.val := congrArg (graphFieldAutomorphism P) hv
        _ = g.val.val := g.val.property
        _ = orderedProduct P v.val := hv.symm
    exact ⟨⟨⟨v.val, hfix⟩, v.property⟩, Subtype.ext (Subtype.ext hv)⟩

@[simp] theorem fixedRootEquiv_val (P : Parameters) (hp : P.prime = 2) (a : Node)
    (v : FixedSupportedCoordinates P a) :
    (fixedRootEquiv P hp a v).val.val = orderedProduct P v.val.val := rfl

/-- The exponents are the sums of the sizes of the surviving diagram orbits. -/
def fixedDimension : Node → ℕ
  | .arms => 9
  | .central => 11

theorem card_fixedSupportedCoordinates (P : Parameters) (a : Node) :
    Nat.card (FixedSupportedCoordinates P a) = P.q ^ fixedDimension a := by
  rw [← Nat.card_congr (rootOrbitEquiv P a)]
  cases a <;> simp only [RootOrbitParameters, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    card_extensionField, card_fixedField, ← pow_mul, ← pow_add, fixedDimension]

theorem card_fixedRootSubgroup (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Nat.card ((rootSubgroup P a).comap (fixedSubgroup P).subtype) = P.q ^ fixedDimension a := by
  rw [← Nat.card_congr (fixedRootEquiv P hp a)]
  exact card_fixedSupportedCoordinates P a

/-- Every fixed element of the root subgroup belongs to the elementary group,
by its proved characteristic-power order. -/
theorem fixedRootSubgroup_le_elementary (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (rootSubgroup P a).comap (fixedSubgroup P).subtype ≤ elementarySubgroup P := by
  intro g hg
  obtain ⟨k, hk⟩ := isPGroup_rootSubgroup P hp a ⟨g.val, hg⟩
  apply mem_elementarySubgroup_of_pow P g k
  calc
    g ^ P.prime ^ k = g ^ 2 ^ k := congrArg (fun p : ℕ => g ^ p ^ k) hp
    _ = 1 := Subtype.ext (congrArg (fun x : rootSubgroup P a => (x : SplitGroup P)) hk)

/-- Neither elementary restriction nor the actual central quotient loses any
fixed root-subgroup element in characteristic two. -/
def descendedRootEquiv (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (rootSubgroup P a).comap (fixedSubgroup P).subtype ≃*
      descendSubgroup P (rootSubgroup P a) :=
  (Subgroup.subgroupOfEquivOfLe (fixedRootSubgroup_le_elementary P hp a)).symm.trans
    (((rootSubgroup P a).comap (elementaryInclusion P)).equivMapOfInjective
      (toCarrier P) (ElementaryCentralKernel.toCarrier_injective P hp))

@[simp] theorem descendedRootEquiv_val (P : Parameters) (hp : P.prime = 2) (a : Node)
    (g : (rootSubgroup P a).comap (fixedSubgroup P).subtype) :
    (descendedRootEquiv P hp a g).val =
      toCarrier P ⟨g.val, fixedRootSubgroup_le_elementary P hp a g.property⟩ := rfl

/-- The descended root product has the source cardinality; identification with
`radical` additionally requires the parabolic normal-closure calculation. -/
theorem card_descendedRootSubgroup (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Nat.card (descendSubgroup P (rootSubgroup P a)) = P.q ^ fixedDimension a := by
  rw [← Nat.card_congr (descendedRootEquiv P hp a).toEquiv]
  exact card_fixedRootSubgroup P hp a

theorem isPGroup_descendedRootSubgroup (P : Parameters) (hp : P.prime = 2) (a : Node) :
    IsPGroup 2 (descendSubgroup P (rootSubgroup P a)) :=
  ((isPGroup_rootSubgroup P hp a).comap_of_injective (elementaryInclusion P)
    (fun _ _ h => Subtype.ext (Subtype.ext h))).map (toCarrier P)

/-- The source root product gives a subgroup of the original radical candidate. -/
theorem descendedRootSubgroup_le_radical (P : Parameters) (hp : P.prime = 2) (a : Node) :
    descendSubgroup P (rootSubgroup P a) ≤ radical P a :=
  descendSubgroup_mono P (rootSubgroup_le_splitRadical P hp a)


end Triality.Standard.RadicalCoordinates
