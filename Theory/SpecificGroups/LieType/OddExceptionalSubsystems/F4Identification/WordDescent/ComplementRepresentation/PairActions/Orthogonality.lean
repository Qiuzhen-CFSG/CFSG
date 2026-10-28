module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Commuting disconnected pairs in the F4 cover and the E6 complement

For the three disconnected pairs, the signed source curves commute by their
zero Cartan entries. In the folded E6 action, the same assertion follows from
the explicit reversed orbit labels: node 0 is node 3, node 1 is node 2, node 2
is the pair (1,4), and node 3 is the pair (0,5). Free-word induction extends
these identities to the two rank-one subgroups and their marked actions.

Multiplication gives a homomorphism from the product of the source subgroups.
If their intersection is trivial, it is faithful; the product of the two
commuting linear actions then descends to the literal two-node subgroup via
`pairActionOfFaithfulModel`. Trivial intersection is an explicit source
obligation here, not a consequence of commutation. No characteristic or
irreducibility assumption is used in the commutation proof.

Source: GLS3 §§2.4, 2.6, especially the common-lattice construction in 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`), used for the inclusions in Aschbacher--Smith
A.2.17, printed p.39. `PairActions` consumes this disconnected construction.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent Theory.AlgebraicGroup.StandardRootSystem
local instance : Fintype typeF4Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

def DisconnectedPair (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3)

private theorem simpleRoot_commute_signed (i j : Fin 6)
    (hij : i ≠ j) (hc : typeE6CartanMatrix j i = 0) (s z : Bool) (t u : F) :
    Commute (simpleRoot F s i t) (simpleRoot F z j u) := by
  cases s <;> cases z
  · exact simpleRoot_commute F false i j hij hc t u
  · exact (simpleRoot_opposite_commute F j i hij.symm u t).symm
  · exact simpleRoot_opposite_commute F i j hij t u
  · exact simpleRoot_commute F true i j hij hc t u

theorem disconnected_f4Simple_commute {i j : Fin 4} (h : DisconnectedPair i j)
    (s z : Bool) (t u : F) : Commute (f4Simple F s i t) (f4Simple F z j u) := by
  have H (a b : Fin 6) (hne : a ≠ b) (hc : typeE6CartanMatrix b a = 0) :=
    simpleRoot_commute_signed F a b hne hc s z t u
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    apply Subtype.ext
    change Commute (foldedSimple F s _ t) (foldedSimple F z _ u)
  · change Commute (simpleRoot F s 3 t) (simpleRoot F z 1 u * simpleRoot F z 4 u)
    exact (H 3 1 (by decide) (by decide)).mul_right (H 3 4 (by decide) (by decide))
  · change Commute (simpleRoot F s 3 t) (simpleRoot F z 0 u * simpleRoot F z 5 u)
    exact (H 3 0 (by decide) (by decide)).mul_right (H 3 5 (by decide) (by decide))
  · change Commute (simpleRoot F s 2 t) (simpleRoot F z 0 u * simpleRoot F z 5 u)
    exact (H 2 0 (by decide) (by decide)).mul_right (H 2 5 (by decide) (by decide))

theorem disconnected_complement_commute {i j : Fin 4} (h : DisconnectedPair i j)
    (s z : Bool) (t u : F) :
    Commute (eigenspaceAction F (-1) (f4Simple F s i t))
      (eigenspaceAction F (-1) (f4Simple F z j u)) :=
  (disconnected_f4Simple_commute F h s z t u).map (eigenspaceAction F (-1))

private theorem coverSimple_commute_signed (i j : Fin 4)
    (hij : i ≠ j) (hc : typeF4CartanMatrix j i = 0) (s z : Bool) (t u : F) :
    Commute (coverSimple F s i t) (coverSimple F z j u) := by
  have hn : sourceIndex i ≠ sourceIndex j := fun h => hij (typeF4RootPairing_baseEquiv.injective h)
  have hz : typeF4RootPairing_base.cartanMatrix (sourceIndex j) (sourceIndex i) = 0 :=
    (typeF4RootPairing_base_cartan_apply j i).trans hc
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coverSimple_val]
  cases s <;> cases z
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero
        (sourceIndex i) (sourceIndex j) hn hz t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative
        (sourceIndex j) (sourceIndex i) hn.symm u t).symm.eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative
        (sourceIndex i) (sourceIndex j) hn t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero
        (sourceIndex i) (sourceIndex j) hn hz t u).eq

theorem disconnected_coverSimple_commute {i j : Fin 4} (h : DisconnectedPair i j)
    (s z : Bool) (t u : F) : Commute (coverSimple F s i t) (coverSimple F z j u) := by
  apply coverSimple_commute_signed F i j _ _ s z t u
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem commute_pair_homs {G : Type*} [Group G] {i j a b : Fin 4}
    (ρ : pairSubgroup F i j →* G) (τ : pairSubgroup F a b →* G)
    (h : ∀ s k t z l u,
      Commute (ρ (pairGenerator F i j s k t)) (τ (pairGenerator F a b z l u)))
    (x : pairSubgroup F i j) (y : pairSubgroup F a b) : Commute (ρ x) (τ y) := by
  obtain ⟨v, rfl⟩ := pairEvaluationRange_surjective F i j x
  obtain ⟨w, rfl⟩ := pairEvaluationRange_surjective F a b y
  let f := ρ.comp (pairEvaluationRange F i j)
  let g := τ.comp (pairEvaluationRange F a b)
  change Commute (f v) (g w)
  induction v using FreeGroup.induction_on with
  | C1 => simp only [map_one]; exact Commute.one_left _
  | of c =>
    induction w using FreeGroup.induction_on with
    | C1 => simp only [map_one]; exact Commute.one_right _
    | of d => exact h c.1 c.2.1 c.2.2 d.1 d.2.1 d.2.2
    | inv_of d hd => simpa only [map_inv] using hd.inv_right
    | mul v w hv hw => simpa only [map_mul] using hv.mul_right hw
  | inv_of c hc => simpa only [map_inv] using hc.inv_left
  | mul v w hv hw => simpa only [map_mul] using hv.mul_left hw

theorem disconnected_rankOne_commute {i j : Fin 4} (h : DisconnectedPair i j)
    (x : pairSubgroup F i i) (y : pairSubgroup F j j) :
    Commute (x : Cover F) (y : Cover F) := by
  apply commute_pair_homs F (pairSubgroup F i i).subtype (pairSubgroup F j j).subtype _ x y
  intro s k t z l u
  simpa only [Subgroup.subtype_apply, pairGenerator_val, pairNode, ite_self] using
    disconnected_coverSimple_commute F h s z t u

theorem disconnected_rankOne_actions_commute {i j : Fin 4} (h : DisconnectedPair i j)
    (ρ : PairAction F i i) (τ : PairAction F j j)
    (x : pairSubgroup F i i) (y : pairSubgroup F j j) : Commute (ρ.hom x) (τ.hom y) := by
  apply commute_pair_homs F ρ.hom τ.hom _ x y
  intro s k t z l u
  simpa only [ρ.map_generator, τ.map_generator, pairNode, ite_self] using
    disconnected_complement_commute F h s z t u

/-- Multiplication of the two literal commuting rank-one subgroups in the cover. -/
def disconnectedProduct {i j : Fin 4} (h : DisconnectedPair i j) :
    pairSubgroup F i i × pairSubgroup F j j →* Cover F :=
  (pairSubgroup F i i).subtype.noncommCoprod (pairSubgroup F j j).subtype
    (disconnected_rankOne_commute F h)

theorem disconnectedProduct_injective {i j : Fin 4} (h : DisconnectedPair i j)
    (hd : Disjoint (pairSubgroup F i i) (pairSubgroup F j j)) :
    Function.Injective (disconnectedProduct F h) := by
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  exact ⟨Subtype.val_injective, Subtype.val_injective, by
    simpa only [Subgroup.range_subtype] using hd⟩

/-- The disconnected action from its two rank-one actions and the concrete
trivial-intersection assertion in the source cover. -/
def disconnectedPairActionOfDisjoint {i j : Fin 4} (h : DisconnectedPair i j)
    (hd : Disjoint (pairSubgroup F i i) (pairSubgroup F j j))
    (ρ : PairAction F i i) (τ : PairAction F j j) : PairAction F i j := by
  let x (s k : Bool) (t : F) : pairSubgroup F i i × pairSubgroup F j j :=
    if k then (pairGenerator F i i s true t, 1) else (1, pairGenerator F j j s false t)
  exact pairActionOfFaithfulModel F i j (disconnectedProduct F h)
    (disconnectedProduct_injective F h hd) x
    (by
      intro s k t
      cases k
      · change 1 * (pairGenerator F j j s false t).val = coverSimple F s j t
        simp [pairNode]
      · change (pairGenerator F i i s true t).val * 1 = coverSimple F s i t
        simp [pairNode])
    (ρ.hom.noncommCoprod τ.hom (disconnected_rankOne_actions_commute F h ρ τ))
    (by
      intro s k t
      cases k <;> simp [x, ρ.map_generator, τ.map_generator, pairNode])

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
