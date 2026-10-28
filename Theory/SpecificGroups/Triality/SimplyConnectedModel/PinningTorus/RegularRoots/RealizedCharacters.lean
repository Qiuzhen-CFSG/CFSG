module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalRootRealization

/-!
# Integral characters and cocharacters of the Spin D4 roots

Pairing an ordinary coordinate vector with the four numbered simple coroots
is an injective integral map. Every D4 root has integral simple-coroot
coefficients: the two signed unit entries make its coordinate sum even.
These two facts identify the root characters and construct genuine algebraic
cocharacters in any given coroot-coordinate torus. Their canonical
character--cocharacter pairing recovers the standard D4 pairing on roots and
remains defined on every torus character.

The torus isomorphism is a geometric input; no inverse to the Spin cover and
no root realization are assumed. The base numbering has central vertex 1 and
arms 0, 2, 3. Source: GLS3, 1.9.5(d), Remarks 1.9.6, 1.12.1(e,g), and 1.14.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators

private theorem simpleRoot_exponent (i : Fin 4) :
    evenOrthogonalRootExponent 4 (simpleRoot i) =
      ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, -1]] i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenOrthogonalRootExponent, simpleRoot, typeDSimpleRootIndex,
      Pi.single_apply, Fin.ext_iff, Fin.val_last]

private theorem rootExponent_sum_even (r : RootIndex) :
    (∑ p, evenOrthogonalRootExponent 4 r p) % 2 = 0 := by
  classical
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  simp only [evenOrthogonalRootExponent, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Pi.single_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> norm_num

/-- Pair a coordinate vector with the four numbered simple roots. -/
def simpleCorootPairingMap : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) where
  toFun x i := ∑ p, x p * evenOrthogonalRootExponent 4 (simpleRoot i) p
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [add_mul, Finset.sum_add_distrib]

theorem simpleCorootPairingMap_injective : Function.Injective simpleCorootPairingMap := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  change (∑ p, x p * evenOrthogonalRootExponent 4 (simpleRoot 0) p) =
    ∑ p, y p * evenOrthogonalRootExponent 4 (simpleRoot 0) p at h0
  change (∑ p, x p * evenOrthogonalRootExponent 4 (simpleRoot 1) p) =
    ∑ p, y p * evenOrthogonalRootExponent 4 (simpleRoot 1) p at h1
  change (∑ p, x p * evenOrthogonalRootExponent 4 (simpleRoot 2) p) =
    ∑ p, y p * evenOrthogonalRootExponent 4 (simpleRoot 2) p at h2
  change (∑ p, x p * evenOrthogonalRootExponent 4 (simpleRoot 3) p) =
    ∑ p, y p * evenOrthogonalRootExponent 4 (simpleRoot 3) p at h3
  simp [simpleRoot_exponent, Fin.sum_univ_four] at h0 h1 h2 h3
  have hx0 : x 0 = y 0 := by omega
  have hx1 : x 1 = y 1 := by omega
  have hx2 : x 2 = y 2 := by omega
  have hx3 : x 3 = y 3 := by omega
  funext i
  fin_cases i <;> assumption

theorem rootCorootExponent_injective : Function.Injective rootCorootExponent := by
  intro r s h
  have hexp : evenOrthogonalRootExponent 4 r = evenOrthogonalRootExponent 4 s :=
    simpleCorootPairingMap_injective h
  apply typeDRootEmbedding_injective 4
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : ℤ => (z : ℝ)) (congrFun hexp i)
  rw [evenOrthogonalRootExponent_cast, evenOrthogonalRootExponent_cast] at hi
  exact neg_injective hi

theorem rootCorootExponent_add_iff (r s t : RootIndex) :
    rootCorootExponent t = rootCorootExponent r + rootCorootExponent s ↔
      (evenOrthogonalSeed 2).add r s = some t := by
  constructor
  · intro h
    have hexp : evenOrthogonalRootExponent 4 t =
        evenOrthogonalRootExponent 4 r + evenOrthogonalRootExponent 4 s := by
      apply simpleCorootPairingMap_injective
      rw [map_add]
      exact h
    apply (evenOrthogonalSeed 2).add_eq_some_iff.mpr
    apply Subtype.ext
    funext p
    change typeDRootVector 4 t p = typeDRootVector 4 r p + typeDRootVector 4 s p
    have hc := congrArg (fun z : ℤ => (z : ℝ)) (congrFun hexp p)
    simp only [Pi.add_apply, Int.cast_add, evenOrthogonalRootExponent_cast] at hc
    linarith
  · intro h
    change simpleCorootPairingMap (evenOrthogonalRootExponent 4 t) =
      simpleCorootPairingMap (evenOrthogonalRootExponent 4 r) +
        simpleCorootPairingMap (evenOrthogonalRootExponent 4 s)
    rw [evenOrthogonalRootExponent_add (le_refl 2) _ _ _ h, map_add]

/-- Integral simple-coroot coefficients of a D4 root. -/
def rootCorootCoefficients (r : RootIndex) : Fin 4 → ℤ :=
  let x := evenOrthogonalRootExponent 4 r
  ![-x 0, -x 0 - x 1, (-x 0 - x 1 - x 2 + x 3) / 2,
    (-x 0 - x 1 - x 2 - x 3) / 2]

theorem rootCorootCoefficients_expansion (r : RootIndex) (p : Fin 4) :
    ∑ i, rootCorootCoefficients r i * evenOrthogonalRootExponent 4 (simpleRoot i) p =
      evenOrthogonalRootExponent 4 r p := by
  have heven := rootExponent_sum_even r
  rw [Fin.sum_univ_four] at heven
  simp only [Fin.sum_univ_four, simpleRoot_exponent]
  fin_cases p <;> simp [rootCorootCoefficients] <;> omega

theorem rootCorootCoefficients_simple (i : Fin 4) :
    rootCorootCoefficients (simpleRoot i) = Pi.single i 1 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootCorootCoefficients, evenOrthogonalRootExponent,
      simpleRoot, typeDSimpleRootIndex, Pi.single_apply, Fin.ext_iff, Fin.val_last]

theorem rootCorootCoefficients_pairing (r s : RootIndex) :
    ∑ i, rootCorootCoefficients s i * rootCorootExponent r i =
      evenOrthogonalRootPairingInt 2 r s := by
  have he : (∑ i, rootCorootCoefficients s i * rootCorootExponent r i) =
      ∑ p, evenOrthogonalRootExponent 4 r p * evenOrthogonalRootExponent 4 s p := by
    simp_rw [rootCorootExponent, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← rootCorootCoefficients_expansion s p, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  apply Int.cast_injective (α := ℝ)
  rw [evenOrthogonalRootPairingInt_cast, typeDRootPairing_pairing]
  push_cast
  simp_rw [evenOrthogonalRootExponent_cast]
  simp only [neg_mul_neg, typeDRootEmbedding, dot]
  apply Finset.sum_congr rfl
  intro i _
  ring

universe u
variable (k : Type u) [Field k] [IsAlgClosed k]
local instance realizedCharactersTorusAlgebraicGroup (T : ClosedSubgroup (groupVariety k)) : AlgebraicGroup T.carrierVariety :=
  T.carrierAlgebraicGroup

/-- Additive Laurent-character transport into the geometric coroot torus. -/
def corootCharacterMap (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    (Fin 4 → ℤ) →+ Additive (TorusWeight T) :=
  (TorusCharacter.pullback e.inv).toAdditive.comp
    (dLaurentCharacterAddEquiv (k := k) 4).toAddMonoidHom

/-- Pullback along the inverse torus isomorphism preserves distinct Laurent characters. -/
theorem corootCharacterMap_injective (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    Function.Injective (corootCharacterMap k T e) := by
  intro z w h
  apply (dLaurentCharacterAddEquiv (k := k) 4).injective
  apply Additive.toMul.injective
  apply Morphism.ext
  funext t
  have ht := congrArg (fun χ : Additive (TorusWeight T) =>
    χ.toMul.onPoints (e.hom.onPoints t)) h
  change (dLaurentCharacter 4 z).onPoints (e.inv.onPoints (e.hom.onPoints t)) =
    (dLaurentCharacter 4 w).onPoints (e.inv.onPoints (e.hom.onPoints t)) at ht
  rwa [e.hom_inv_id] at ht

theorem coordinateRootWeight_injective (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    Function.Injective (coordinateRootWeight k T e) := by
  intro r s h
  apply rootCorootExponent_injective
  apply corootCharacterMap_injective k T e
  exact congrArg Additive.ofMul h

/-- The cocharacter with a root's integral simple-coroot coefficients. -/
def coordinateRootCocharacter (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) (r : RootIndex) :
    ClosedSubgroupTorusCocharacter T :=
  e.hom.comp (dCharacterTupleMorphism 4 1 (fun i _ => rootCorootCoefficients r i))

theorem coordinateRootCocharacter_pairing (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) (r s : RootIndex) :
    characterCocharacterPairing T (coordinateRootCocharacter k T e s)
      (Additive.ofMul (coordinateRootWeight k T e r)) =
        evenOrthogonalRootPairingInt 2 r s := by
  apply (weightCocharacterEquation_existsUnique T (coordinateRootWeight k T e r)
    (coordinateRootCocharacter k T e s)).unique
  · exact characterCocharacterPairing_spec _ _ _
  · intro t
    change (coordinateRootWeight k T e r).pointCharacter
      (e.hom.onPoints ((dCharacterTupleMorphism 4 1
        (fun i _ => rootCorootCoefficients s i)).onPoints t)) = _
    rw [coordinateRootWeight_apply]
    rw [← rootCorootCoefficients_pairing r s]
    have hu : (∏ i, (dPointEquiv 4 ((dCharacterTupleMorphism (k := k) 4 1
          (fun j _ => rootCorootCoefficients s j)).onPoints t) i) ^ rootCorootExponent r i) =
        (dPointEquiv 1 t 0) ^ ∑ i, rootCorootCoefficients s i * rootCorootExponent r i := by
      simp_rw [dCharacterTupleMorphism_apply (k := k)]
      rw [prod_laurentMonomial_zpow]
      simp only [Fin.prod_univ_one, mul_comm]
    exact_mod_cast hu
end Triality.SimplyConnected.Pinning
