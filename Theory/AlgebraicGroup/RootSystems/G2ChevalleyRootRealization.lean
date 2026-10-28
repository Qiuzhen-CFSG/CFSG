module

public import Theory.AlgebraicGroup.RootData.FiniteReflectionSeed
public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyTorusRootSupport
public import Theory.AlgebraicGroup.RootSystems.G2RootPairing

/-!
# The G2 Chevalley root realization

This file identifies the twelve explicit Chevalley curves with the standard
G2 roots and checks the full root-group realization contract in every
characteristic.  Exhaustiveness uses the split-torus root-support theorem for
the closed Chevalley carrier, while the subgroup packages come from the
integral root curves.

The proof transports explicit integral character and cocharacter exponent
tables through the carrier's split-torus isomorphism.  The resulting Laurent
monomial calculation gives the standard G2 Cartan pairing, and the finite
twelve-root coordinate identification transports opposites, additions,
reflections, positivity, simple roots, and heights from the standard based
pairing.  Thus no characteristic-dependent division is used.  The construction
follows the standard G2 coordinates established in `G2RootPairing` and the
integral Chevalley representation developed in the preceding carrier modules.
-/

set_option maxHeartbeats 2000000

open scoped BigOperators
open Set

namespace Theory.AlgebraicGroup.G2Chevalley

open StandardRootSystem

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable local instance splitTorusAlgebraicGroup :
    AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

public section

noncomputable section

local instance : typeG2RootPairing.IsRootSystem :=
  typeG2RootPairing_isRootSystem

local instance : typeG2RootPairing.IsReduced :=
  typeG2RootPairing_isReduced

/-- The coordinate vector of a root in the explicit Chevalley enumeration. -/
@[expose] public noncomputable def standardRootVector (r : Root) : Vec 2 :=
  ![(r.coord.1 : ℝ), (r.coord.2 : ℝ)]

private lemma standardRootVector_mem (r : Root) :
    standardRootVector r ∈ typeG2Roots typeG2Long typeG2Short := by
  fin_cases r <;>
    simp [standardRootVector, Root.coord, typeG2Roots, typeG2Long, typeG2Short]

private noncomputable def standardRootIndexMap (r : Root) : typeG2Root :=
  ⟨standardRootVector r, standardRootVector_mem r⟩

private lemma standardRootIndexMap_injective :
    Function.Injective standardRootIndexMap := by
  intro r s hrs
  have hv := congrArg Subtype.val hrs
  fin_cases r <;> fin_cases s <;>
    simp [standardRootIndexMap, standardRootVector, Root.coord] at hv ⊢ <;>
    norm_num at hv

private lemma standardRootIndexMap_surjective :
    Function.Surjective standardRootIndexMap := by
  rintro ⟨v, hv⟩
  simp only [typeG2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv
  all_goals subst v
  · exact ⟨(1 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(7 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(0 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(6 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(2 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(8 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(3 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(9 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(4 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(10 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(5 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩
  · exact ⟨(11 : Root), by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        norm_num [standardRootIndexMap, standardRootVector, Root.coord,
          typeG2Long, typeG2Short]⟩

/-- The explicit Chevalley enumeration identified with the standard G2 roots. -/
public noncomputable def rootIndexEquiv : Root ≃ typeG2Root :=
  Equiv.ofBijective standardRootIndexMap
    ⟨standardRootIndexMap_injective, standardRootIndexMap_surjective⟩

private lemma rootIndexEquiv_apply (r : Root) :
    rootIndexEquiv r = standardRootIndexMap r := rfl

@[simp] public lemma rootIndexEquiv_val (r : Root) :
    (rootIndexEquiv r : Vec 2) = standardRootVector r := by
  exact congrArg Subtype.val (rootIndexEquiv_apply r)

@[simp] private lemma rootIndexEquiv_symm_vector (r : typeG2Root) :
    standardRootVector (rootIndexEquiv.symm r) = (r : Vec 2) := by
  calc
    standardRootVector (rootIndexEquiv.symm r) =
        (rootIndexEquiv (rootIndexEquiv.symm r) : Vec 2) :=
      (rootIndexEquiv_val _).symm
    _ = (r : Vec 2) := congrArg Subtype.val (rootIndexEquiv.apply_symm_apply r)

/-- Root indices for the G2 carrier, lifted to the field's universe. -/
public abbrev RootIndex := ULift.{u, 0} typeG2Root

private noncomputable def rootPairingInt (r s : typeG2Root) : ℤ :=
  Classical.choose (typeG2RootPairing_pairing_eq_intCast r s)

private lemma rootPairingInt_cast (r s : typeG2Root) :
    (rootPairingInt r s : ℝ) = typeG2RootPairing.pairing r s :=
  Classical.choose_spec (typeG2RootPairing_pairing_eq_intCast r s)

private noncomputable def rootSeed :
    FiniteReflectionSeed typeG2Root ℝ (Vec 2) (Vec 2) where
  pairing := typeG2RootPairing.toLinearMap
  pairing_isPerfPair := typeG2RootPairing.isPerfPair_toLinearMap
  root := typeG2RootPairing.root
  coroot := typeG2RootPairing.coroot
  cartan := rootPairingInt
  pairing_eq_cartan := by
    intro r s
    exact (rootPairingInt_cast r s).symm
  cartan_self := by
    intro r
    have h : (rootPairingInt r r : ℝ) = (2 : ℝ) := by
      rw [rootPairingInt_cast]
      exact typeG2RootPairing.pairing_same r
    exact_mod_cast h
  reflectionPerm := typeG2RootPairing.reflectionPerm
  reflection_root := by
    intro r s
    rw [rootPairingInt_cast]
    exact typeG2RootPairing.reflectionPerm_root r s
  reflection_coroot := by
    intro r s
    rw [rootPairingInt_cast]
    exact typeG2RootPairing.reflectionPerm_coroot r s
  span_root := RootPairing.IsRootSystem.span_root_eq_top
  span_coroot := RootPairing.IsRootSystem.span_coroot_eq_top
  reduced_scalar_multiple := RootPairing.IsReduced.eq_or_eq_neg

private def rootCorootExponent : Root → Fin 2 → ℤ
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![1, 3]
  | 3 => ![2, 3]
  | 4 => ![1, 1]
  | 5 => ![1, 2]
  | 6 => ![-1, 0]
  | 7 => ![0, -1]
  | 8 => ![-1, -3]
  | 9 => ![-2, -3]
  | 10 => ![-1, -1]
  | 11 => ![-1, -2]

private def rootWeightExponentTable : Root → Fin 2 → ℤ
  | 0 => ![2, -1]
  | 1 => ![-3, 2]
  | 2 => ![-1, 1]
  | 3 => ![1, 0]
  | 4 => ![3, -1]
  | 5 => ![0, 1]
  | 6 => ![-2, 1]
  | 7 => ![3, -2]
  | 8 => ![1, -1]
  | 9 => ![-1, 0]
  | 10 => ![-3, 1]
  | 11 => ![0, -1]

private lemma rootWeightExponent_eq_table (r : Root) :
    rootWeightExponent r = rootWeightExponentTable r := by
  rcases rootWeightExponent_values with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  fin_cases r <;> simp only [rootWeightExponentTable]
  all_goals assumption

private noncomputable def rootCocharacter (r : RootIndex.{u}) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter (splitTorus (k := k)) :=
  splitTorusCocharacter (k := k)
    (rootCorootExponent (rootIndexEquiv.symm r.down))

private lemma rootWeight_cocharacter_pairing (r s : typeG2Root) :
    characterCocharacterPairing (splitTorus (k := k))
        (splitTorusCocharacter (k := k)
          (rootCorootExponent (rootIndexEquiv.symm s)))
        (Additive.ofMul (rootWeight (k := k) (rootIndexEquiv.symm r))) =
      ∑ i, rootWeightExponent (rootIndexEquiv.symm r) i *
        rootCorootExponent (rootIndexEquiv.symm s) i := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  apply (weightCocharacterEquation_existsUnique
    (splitTorus (k := k))
    (rootWeight (k := k) (rootIndexEquiv.symm r))
    (splitTorusCocharacter (k := k)
      (rootCorootExponent (rootIndexEquiv.symm s)))).unique
  · exact characterCocharacterPairing_spec _ _ _
  · intro t
    have hweight := congrArg
      (fun chi : TorusCharacter (dVariety k 2) =>
        chi.pointCharacter
          ((splitTorusIso (k := k)).inv.onPoints
            ((splitTorusCocharacter (k := k)
              (rootCorootExponent (rootIndexEquiv.symm s))).onPoints t)))
      (rootWeight_comp_splitTorusIso (k := k) (rootIndexEquiv.symm r))
    have hweight' :
        (rootWeight (k := k) (rootIndexEquiv.symm r)).pointCharacter
            ((splitTorusCocharacter (k := k)
              (rootCorootExponent (rootIndexEquiv.symm s))).onPoints t) =
          (dLaurentCharacter (k := k) 2
            (rootWeightExponent (rootIndexEquiv.symm r))).pointCharacter
              ((splitTorusIso (k := k)).inv.onPoints
                ((splitTorusCocharacter (k := k)
                  (rootCorootExponent (rootIndexEquiv.symm s))).onPoints t)) := by
      change (rootWeight (k := k) (rootIndexEquiv.symm r)).pointCharacter
          ((splitTorusIso (k := k)).hom.onPoints
            ((splitTorusIso (k := k)).inv.onPoints
              ((splitTorusCocharacter (k := k)
                (rootCorootExponent (rootIndexEquiv.symm s))).onPoints t))) = _ at hweight
      simpa only [(splitTorusIso (k := k)).inv_hom_id] using hweight
    change (rootWeight (k := k) (rootIndexEquiv.symm r)).pointCharacter
        ((splitTorusCocharacter (k := k)
          (rootCorootExponent (rootIndexEquiv.symm s))).onPoints t) = _
    rw [hweight', splitTorusCocharacter_inverse_apply,
      TorusCharacter.pointCharacter_dLaurentCharacter]
    change (↑(∏ i,
      (dPointEquiv 2
        ((dCharacterTupleMorphism (k := k) 2 1
          (fun i _ => rootCorootExponent (rootIndexEquiv.symm s) i)).onPoints t) i) ^
            rootWeightExponent (rootIndexEquiv.symm r) i) : k) = _
    simp_rw [dCharacterTupleMorphism_apply (k := k)]
    rw [prod_laurentMonomial_zpow]
    simp

private lemma rootExponent_corootExponent_pairing (r s : Root) :
    (((∑ i, rootWeightExponent r i * rootCorootExponent s i : ℤ) : ℝ)) =
      dot (standardRootVector r) (typeG2CorootVector (rootIndexEquiv s)) := by
  rw [rootWeightExponent_eq_table]
  fin_cases r <;> fin_cases s <;>
    simp [rootWeightExponentTable, rootCorootExponent,
      standardRootVector, Root.coord, rootIndexEquiv_val,
      typeG2CorootVector, typeG2LongRootSet, typeG2Long, typeG2Short,
      dot, Fin.sum_univ_succ] <;> norm_num

private lemma rootWeight_cocharacter_pairing_cast (r s : typeG2Root) :
    (((characterCocharacterPairing (splitTorus (k := k))
      (splitTorusCocharacter (k := k)
        (rootCorootExponent (rootIndexEquiv.symm s)))
      (Additive.ofMul (rootWeight (k := k) (rootIndexEquiv.symm r)))) : ℤ) : ℝ) =
        typeG2RootPairing.pairing r s := by
  rw [show (((characterCocharacterPairing (splitTorus (k := k))
      (splitTorusCocharacter (k := k)
        (rootCorootExponent (rootIndexEquiv.symm s)))
      (Additive.ofMul (rootWeight (k := k) (rootIndexEquiv.symm r)))) : ℤ) : ℝ) =
        ((∑ i, rootWeightExponent (rootIndexEquiv.symm r) i *
          rootCorootExponent (rootIndexEquiv.symm s) i : ℤ) : ℝ) by
    rw [rootWeight_cocharacter_pairing (k := k) r s]]
  rw [typeG2RootPairing_pairing]
  simpa using rootExponent_corootExponent_pairing
    (rootIndexEquiv.symm r) (rootIndexEquiv.symm s)

private noncomputable def rootExponentReal (r : typeG2Root) : Fin 2 → ℝ :=
  ![2 * (r : Vec 2) 0 - 3 * (r : Vec 2) 1,
    -(r : Vec 2) 0 + 2 * (r : Vec 2) 1]

private lemma rootWeightExponent_cast (r : typeG2Root) (i : Fin 2) :
    ((rootWeightExponent (rootIndexEquiv.symm r) i : ℤ) : ℝ) =
      rootExponentReal r i := by
  rw [← rootIndexEquiv.apply_symm_apply r]
  generalize rootIndexEquiv.symm r = q
  rw [rootWeightExponent_eq_table]
  fin_cases q <;> fin_cases i <;>
    simp [rootWeightExponentTable, rootExponentReal,
      rootIndexEquiv_val, standardRootVector, Root.coord] <;> norm_num

private lemma rootWeightExponent_neg (r : typeG2Root) :
    rootWeightExponent (rootIndexEquiv.symm (rootSeed.neg r)) =
      -rootWeightExponent (rootIndexEquiv.symm r) := by
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.neg_apply]
  push_cast
  rw [rootWeightExponent_cast, rootWeightExponent_cast]
  have hv := rootSeed.root_neg r
  change ((rootSeed.neg r : typeG2Root) : Vec 2) = -(r : Vec 2) at hv
  have h0 := congrFun hv (0 : Fin 2)
  have h1 := congrFun hv (1 : Fin 2)
  fin_cases i <;>
    simp [rootExponentReal] at h0 h1 ⊢ <;> linarith

private lemma rootWeightExponent_add {r s t : typeG2Root}
    (h : rootSeed.add r s = some t) :
    rootWeightExponent (rootIndexEquiv.symm t) =
      rootWeightExponent (rootIndexEquiv.symm r) +
        rootWeightExponent (rootIndexEquiv.symm s) := by
  have hv := rootSeed.add_eq_some_iff.mp h
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.add_apply]
  push_cast
  rw [rootWeightExponent_cast, rootWeightExponent_cast,
    rootWeightExponent_cast]
  change (t : Vec 2) = (r : Vec 2) + (s : Vec 2) at hv
  have h0 := congrFun hv (0 : Fin 2)
  have h1 := congrFun hv (1 : Fin 2)
  fin_cases i <;>
    simp [rootExponentReal] at h0 h1 ⊢ <;> linarith

private lemma rootWeightExponent_reflect (r s : typeG2Root) :
    rootWeightExponent
        (rootIndexEquiv.symm (rootSeed.reflectionPerm r s)) =
      rootWeightExponent (rootIndexEquiv.symm s) -
        rootPairingInt s r • rootWeightExponent (rootIndexEquiv.symm r) := by
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [rootWeightExponent_cast, rootWeightExponent_cast,
    rootWeightExponent_cast]
  have hv := rootSeed.reflection_root r s
  change (s : Vec 2) - (rootPairingInt s r : ℝ) • (r : Vec 2) =
    ((rootSeed.reflectionPerm r s : typeG2Root) : Vec 2) at hv
  have h0 := congrFun hv (0 : Fin 2)
  have h1 := congrFun hv (1 : Fin 2)
  fin_cases i <;>
    simp [rootExponentReal] at h0 h1 ⊢ <;> linarith

private lemma splitTorusWeight_ext
    {chi psi : TorusWeight (splitTorus (k := k))}
    (h : chi.comp (splitTorusIso (k := k)).hom =
      psi.comp (splitTorusIso (k := k)).hom) : chi = psi := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  change chi.onPoints x = psi.onPoints x
  have hx := congrArg
    (fun eta : TorusCharacter (dVariety k 2) =>
      eta.onPoints ((splitTorusIso (k := k)).inv.onPoints x)) h
  change chi.onPoints ((splitTorusIso (k := k)).hom.onPoints
      ((splitTorusIso (k := k)).inv.onPoints x)) =
    psi.onPoints ((splitTorusIso (k := k)).hom.onPoints
      ((splitTorusIso (k := k)).inv.onPoints x)) at hx
  simpa only [(splitTorusIso (k := k)).inv_hom_id] using hx

private lemma rootWeight_neg (r : RootIndex.{u}) :
    rootWeight (k := k) (rootIndexEquiv.symm (rootSeed.neg r.down)) =
      (rootWeight (k := k) (rootIndexEquiv.symm r.down))⁻¹ := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  apply splitTorusWeight_ext (k := k)
  change (TorusCharacter.pullback (splitTorusIso (k := k)).hom)
      (rootWeight (k := k) (rootIndexEquiv.symm (rootSeed.neg r.down))) =
    (TorusCharacter.pullback (splitTorusIso (k := k)).hom)
      ((rootWeight (k := k) (rootIndexEquiv.symm r.down))⁻¹)
  rw [map_inv]
  change (rootWeight (k := k)
      (rootIndexEquiv.symm (rootSeed.neg r.down))).comp
        (splitTorusIso (k := k)).hom =
    ((rootWeight (k := k) (rootIndexEquiv.symm r.down)).comp
        (splitTorusIso (k := k)).hom)⁻¹
  rw [rootWeight_comp_splitTorusIso,
    rootWeight_comp_splitTorusIso]
  apply Additive.ofMul.injective
  change (dLaurentCharacterAddEquiv (k := k) 2)
      (rootWeightExponent (rootIndexEquiv.symm (rootSeed.neg r.down))) =
    -((dLaurentCharacterAddEquiv (k := k) 2)
      (rootWeightExponent (rootIndexEquiv.symm r.down)))
  rw [rootWeightExponent_neg, map_neg]

private lemma rootWeight_add (r s t : RootIndex.{u})
    (h : rootSeed.add r.down s.down = some t.down) :
    rootWeight (k := k) (rootIndexEquiv.symm t.down) =
      rootWeight (k := k) (rootIndexEquiv.symm r.down) *
        rootWeight (k := k) (rootIndexEquiv.symm s.down) := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  apply splitTorusWeight_ext (k := k)
  change (TorusCharacter.pullback (splitTorusIso (k := k)).hom)
      (rootWeight (k := k) (rootIndexEquiv.symm t.down)) =
    (TorusCharacter.pullback (splitTorusIso (k := k)).hom)
      (rootWeight (k := k) (rootIndexEquiv.symm r.down) *
        rootWeight (k := k) (rootIndexEquiv.symm s.down))
  rw [map_mul]
  change (rootWeight (k := k) (rootIndexEquiv.symm t.down)).comp
      (splitTorusIso (k := k)).hom =
    (rootWeight (k := k) (rootIndexEquiv.symm r.down)).comp
        (splitTorusIso (k := k)).hom *
      (rootWeight (k := k) (rootIndexEquiv.symm s.down)).comp
        (splitTorusIso (k := k)).hom
  rw [rootWeight_comp_splitTorusIso,
    rootWeight_comp_splitTorusIso, rootWeight_comp_splitTorusIso]
  apply Additive.ofMul.injective
  change (dLaurentCharacterAddEquiv (k := k) 2)
      (rootWeightExponent (rootIndexEquiv.symm t.down)) =
    (dLaurentCharacterAddEquiv (k := k) 2)
      (rootWeightExponent (rootIndexEquiv.symm r.down)) +
      (dLaurentCharacterAddEquiv (k := k) 2)
        (rootWeightExponent (rootIndexEquiv.symm s.down))
  rw [rootWeightExponent_add h, map_add]

private lemma rootWeight_reflect (r s : RootIndex.{u}) :
    rootWeight (k := k)
        (rootIndexEquiv.symm (rootSeed.reflectionPerm r.down s.down)) =
      rootWeight (k := k) (rootIndexEquiv.symm s.down) *
        rootWeight (k := k) (rootIndexEquiv.symm r.down) ^
          (-rootPairingInt s.down r.down) := by
  let _ := (splitTorus (k := k)).carrierAlgebraicGroup
  apply splitTorusWeight_ext (k := k)
  change (TorusCharacter.pullback (splitTorusIso (k := k)).hom)
      (rootWeight (k := k)
        (rootIndexEquiv.symm (rootSeed.reflectionPerm r.down s.down))) =
    (TorusCharacter.pullback (splitTorusIso (k := k)).hom)
      (rootWeight (k := k) (rootIndexEquiv.symm s.down) *
        rootWeight (k := k) (rootIndexEquiv.symm r.down) ^
          (-rootPairingInt s.down r.down))
  rw [map_mul, map_zpow]
  change (rootWeight (k := k)
      (rootIndexEquiv.symm (rootSeed.reflectionPerm r.down s.down))).comp
        (splitTorusIso (k := k)).hom =
    (rootWeight (k := k) (rootIndexEquiv.symm s.down)).comp
        (splitTorusIso (k := k)).hom *
      (rootWeight (k := k) (rootIndexEquiv.symm r.down)).comp
          (splitTorusIso (k := k)).hom ^
        (-rootPairingInt s.down r.down)
  rw [rootWeight_comp_splitTorusIso,
    rootWeight_comp_splitTorusIso, rootWeight_comp_splitTorusIso]
  apply Additive.ofMul.injective
  change (dLaurentCharacterAddEquiv (k := k) 2)
      (rootWeightExponent
        (rootIndexEquiv.symm (rootSeed.reflectionPerm r.down s.down))) =
    (dLaurentCharacterAddEquiv (k := k) 2)
      (rootWeightExponent (rootIndexEquiv.symm s.down)) +
      (-rootPairingInt s.down r.down) •
        (dLaurentCharacterAddEquiv (k := k) 2)
          (rootWeightExponent (rootIndexEquiv.symm r.down))
  rw [rootWeightExponent_reflect, map_sub, map_zsmul]
  simp [sub_eq_add_neg, neg_smul]

private lemma rootWeightExponent_injective :
    Function.Injective rootWeightExponent := by
  intro r s hrs
  rw [rootWeightExponent_eq_table, rootWeightExponent_eq_table] at hrs
  fin_cases r <;> fin_cases s <;>
    simp [rootWeightExponentTable,
      funext_iff, Fin.forall_fin_two] at hrs ⊢

private lemma rootData_rootWeight_injective : Function.Injective
    (fun r : RootIndex.{u} =>
      rootWeight (k := k) (rootIndexEquiv.symm r.down)) := by
  intro r s hrs
  apply ULift.ext
  apply rootIndexEquiv.symm.injective
  apply rootWeightExponent_injective
  apply dLaurentCharacter_injective (k := k) 2
  have h := congrArg
    (fun chi : TorusWeight (splitTorus (k := k)) =>
      chi.comp (splitTorusIso (k := k)).hom) hrs
  simpa only [rootWeight_comp_splitTorusIso] using h

private lemma rootData_add_eq_some_iff (r s t : RootIndex.{u}) :
    Option.map ULift.up (rootSeed.add r.down s.down) = some t ↔
      rootSeed.add r.down s.down = some t.down := by
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    refine ⟨t.down, h, ?_⟩
    apply ULift.ext
    rfl

private lemma mem_standardBase_iff (r : typeG2Root) :
    r ∈ typeG2RootPairing_base.support ↔
      typeG2RootPairing_base.IsPos r ∧
        ∀ s t, rootSeed.add s t = some r →
          ¬(typeG2RootPairing_base.IsPos s ∧
            typeG2RootPairing_base.IsPos t) := by
  constructor
  · intro hr
    refine ⟨typeG2RootPairing_base.isPos_of_mem_support hr, ?_⟩
    intro s t hadd ⟨hs, ht⟩
    have hHeight := typeG2RootPairing_base.height_add
      (rootSeed.add_eq_some_iff.mp hadd)
    have hrHeight := typeG2RootPairing_base.height_one_of_mem_support hr
    rw [typeG2RootPairing_base.isPos_iff] at hs ht
    linarith
  · rintro ⟨hr, hindecomp⟩
    suffices r ∈ typeG2RootPairing_base.support ∨
        ∃ s t, typeG2RootPairing_base.IsPos s ∧
          typeG2RootPairing_base.IsPos t ∧
          typeG2RootPairing.root r =
            typeG2RootPairing.root s + typeG2RootPairing.root t by
      rcases this with hrBase | ⟨s, t, hs, ht, hst⟩
      · exact hrBase
      · exact False.elim <| hindecomp s t
          (rootSeed.add_eq_some_iff.mpr hst) ⟨hs, ht⟩
    let p : typeG2Root → Prop := fun q =>
      typeG2RootPairing_base.IsPos q →
        q ∈ typeG2RootPairing_base.support ∨
          ∃ s t, typeG2RootPairing_base.IsPos s ∧
            typeG2RootPairing_base.IsPos t ∧
            typeG2RootPairing.root q =
              typeG2RootPairing.root s + typeG2RootPairing.root t
    have hp : p r := hr.induction_on_add
      (fun q hq _ => Or.inl hq)
      (fun s t q hq _ htBase hqPos => by
        have hsPos : typeG2RootPairing_base.IsPos s := by
          rw [RootPairing.Base.isPos_iff']
          have hHeight := typeG2RootPairing_base.height_add hq
          have htHeight := typeG2RootPairing_base.height_one_of_mem_support htBase
          rw [htHeight] at hHeight
          rw [RootPairing.Base.isPos_iff] at hqPos
          have hsNe := typeG2RootPairing_base.height_ne_zero s
          linarith
        exact Or.inr ⟨s, t, hsPos,
          typeG2RootPairing_base.isPos_of_mem_support htBase, hq⟩)
    exact hp hr

/-- The complete root-group datum on the closed G2 Chevalley carrier. -/
public noncomputable def rootData :
    RootGroupData (Carrier (k := k)) (splitTorus (k := k)) where
  Root := RootIndex.{u}
  rootWeight := fun r => rootWeight (k := k) (rootIndexEquiv.symm r.down)
  rootSubgroup := fun r => rootSubgroup (k := k) (rootIndexEquiv.symm r.down)
  neg := fun r => ULift.up (rootSeed.neg r.down)
  add := fun r s => (rootSeed.add r.down s.down).map ULift.up
  pairing := fun r s => rootPairingInt r.down s.down
  weightPairing := fun chi s => characterCocharacterPairing
    (splitTorus (k := k)) (rootCocharacter (k := k) s) (Additive.ofMul chi)
  rootCocharacter := rootCocharacter (k := k)
  reflect := fun r s => ULift.up (rootSeed.reflectionPerm r.down s.down)
  positive := fun r => typeG2RootPairing_base.IsPos r.down
  simple := fun r => r.down ∈ typeG2RootPairing_base.support
  height := fun r => typeG2RootPairing_base.height r.down

/-- The explicit G2 curves realize every and only split-torus root. -/
public theorem rootData_isRealization : (rootData (k := k)).IsRealization := by
  simp only [rootData]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rootData_rootWeight_injective (k := k)
  · apply Set.Subset.antisymm
    · rintro chi ⟨r, rfl⟩
      exact rootWeight_mem_torusRootSet (k := k) (rootIndexEquiv.symm r.down)
    · intro chi hchi
      rw [← rootWeight_range (k := k)] at hchi
      rcases hchi with ⟨r, rfl⟩
      exact ⟨ULift.up (rootIndexEquiv r), by simp⟩
  · intro r
    exact rootSubgroup_package (k := k) (rootIndexEquiv.symm r.down)
  · exact rootWeight_neg (k := k)
  · intro r s t h
    exact rootWeight_add (k := k) r s t
      ((rootData_add_eq_some_iff r s t).mp h)
  · exact rootWeight_reflect (k := k)
  · intro r
    exact rootSeed.cartan_self r.down
  · intro r s
    apply Int.cast_injective (α := ℝ)
    change (((characterCocharacterPairing (splitTorus (k := k))
      (splitTorusCocharacter (k := k)
        (rootCorootExponent (rootIndexEquiv.symm s.down)))
      (Additive.ofMul
        (rootWeight (k := k) (rootIndexEquiv.symm r.down)))) : ℤ) : ℝ) =
      (rootPairingInt r.down s.down : ℝ)
    rw [rootWeight_cocharacter_pairing_cast, rootPairingInt_cast]
  · intro r
    exact typeG2RootPairing_base.height_reflectionPerm_self r.down
  · intro r s t h
    exact typeG2RootPairing_base.height_add
      (rootSeed.add_eq_some_iff.mp
        ((rootData_add_eq_some_iff r s t).mp h))
  · rfl
  · intro r
    change r.down ∈ typeG2RootPairing_base.support ↔
      typeG2RootPairing_base.IsPos r.down ∧
        ∀ s t, (rootData (k := k)).add s t = some r →
          ¬(typeG2RootPairing_base.IsPos s.down ∧
            typeG2RootPairing_base.IsPos t.down)
    rw [mem_standardBase_iff]
    constructor
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      intro s t hadd
      exact h s.down t.down
        ((rootData_add_eq_some_iff s t r).mp hadd)
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      intro s t hadd
      let sl : RootIndex.{u} := ULift.up s
      let tl : RootIndex.{u} := ULift.up t
      exact h sl tl
        ((rootData_add_eq_some_iff sl tl r).mpr (by simpa using hadd))
  · intro chi r
    exact characterCocharacterPairing_spec
      (splitTorus (k := k)) chi (rootCocharacter (k := k) r)

/-- Forgetting the universe lift identifies the carrier labels with the
standard G2 root indices. -/
public def rootDataIndexEquiv : (rootData (k := k)).Root ≃ typeG2Root :=
  Equiv.ulift

/-- The root pairing, reflection action, opposites, and simple roots of the
carrier datum are the actual standard based G2 data. -/
public theorem rootData_isActualBasedRootPairing :
    IsActualBasedRootPairing (rootData (k := k)) typeG2RootPairing
      typeG2RootPairing_base (rootDataIndexEquiv (k := k)) := by
  simp only [rootData, rootDataIndexEquiv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    exact rootPairingInt_cast r.down s.down
  · intro r s
    rfl
  · intro r
    rfl
  · intro r
    rfl

/-- The full root-system realization, including standard-base heights. -/
public theorem rootData_isRootSystemRealization :
    IsRootSystemRealization (rootData (k := k)) typeG2RootPairing
      (rootDataIndexEquiv (k := k)) typeG2RootPairing_base := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (rootData_isActualBasedRootPairing (k := k)).1
  · exact (rootData_isActualBasedRootPairing (k := k)).2.1
  · exact (rootData_isActualBasedRootPairing (k := k)).2.2.1
  · exact (rootData_isActualBasedRootPairing (k := k)).2.2.2
  · intro r
    rfl

/-- The partial addition in the carrier datum is exactly addition of standard
G2 root vectors. -/
public theorem rootData_isRootAdditionRealization :
    IsRootAdditionRealization (rootData (k := k)) typeG2RootPairing
      (rootDataIndexEquiv (k := k)) := by
  simp only [rootData, rootDataIndexEquiv]
  intro r s t
  change Option.map ULift.up (rootSeed.add r.down s.down) = some t ↔
    typeG2RootPairing.root t.down =
      typeG2RootPairing.root r.down + typeG2RootPairing.root s.down
  rw [rootData_add_eq_some_iff]
  exact rootSeed.add_eq_some_iff

end

end

end Theory.AlgebraicGroup.G2Chevalley
