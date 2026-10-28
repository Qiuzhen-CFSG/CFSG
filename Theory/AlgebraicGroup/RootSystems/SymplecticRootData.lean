module

public import Theory.AlgebraicGroup.RootSystems.SymplecticTorusRootExhaustiveness
public import Theory.AlgebraicGroup.RootSystems.ClassicalSymplecticRootRealization
public import Theory.AlgebraicGroup.RootData.FiniteReflectionSeed
public import Theory.AlgebraicGroup.RootData.Realization

/-!
# Symplectic maximal-torus root data

This module assembles the concrete diagonal torus and root subgroups of the
standard symplectic matrix group into realized root data. The root labels are
the signed pair roots and signed double-coordinate roots of
`StandardRootSystem.TypeCRootIndex`; a universe lift places those finite labels
beside the ambient algebraic variety.

The geometric input is the explicit one-parameter subgroup family, its torus
conjugation formula, and the exhaustive classification of diagonal-torus
roots. A finite reflection seed built from the standard type-C pairing supplies
integral Cartan values, opposites, partial addition, a positive system, and
heights. Direct Laurent-character calculations identify the explicit
cocharacters with those Cartan values. Consequently the assembled
`RootGroupData` is a realization, and its pairing, reflection, simple roots,
and heights identify with `StandardRootSystem.typeCRootPairing`.

The maximality proof uses the previously computed centralizer of the diagonal
torus. The final Dynkin-type wrapper reuses
`ClassicalSymplecticRootRealization.typeCRootPairing_hasDynkinType_of_pos`.
-/

open scoped BigOperators
open Set

namespace Theory.AlgebraicGroup
open StandardRootSystem
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public section

noncomputable section

local instance typeCRootPairing_isRootSystem_inst (m : ℕ) :
    (typeCRootPairing m).IsRootSystem := typeCRootPairing_isRootSystem m

local instance typeCRootPairing_isReduced_inst (m : ℕ) :
    (typeCRootPairing m).IsReduced := typeCRootPairing_isReduced m

abbrev SymplecticRootIndex (m : ℕ) := ULift.{u, 0} (TypeCRootIndex m)

noncomputable def symplecticRootPairingInt (m : ℕ) (r s : TypeCRootIndex m) : ℤ :=
  Classical.choose ((typeCRootPairing_isCrystallographic m).exists_value r s)

lemma symplecticRootPairingInt_cast (m : ℕ) (r s : TypeCRootIndex m) :
    (symplecticRootPairingInt m r s : ℝ) = (typeCRootPairing m).pairing r s := by
  exact Classical.choose_spec ((typeCRootPairing_isCrystallographic m).exists_value r s)

@[expose] noncomputable def symplecticSeed (m : ℕ) :
    FiniteReflectionSeed (TypeCRootIndex m) ℝ (typeCRootSpan m)
      (Module.Dual ℝ (typeCRootSpan m)) where
  pairing := (typeCRootPairing m).toLinearMap
  pairing_isPerfPair := (typeCRootPairing m).isPerfPair_toLinearMap
  root := (typeCRootPairing m).root
  coroot := (typeCRootPairing m).coroot
  cartan := symplecticRootPairingInt m
  pairing_eq_cartan := by
    intro i j
    exact (symplecticRootPairingInt_cast m i j).symm
  cartan_self := by
    intro i
    have h : (symplecticRootPairingInt m i i : ℝ) = (2 : ℝ) := by
      rw [symplecticRootPairingInt_cast]
      exact (typeCRootPairing m).pairing_same i
    exact_mod_cast h
  reflectionPerm := (typeCRootPairing m).reflectionPerm
  reflection_root := by
    intro i j
    rw [symplecticRootPairingInt_cast]
    exact (typeCRootPairing m).reflectionPerm_root i j
  reflection_coroot := by
    intro i j
    rw [symplecticRootPairingInt_cast]
    exact (typeCRootPairing m).reflectionPerm_coroot i j
  span_root := RootPairing.IsRootSystem.span_root_eq_top
  span_coroot := RootPairing.IsRootSystem.span_coroot_eq_top
  reduced_scalar_multiple := RootPairing.IsReduced.eq_or_eq_neg

theorem symplecticDiagonalTorus_isMaximalTorus (m : ℕ) :
    IsMaximalTorus (symplecticDiagonalTorus (k := k) m) := by
  refine ⟨symplecticDiagonalTorus_isSubtorus m, ?_⟩
  intro S hS hTS
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro g hg
    have hgcentral : g ∈ Subgroup.centralizer
        ((symplecticDiagonalTorus (k := k) m).toSubgroup :
          Set (Variety.Point
            (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      let _ := S.carrierAlgebraicGroup
      let gs : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨g, hg⟩
      let ts : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨t, hTS ht⟩
      have hcomm := hS.isMulCommutative
      rw [isMulCommutative_iff] at hcomm
      have hamb := congrArg S.inclusion.onPoints (hcomm ts gs)
      have hts : S.inclusion.onPoints ts = t := by
        change (S.pointEquiv ts).val = t
        dsimp only [ts]
        rw [S.pointEquiv.apply_symm_apply]
      have hgs : S.inclusion.onPoints gs = g := by
        change (S.pointEquiv gs).val = g
        dsimp only [gs]
        rw [S.pointEquiv.apply_symm_apply]
      simpa only [map_mul, hts, hgs] using hamb
    have hgclosed : g ∈
        Theory.AlgebraicGroup.ClosedSubgroup.centralizer
          (symplecticDiagonalTorus (k := k) m) := hgcentral
    change g ∈ (symplecticDiagonalTorus (k := k) m).centralizer.toSubgroup at hgclosed
    rw [symplecticDiagonalTorus_centralizer_eq (k := k) m] at hgclosed
    exact hgclosed
  · exact hTS

noncomputable def symplecticRootCorootExponent (m : ℕ) (r : TypeCRootIndex m) : Fin m → ℤ :=
  match r with
  | .inl _ => symplecticRootExponent m r
  | .inr ⟨i, false⟩ => -Pi.single i 1
  | .inr ⟨i, true⟩ => Pi.single i 1

noncomputable def symplecticDiagonalCocharacter (m : ℕ) (z : Fin m → ℤ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter (symplecticDiagonalTorus (k := k) m) := by
  let _ := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (symplecticDiagonalTorusIso (k := k) m).hom.comp
    (dCharacterTupleMorphism (k := k) m 1 (fun i _ => z i))

noncomputable def symplecticRootCocharacter (m : ℕ) (r : SymplecticRootIndex.{u} m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter (symplecticDiagonalTorus (k := k) m) :=
  symplecticDiagonalCocharacter (k := k) m
    (symplecticRootCorootExponent m r.down)

lemma symplecticRootWeight_cocharacter_pairing (m : ℕ)
    (r s : TypeCRootIndex m) :
    characterCocharacterPairing (symplecticDiagonalTorus (k := k) m)
        (symplecticDiagonalCocharacter (k := k) m
          (symplecticRootCorootExponent m s))
        (Additive.ofMul (symplecticRootWeight (k := k) m r)) =
      ∑ i, symplecticRootExponent m r i * symplecticRootCorootExponent m s i := by
  let _ := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  apply (weightCocharacterEquation_existsUnique
    (symplecticDiagonalTorus (k := k) m) (symplecticRootWeight (k := k) m r)
      (symplecticDiagonalCocharacter (k := k) m
        (symplecticRootCorootExponent m s))).unique
  · exact characterCocharacterPairing_spec _ _ _
  · intro t
    change (dLaurentCharacter (k := k) m (symplecticRootExponent m r)).pointCharacter
      ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints
        ((symplecticDiagonalTorusIso (k := k) m).hom.onPoints
          ((dCharacterTupleMorphism (k := k) m 1
            (fun i _ => symplecticRootCorootExponent m s i)).onPoints t))) = _
    rw [(symplecticDiagonalTorusIso (k := k) m).hom_inv_id]
    rw [TorusCharacter.pointCharacter_dLaurentCharacter]
    change (↑(∏ i,
      (dPointEquiv m
        ((dCharacterTupleMorphism (k := k) m 1
          (fun i _ => symplecticRootCorootExponent m s i)).onPoints t) i) ^
            symplecticRootExponent m r i) : k) = _
    simp_rw [dCharacterTupleMorphism_apply (k := k)]
    rw [prod_laurentMonomial_zpow]
    simp

noncomputable def symplecticDiagonalCharacterAddEquiv (m : ℕ) :
    (Fin m → ℤ) ≃+ Additive (TorusWeight (symplecticDiagonalTorus (k := k) m)) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (dLaurentCharacterAddEquiv (k := k) m).trans
    (symplecticDiagonalCharacterTransport (k := k) m).toAdditive

lemma symplecticDiagonalCharacterAddEquiv_apply (m : ℕ) (z : Fin m → ℤ) :
    symplecticDiagonalCharacterAddEquiv (k := k) m z =
      Additive.ofMul (symplecticDiagonalCharacter (k := k) m z) := by
  let _ := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rfl

lemma symplecticRootExponent_cast (m : ℕ) (r : TypeCRootIndex m)
    (i : Fin m) :
    ((symplecticRootExponent m r i : ℤ) : ℝ) = -(typeCRootVector m r i) := by
  rcases r with ⟨⟨⟨a, b⟩, _⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨a, u⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        norm_num [symplecticRootExponent, typeCRootVector, basisVector,
          Pi.single_apply, hia, hib, add_comm]
  · cases u <;> by_cases hia : i = a <;>
      simp [symplecticRootExponent, typeCRootVector, basisVector, hia]

lemma symplecticRootWeight_cocharacter_pairing_cast (m : ℕ)
    (r s : TypeCRootIndex m) :
  (((characterCocharacterPairing (symplecticDiagonalTorus (k := k) m)
      (symplecticDiagonalCocharacter (k := k) m
        (symplecticRootCorootExponent m s))
      (Additive.ofMul (symplecticRootWeight (k := k) m r))) : ℤ) : ℝ) =
      (typeCRootPairing m).pairing r s := by
  rw [show (((characterCocharacterPairing (symplecticDiagonalTorus (k := k) m)
      (symplecticDiagonalCocharacter (k := k) m
        (symplecticRootCorootExponent m s))
      (Additive.ofMul (symplecticRootWeight (k := k) m r))) : ℤ) : ℝ) =
        ((∑ i, symplecticRootExponent m r i *
          symplecticRootCorootExponent m s i : ℤ) : ℝ) by
    rw [symplecticRootWeight_cocharacter_pairing (k := k) m r s]]
  rw [typeCRootPairing_pairing]
  push_cast
  simp_rw [symplecticRootExponent_cast]
  cases s with
  | inl s =>
      simp only [symplecticRootCorootExponent]
      simp_rw [symplecticRootExponent_cast]
      rw [dot_comm]
      simp [typeCRootEmbedding, dot]
  | inr s =>
      rcases s with ⟨i, b⟩
      cases b <;>
        simp [symplecticRootCorootExponent, typeCRootEmbedding, typeCRootVector,
          basisVector, Pi.single_apply, dot]

lemma symplecticRootExponent_neg (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootExponent m (symplecticRootNeg m r) =
      -symplecticRootExponent m r := by
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.neg_apply]
  push_cast
  rw [symplecticRootExponent_cast, symplecticRootExponent_cast,
    symplecticRootNeg_vector]
  simp

@[expose] noncomputable def symplecticRootData (m : ℕ) :
    RootGroupData
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
      (symplecticDiagonalTorus (k := k) m) where
  Root := SymplecticRootIndex.{u} m
  rootWeight := fun r => symplecticRootWeight (k := k) m r.down
  rootSubgroup := fun r => symplecticRootSubgroup (k := k) m r.down
  neg := fun r => ULift.up (symplecticRootNeg m r.down)
  add := fun r s => (symplecticSeed m).add r.down s.down |>.map ULift.up
  pairing := fun r s => symplecticRootPairingInt m r.down s.down
  weightPairing := fun χ s => characterCocharacterPairing
    (symplecticDiagonalTorus (k := k) m)
    (symplecticRootCocharacter (k := k) m s) (Additive.ofMul χ)
  rootCocharacter := symplecticRootCocharacter (k := k) m
  reflect := fun r s => ULift.up (symplecticRootReflect m r.down s.down)
  positive := (symplecticSeed m).positive ∘ ULift.down
  simple := (symplecticSeed m).simple ∘ ULift.down
  height := fun r => (symplecticSeed m).height r.down

lemma symplecticRootExponent_add {m : ℕ} (r s t : TypeCRootIndex m)
    (h : (symplecticSeed m).add r s = some t) :
    symplecticRootExponent m t =
      symplecticRootExponent m r + symplecticRootExponent m s := by
  have hroot := (symplecticSeed m).add_eq_some_iff.mp h
  have hv : typeCRootVector m t = typeCRootVector m r + typeCRootVector m s := by
    have hv' := congrArg (fun z : typeCRootSpan m => (z : Vec m)) hroot
    simpa [symplecticSeed, typeCRootPairing_root, typeCRootInSpan_val,
      typeCRootEmbedding] using hv'
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.add_apply]
  push_cast
  rw [symplecticRootExponent_cast, symplecticRootExponent_cast,
    symplecticRootExponent_cast]
  rw [congrFun hv i]
  simp
  ring

lemma symplecticRootExponent_reflect (m : ℕ) (r s : TypeCRootIndex m) :
    symplecticRootExponent m (symplecticRootReflect m r s) =
      symplecticRootExponent m s -
        symplecticRootPairingInt m s r • symplecticRootExponent m r := by
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  have hv := congrArg (fun z : typeCRootSpan m => (z : Vec m))
    (symplecticRootReflect_root m r s)
  rw [symplecticRootExponent_cast, symplecticRootExponent_cast,
    symplecticRootExponent_cast]
  have hp := symplecticRootPairingInt_cast m s r
  have hvi : typeCRootVector m (symplecticRootReflect m r s) i =
      typeCRootVector m s i -
        (typeCRootPairing m).pairing s r * typeCRootVector m r i := by
    simpa [typeCRootPairing_root, typeCRootInSpan_val, typeCRootEmbedding] using
      congrFun hv i
  rw [← hp] at hvi
  rw [hvi]
  ring

lemma symplecticRootWeight_neg (m : ℕ) (r : SymplecticRootIndex.{u} m) :
    symplecticRootWeight (k := k) m (symplecticRootNeg m r.down) =
      (symplecticRootWeight (k := k) m r.down)⁻¹ := by
  let _ := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticRootExponent m (symplecticRootNeg m r.down)) =
    -(symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticRootExponent m r.down))
  rw [symplecticRootExponent_neg, map_neg]

lemma symplecticRootWeight_add (m : ℕ) (r s t : SymplecticRootIndex.{u} m)
    (h : (symplecticSeed m).add r.down s.down = some t.down) :
    symplecticRootWeight (k := k) m t.down =
      symplecticRootWeight (k := k) m r.down *
        symplecticRootWeight (k := k) m s.down := by
  let _ := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticRootExponent m t.down) =
    symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticRootExponent m r.down) +
      symplecticDiagonalCharacterAddEquiv (k := k) m
        (symplecticRootExponent m s.down)
  rw [symplecticRootExponent_add _ _ _ h, map_add]

lemma symplecticRootWeight_reflect (m : ℕ) (r s : SymplecticRootIndex.{u} m) :
    symplecticRootWeight (k := k) m (symplecticRootReflect m r.down s.down) =
      symplecticRootWeight (k := k) m s.down *
        symplecticRootWeight (k := k) m r.down ^
          (-symplecticRootPairingInt m s.down r.down) := by
  let _ := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticRootExponent m (symplecticRootReflect m r.down s.down)) =
    symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticRootExponent m s.down) +
      (-symplecticRootPairingInt m s.down r.down) •
        symplecticDiagonalCharacterAddEquiv (k := k) m
          (symplecticRootExponent m r.down)
  rw [symplecticRootExponent_reflect, map_sub]
  simp only [map_zsmul]
  simp [sub_eq_add_neg, neg_smul]

lemma symplecticRootNeg_eq_seed_neg (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootNeg m r = (symplecticSeed m).neg r := by
  apply (symplecticSeed m).root.injective
  rw [(symplecticSeed m).root_neg]
  apply Subtype.ext
  simpa [symplecticSeed, typeCRootPairing_root, typeCRootInSpan_val,
    typeCRootEmbedding] using symplecticRootNeg_vector m r

lemma symplecticRootData_add_eq_some_iff (m : ℕ)
    (r s t : SymplecticRootIndex.{u} m) :
    (symplecticRootData (k := k) m).add r s = some t ↔
      (symplecticSeed m).add r.down s.down = some t.down := by
  change Option.map ULift.up ((symplecticSeed m).add r.down s.down) = some t ↔ _
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    refine ⟨t.down, h, ?_⟩
    apply ULift.ext
    rfl

theorem symplecticRootData_isRealization (m : ℕ) :
    (symplecticRootData (k := k) m).IsRealization := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s h
    apply ULift.ext
    exact symplecticRootWeight_injective (k := k) m h
  · apply Set.Subset.antisymm
    · rintro chi ⟨r, rfl⟩
      exact symplecticRootWeight_mem_torusRootSet (k := k) m r.down
    · intro chi hchi
      rw [← symplecticRootWeight_range (k := k) m] at hchi
      rcases hchi with ⟨r, rfl⟩
      exact ⟨ULift.up r, rfl⟩
  · intro r
    change IsTorusRootSubgroup (symplecticDiagonalTorus (k := k) m)
        (symplecticRootSubgroup (k := k) m r.down) ∧
      RootWeightEquation (symplecticDiagonalTorus (k := k) m)
        (symplecticRootSubgroup (k := k) m r.down)
        (symplecticRootWeight (k := k) m r.down)
    exact ⟨⟨symplecticRootSubgroup_invariant (k := k) m r.down,
      symplecticRootSubgroup_isOneParameter (k := k) m r.down⟩,
      symplecticRootWeight_equation (k := k) m r.down⟩
  · exact symplecticRootWeight_neg (k := k) m
  · intro r s t h
    exact symplecticRootWeight_add (k := k) m r s t
      ((symplecticRootData_add_eq_some_iff (k := k) m r s t).mp h)
  · exact symplecticRootWeight_reflect (k := k) m
  · intro r
    exact (symplecticSeed m).cartan_self r.down
  · intro r s
    apply Int.cast_injective (α := ℝ)
    change (((characterCocharacterPairing (symplecticDiagonalTorus (k := k) m)
        (symplecticDiagonalCocharacter (k := k) m
          (symplecticRootCorootExponent m s.down))
        (Additive.ofMul (symplecticRootWeight (k := k) m r.down))) : ℤ) : ℝ) =
      (symplecticRootPairingInt m r.down s.down : ℝ)
    rw [symplecticRootWeight_cocharacter_pairing_cast,
      symplecticRootPairingInt_cast]
  · intro r
    change (symplecticSeed m).height (symplecticRootNeg m r.down) =
      -(symplecticSeed m).height r.down
    rw [symplecticRootNeg_eq_seed_neg, (symplecticSeed m).height_neg]
  · intro r s t h
    exact (symplecticSeed m).height_add
      ((symplecticRootData_add_eq_some_iff (k := k) m r s t).mp h)
  · rfl
  · intro r
    change r.down ∈ (symplecticSeed m).simple ↔
      r.down ∈ (symplecticSeed m).positive ∧
        ∀ s t, (symplecticRootData (k := k) m).add s t = some r →
          ¬(s.down ∈ (symplecticSeed m).positive ∧
            t.down ∈ (symplecticSeed m).positive)
    rw [(symplecticSeed m).mem_simple_iff]
    constructor
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      intro s t hadd
      exact h s.down t.down
        ((symplecticRootData_add_eq_some_iff (k := k) m s t r).mp hadd)
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      intro s t hadd
      let sl : SymplecticRootIndex.{u} m := ULift.up s
      let tl : SymplecticRootIndex.{u} m := ULift.up t
      exact h sl tl
        ((symplecticRootData_add_eq_some_iff (k := k) m sl tl r).mpr
          (by simpa using hadd))
  · intro chi r
    exact characterCocharacterPairing_spec
      (symplecticDiagonalTorus (k := k) m) chi
      (symplecticRootCocharacter (k := k) m r)

/-- Forgetting the universe lift identifies concrete symplectic roots with the
standard type-C root indices. -/
def symplecticRootIndexEquiv (m : ℕ) :
    SymplecticRootIndex.{u} m ≃ TypeCRootIndex m := Equiv.ulift

theorem symplecticRootData_isActualBasedRootPairing (m : ℕ) :
    IsActualBasedRootPairing
      (symplecticRootData (k := k) m)
      (typeCRootPairing m) (symplecticSeed m).base
      (symplecticRootIndexEquiv m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    exact symplecticRootPairingInt_cast m r.down s.down
  · intro r s
    rfl
  · intro r
    change symplecticRootNeg m r.down =
      (typeCRootPairing m).reflectionPerm r.down r.down
    rw [symplecticRootNeg_eq_seed_neg]
    rfl
  · intro r
    rfl

theorem symplecticRootData_isRootSystemRealization (m : ℕ) :
    IsRootSystemRealization
      (symplecticRootData (k := k) m)
      (typeCRootPairing m) (symplecticRootIndexEquiv m)
      (symplecticSeed m).base := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (symplecticRootData_isActualBasedRootPairing (k := k) m).1
  · exact (symplecticRootData_isActualBasedRootPairing (k := k) m).2.1
  · exact (symplecticRootData_isActualBasedRootPairing (k := k) m).2.2.1
  · exact (symplecticRootData_isActualBasedRootPairing (k := k) m).2.2.2
  · intro r
    rfl

theorem symplecticRootData_isRootAdditionRealization (m : ℕ) :
    IsRootAdditionRealization
      (symplecticRootData (k := k) m)
      (typeCRootPairing m) (symplecticRootIndexEquiv m) := by
  intro r s t
  change Option.map ULift.up ((symplecticSeed m).add r.down s.down) = some t ↔
    (typeCRootPairing m).root t.down =
      (typeCRootPairing m).root r.down + (typeCRootPairing m).root s.down
  rw [show Option.map ULift.up ((symplecticSeed m).add r.down s.down) = some t ↔
      (symplecticSeed m).add r.down s.down = some t.down by
    exact symplecticRootData_add_eq_some_iff (k := k) m r s t]
  exact (symplecticSeed m).add_eq_some_iff

theorem symplecticRootData_hasDynkinType_of_pos (m : ℕ) (hm : 0 < m) :
    HasDynkinType (typeCRootPairing m) ⟨.C, m⟩ :=
  typeCRootPairing_hasDynkinType_of_pos m hm

end

end

end Theory.AlgebraicGroup
