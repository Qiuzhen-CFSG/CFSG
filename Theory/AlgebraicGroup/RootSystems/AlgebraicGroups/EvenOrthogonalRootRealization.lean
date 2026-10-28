module

public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalTorusRootExhaustiveness
public import Theory.AlgebraicGroup.RootData.FiniteReflectionSeed
public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions
public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalOmegaSemisimple

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Direct split type-D root realization

This module assembles the explicit split even-orthogonal diagonal torus and
its root curves into a characteristic-free realized type-D root datum.  The
torus is maximal by the direct centralizer calculation, while the tangent
weight and root-curve exhaustiveness theorems identify its roots with the
coordinate roots.  Both the standard type-D pairing and a universe-lifted
copy are realized, so the construction remains usable over an arbitrary
ground-field universe.  The resulting Omega model is the direct geometric
input for the separate Spin-cover and projective-quotient transports.
-/

open scoped BigOperators
open Set

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public section
noncomputable section

abbrev EvenOrthogonalRootIndex (n : ℕ) := ULift.{u, 0} (TypeDRootIndex n)
abbrev TypeDRootSpaceULift (n : ℕ) := ULift.{u, 0} (typeDRootSpan n)
abbrev TypeDCorootSpaceULift (n : ℕ) :=
  ULift.{u, 0} (Module.Dual ℝ (typeDRootSpan n))

@[expose] noncomputable def typeDRootPairingULift (m : ℕ) :
    RootPairing (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2)) := by
  let P := typeDRootPairing m
  let p := P.toLinearMap.compl₁₂
    (ULift.moduleEquiv : TypeDRootSpaceULift.{u} (m + 2) ≃ₗ[ℝ]
      typeDRootSpan (m + 2)).toLinearMap
    (ULift.moduleEquiv : TypeDCorootSpaceULift.{u} (m + 2) ≃ₗ[ℝ]
      Module.Dual ℝ (typeDRootSpan (m + 2))).toLinearMap
  let root : EvenOrthogonalRootIndex.{u} (m + 2) ↪
      TypeDRootSpaceULift.{u} (m + 2) :=
    ⟨fun i => ⟨P.root i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.root.injective
      exact congrArg ULift.down h⟩
  let coroot : EvenOrthogonalRootIndex.{u} (m + 2) ↪
      TypeDCorootSpaceULift.{u} (m + 2) :=
    ⟨fun i => ⟨P.coroot i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.coroot.injective
      exact congrArg ULift.down h⟩
  let reflect (i : EvenOrthogonalRootIndex.{u} (m + 2)) :
      EvenOrthogonalRootIndex.{u} (m + 2) ≃
        EvenOrthogonalRootIndex.{u} (m + 2) :=
    Equiv.ulift.trans ((P.reflectionPerm i.down).trans Equiv.ulift.symm)
  letI : p.IsPerfPair := inferInstance
  exact RootPairing.mk p root coroot
    (by intro i; exact P.root_coroot_two i.down)
    reflect
    (by
      intro i j
      apply ULift.ext
      exact P.reflectionPerm_root i.down j.down)
    (by
      intro i j
      apply ULift.ext
      exact P.reflectionPerm_coroot i.down j.down)

noncomputable def typeDRootPairingULiftEquiv (m : ℕ) :
    RootPairing.Equiv
      (typeDRootPairingULift m : RootPairing
        (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
        (TypeDRootSpaceULift.{u} (m + 2))
        (TypeDCorootSpaceULift.{u} (m + 2)))
      (typeDRootPairing m) where
  weightMap := ULift.moduleEquiv.toLinearMap
  coweightMap := ULift.moduleEquiv.symm.toLinearMap
  indexEquiv := Equiv.ulift
  weight_coweight_transpose := by ext x y; rfl
  root_weightMap := by ext i; rfl
  coroot_coweightMap := by ext i; rfl
  bijective_weightMap := ULift.moduleEquiv.bijective
  bijective_coweightMap := ULift.moduleEquiv.symm.bijective

local instance typeDRootPairingULift_isRootSystem (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).IsRootSystem := by
  constructor
  · change Submodule.span ℝ (Set.range
      (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
        (⟨(typeDRootPairing m).root i.down⟩ :
          TypeDRootSpaceULift.{u} (m + 2)))) = ⊤
    let e : TypeDRootSpaceULift.{u} (m + 2) ≃ₗ[ℝ]
        typeDRootSpan (m + 2) := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
          (⟨(typeDRootPairing m).root i.down⟩ :
            TypeDRootSpaceULift.{u} (m + 2))) =
        Set.range (typeDRootPairing m).root := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeDRootPairing m).root i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_root_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm
  · change Submodule.span ℝ (Set.range
      (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
        (⟨(typeDRootPairing m).coroot i.down⟩ :
          TypeDCorootSpaceULift.{u} (m + 2)))) = ⊤
    let e : TypeDCorootSpaceULift.{u} (m + 2) ≃ₗ[ℝ]
        Module.Dual ℝ (typeDRootSpan (m + 2)) := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
          (⟨(typeDRootPairing m).coroot i.down⟩ :
            TypeDCorootSpaceULift.{u} (m + 2))) =
        Set.range (typeDRootPairing m).coroot := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeDRootPairing m).coroot i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_coroot_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

local instance typeDRootPairingULift_isCrystallographic (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).IsCrystallographic := by
  constructor
  intro i j
  change ∃ z : ℤ, (z : ℝ) = (typeDRootPairing m).pairing i.down j.down
  exact (typeDRootPairing m).exists_value i.down j.down

local instance typeDRootPairingULift_isReduced (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).IsReduced := by
  constructor
  intro i j h
  change ¬ LinearIndependent ℝ
      ![(⟨(typeDRootPairing m).root i.down⟩ :
          TypeDRootSpaceULift.{u} (m + 2)),
        (⟨(typeDRootPairing m).root j.down⟩ :
          TypeDRootSpaceULift.{u} (m + 2))] at h
  have hdown : ¬ LinearIndependent ℝ
      ![(typeDRootPairing m).root i.down,
        (typeDRootPairing m).root j.down] := by
    intro hli
    apply h
    have hmapped := hli.map'
      (ULift.moduleEquiv.symm : typeDRootSpan (m + 2) ≃ₗ[ℝ]
        TypeDRootSpaceULift.{u} (m + 2)).toLinearMap
      (LinearMap.ker_eq_bot.mpr
        (ULift.moduleEquiv.symm : typeDRootSpan (m + 2) ≃ₗ[ℝ]
          TypeDRootSpaceULift.{u} (m + 2)).injective)
    have hvectors :
        (![(⟨(typeDRootPairing m).root i.down⟩ :
              TypeDRootSpaceULift.{u} (m + 2)),
            (⟨(typeDRootPairing m).root j.down⟩ :
              TypeDRootSpaceULift.{u} (m + 2))] :
            Fin 2 → TypeDRootSpaceULift.{u} (m + 2)) =
          (ULift.moduleEquiv.symm : typeDRootSpan (m + 2) ≃ₗ[ℝ]
            TypeDRootSpaceULift.{u} (m + 2)) ∘
            ![(typeDRootPairing m).root i.down,
              (typeDRootPairing m).root j.down] := by
      funext x
      fin_cases x <;> rfl
    rw [hvectors]
    exact hmapped
  letI : (typeDRootPairing m).IsReduced := typeDRootPairing_isReduced m
  rcases RootPairing.IsReduced.eq_or_eq_neg i.down j.down hdown with hij | hij
  · left
    apply ULift.ext
    exact hij
  · right
    apply ULift.ext
    exact hij

noncomputable def evenOrthogonalRootPairingInt (m : ℕ)
    (r s : TypeDRootIndex (m + 2)) : ℤ :=
  Classical.choose ((typeDRootPairing_isCrystallographic m).exists_value r s)

lemma evenOrthogonalRootPairingInt_cast (m : ℕ)
    (r s : TypeDRootIndex (m + 2)) :
    (evenOrthogonalRootPairingInt m r s : ℝ) =
      (typeDRootPairing m).pairing r s :=
  Classical.choose_spec ((typeDRootPairing_isCrystallographic m).exists_value r s)

@[expose] noncomputable def evenOrthogonalSeed (m : ℕ) :
    FiniteReflectionSeed (TypeDRootIndex (m + 2)) ℝ
      (typeDRootSpan (m + 2))
      (Module.Dual ℝ (typeDRootSpan (m + 2))) where
  pairing := (typeDRootPairing m).toLinearMap
  pairing_isPerfPair := (typeDRootPairing m).isPerfPair_toLinearMap
  root := (typeDRootPairing m).root
  coroot := (typeDRootPairing m).coroot
  cartan := evenOrthogonalRootPairingInt m
  pairing_eq_cartan := by intro i j; exact (evenOrthogonalRootPairingInt_cast m i j).symm
  cartan_self := by
    intro i
    have h : (evenOrthogonalRootPairingInt m i i : ℝ) = 2 := by
      rw [evenOrthogonalRootPairingInt_cast]
      exact (typeDRootPairing m).pairing_same i
    exact_mod_cast h
  reflectionPerm := (typeDRootPairing m).reflectionPerm
  reflection_root := by
    intro i j
    rw [evenOrthogonalRootPairingInt_cast]
    exact (typeDRootPairing m).reflectionPerm_root i j
  reflection_coroot := by
    intro i j
    rw [evenOrthogonalRootPairingInt_cast]
    exact (typeDRootPairing m).reflectionPerm_coroot i j
  span_root := RootPairing.IsRootSystem.span_root_eq_top
  span_coroot := RootPairing.IsRootSystem.span_coroot_eq_top
  reduced_scalar_multiple := RootPairing.IsReduced.eq_or_eq_neg

@[expose] noncomputable def typeDRootPairingULiftBase (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).Base :=
  RootPairing.Base.mapEquiv
    (RootPairing.Equiv.symm _ _ (typeDRootPairingULiftEquiv m))
    (evenOrthogonalSeed m).base

noncomputable def evenOrthogonalRootIndexEquiv (m : ℕ) :
    EvenOrthogonalRootIndex.{u} (m + 2) ≃ TypeDRootIndex (m + 2) :=
  Equiv.ulift

noncomputable def evenOrthogonalRootCorootExponent (m : ℕ)
    (r : TypeDRootIndex (m + 2)) : Fin (m + 2) → ℤ :=
  evenOrthogonalRootExponent (m + 2) r

noncomputable def evenOrthogonalDiagonalCocharacter (n : ℕ) (hn : 4 ≤ n)
    (z : Fin n → ℤ) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter
      (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  let _ := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.comp
    (dCharacterTupleMorphism (k := k) n 1 (fun i _ => z i))

noncomputable def evenOrthogonalRootCocharacter (n : ℕ) (hn : 4 ≤ n)
    (r : EvenOrthogonalRootIndex.{u} n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter
      (evenOrthogonalDiagonalTorus (k := k) n hn) :=
    evenOrthogonalDiagonalCocharacter (k := k) n hn
      (evenOrthogonalRootExponent n r.down)

lemma evenOrthogonalRootExponent_cast (n : ℕ) (r : TypeDRootIndex n)
    (i : Fin n) :
    ((evenOrthogonalRootExponent n r i : ℤ) : ℝ) =
      -(typeDRootVector n r i) := by
  rcases r with ⟨⟨⟨a, b⟩, hab⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      norm_num [evenOrthogonalRootExponent, typeDRootVector, basisVector,
        Pi.single_apply, hia, hib, add_comm]

lemma evenOrthogonalRootWeight_cocharacter_pairing (m : ℕ) (hm : 2 ≤ m)
    (r s : TypeDRootIndex (m + 2)) :
    characterCocharacterPairing
        (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
        (evenOrthogonalDiagonalCocharacter (k := k) (m + 2) (by omega)
          (evenOrthogonalRootExponent (m + 2) s))
        (Additive.ofMul (evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r)) =
      ∑ i, evenOrthogonalRootExponent (m + 2) r i *
        evenOrthogonalRootExponent (m + 2) s i := by
  let hn : 4 ≤ m + 2 := by omega
  let _ := (evenOrthogonalDiagonalTorus (k := k) (m + 2) hn).carrierAlgebraicGroup
  apply (weightCocharacterEquation_existsUnique
    (evenOrthogonalDiagonalTorus (k := k) (m + 2) hn)
    (evenOrthogonalRootWeight (k := k) (m + 2) hn r)
      (evenOrthogonalDiagonalCocharacter (k := k) (m + 2) hn
        (evenOrthogonalRootExponent (m + 2) s))).unique
  · exact characterCocharacterPairing_spec _ _ _
  · intro t
    change (dLaurentCharacter (k := k) (m + 2)
      (evenOrthogonalRootExponent (m + 2) r)).pointCharacter
      ((evenOrthogonalDiagonalTorusIso (k := k) (m + 2) hn).inv.onPoints
        ((evenOrthogonalDiagonalTorusIso (k := k) (m + 2) hn).hom.onPoints
          ((dCharacterTupleMorphism (k := k) (m + 2) 1
            (fun i _ => evenOrthogonalRootExponent (m + 2) s i)).onPoints t))) =
      (dPointEquiv 1 t 0 : k) ^
        (∑ i, evenOrthogonalRootExponent (m + 2) r i *
          evenOrthogonalRootExponent (m + 2) s i)
    rw [(evenOrthogonalDiagonalTorusIso (k := k) (m + 2) hn).hom_inv_id,
      TorusCharacter.pointCharacter_dLaurentCharacter]
    change (↑(∏ i,
      (dPointEquiv (m + 2)
        ((dCharacterTupleMorphism (k := k) (m + 2) 1
          (fun i _ => evenOrthogonalRootExponent (m + 2) s i)).onPoints t) i) ^
            evenOrthogonalRootExponent (m + 2) r i) : k) = _
    simp_rw [dCharacterTupleMorphism_apply (k := k)]
    rw [prod_laurentMonomial_zpow]
    simp

lemma evenOrthogonalRootWeight_cocharacter_pairing_cast (m : ℕ) (hm : 2 ≤ m)
    (r s : TypeDRootIndex (m + 2)) :
    (((characterCocharacterPairing
      (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
      (evenOrthogonalDiagonalCocharacter (k := k) (m + 2) (by omega)
        (evenOrthogonalRootExponent (m + 2) s))
      (Additive.ofMul (evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r))) : ℤ) : ℝ) =
      (typeDRootPairing m).pairing r s := by
  have hpair := evenOrthogonalRootWeight_cocharacter_pairing (k := k) m hm r s
  rw [show (((characterCocharacterPairing
      (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
      (evenOrthogonalDiagonalCocharacter (k := k) (m + 2) (by omega)
        (evenOrthogonalRootExponent (m + 2) s))
      (Additive.ofMul (evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r))) : ℤ) : ℝ) =
        ((∑ i, evenOrthogonalRootExponent (m + 2) r i *
          evenOrthogonalRootExponent (m + 2) s i : ℤ) : ℝ) by
    rw [hpair]]
  rw [typeDRootPairing_pairing]
  push_cast
  simp_rw [evenOrthogonalRootExponent_cast]
  simp only [neg_mul_neg]
  simp only [typeDRootEmbedding, dot]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma evenOrthogonalRootExponent_neg (m : ℕ) (hm : 2 ≤ m)
    (r : TypeDRootIndex (m + 2)) :
    evenOrthogonalRootExponent (m + 2) ((evenOrthogonalSeed m).neg r) =
      -evenOrthogonalRootExponent (m + 2) r := by
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.neg_apply]
  push_cast
  rw [evenOrthogonalRootExponent_cast, evenOrthogonalRootExponent_cast]
  have hv := congrArg (fun z : typeDRootSpan (m + 2) => (z : Vec (m + 2)))
    ((evenOrthogonalSeed m).root_neg r)
  have hvi : typeDRootVector (m + 2) ((evenOrthogonalSeed m).neg r) i =
      -typeDRootVector (m + 2) r i := by
    simpa [evenOrthogonalSeed, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding] using congrFun hv i
  rw [hvi]

lemma evenOrthogonalRootExponent_add {m : ℕ} (hm : 2 ≤ m)
    (r s t : TypeDRootIndex (m + 2))
    (h : (evenOrthogonalSeed m).add r s = some t) :
    evenOrthogonalRootExponent (m + 2) t =
      evenOrthogonalRootExponent (m + 2) r +
        evenOrthogonalRootExponent (m + 2) s := by
  have hroot := (evenOrthogonalSeed m).add_eq_some_iff.mp h
  have hv : typeDRootVector (m + 2) t =
      typeDRootVector (m + 2) r + typeDRootVector (m + 2) s := by
    have hv' := congrArg (fun z : typeDRootSpan (m + 2) => (z : Vec (m + 2))) hroot
    simpa [evenOrthogonalSeed, typeDRootPairing_root, typeDRootInSpan_val,
      typeDRootEmbedding] using hv'
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.add_apply]
  push_cast
  rw [evenOrthogonalRootExponent_cast, evenOrthogonalRootExponent_cast,
    evenOrthogonalRootExponent_cast]
  rw [congrFun hv i]
  simp only [Pi.add_apply]
  ring

lemma evenOrthogonalRootExponent_reflect (m : ℕ) (hm : 2 ≤ m)
    (r s : TypeDRootIndex (m + 2)) :
    evenOrthogonalRootExponent (m + 2)
        ((evenOrthogonalSeed m).reflectionPerm r s) =
      evenOrthogonalRootExponent (m + 2) s -
        evenOrthogonalRootPairingInt m s r •
          evenOrthogonalRootExponent (m + 2) r := by
  funext i
  apply Int.cast_injective (α := ℝ)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [evenOrthogonalRootExponent_cast, evenOrthogonalRootExponent_cast,
    evenOrthogonalRootExponent_cast]
  have hvi : typeDRootVector (m + 2) ((evenOrthogonalSeed m).reflectionPerm r s) i =
      typeDRootVector (m + 2) s i -
        (evenOrthogonalRootPairingInt m s r : ℝ) * typeDRootVector (m + 2) r i := by
    have hv := congrArg (fun z : typeDRootSpan (m + 2) => (z : Vec (m + 2)) i)
      ((evenOrthogonalSeed m).reflection_root r s).symm
    change typeDRootVector (m + 2) ((evenOrthogonalSeed m).reflectionPerm r s) i =
      typeDRootVector (m + 2) s i -
        (evenOrthogonalRootPairingInt m s r : ℝ) * typeDRootVector (m + 2) r i at hv
    exact hv
  rw [hvi]
  ring

noncomputable def evenOrthogonalDiagonalCharacterAddEquiv (n : ℕ) (hn : 4 ≤ n) :
    (Fin n → ℤ) ≃+ Additive
      (TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn)) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact (dLaurentCharacterAddEquiv (k := k) n).trans
    (evenOrthogonalDiagonalCharacterTransport (k := k) n hn).toAdditive

lemma evenOrthogonalDiagonalCharacterAddEquiv_apply (n : ℕ) (hn : 4 ≤ n)
    (z : Fin n → ℤ) :
    evenOrthogonalDiagonalCharacterAddEquiv (k := k) n hn z =
      Additive.ofMul (evenOrthogonalDiagonalCharacter (k := k) n hn z) := by
  let _ := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  rfl

@[expose] noncomputable def evenOrthogonalRootData (m : ℕ) (hm : 2 ≤ m) :
    RootGroupData
      (evenSpinActionImageClosedSubgroup
        (hyperbolicForm (k := k) (m + 2))
        (standardHyperbolicSplit (m + 2))).carrierVariety
      (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega)) where
  Root := EvenOrthogonalRootIndex.{u} (m + 2)
  rootWeight := fun r => evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down
  rootSubgroup := fun r => evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down
  neg := fun r => ULift.up ((evenOrthogonalSeed m).neg r.down)
  add := fun r s => ((evenOrthogonalSeed m).add r.down s.down).map ULift.up
  pairing := fun r s => evenOrthogonalRootPairingInt m r.down s.down
  weightPairing := fun χ s => characterCocharacterPairing
    (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
    (evenOrthogonalRootCocharacter (k := k) (m + 2) (by omega) s)
    (Additive.ofMul χ)
  rootCocharacter := evenOrthogonalRootCocharacter (k := k) (m + 2) (by omega)
  reflect := fun r s => ULift.up ((evenOrthogonalSeed m).reflectionPerm r.down s.down)
  positive := (evenOrthogonalSeed m).positive ∘ ULift.down
  simple := (evenOrthogonalSeed m).simple ∘ ULift.down
  height := fun r => (evenOrthogonalSeed m).height r.down

lemma evenOrthogonalRootWeight_neg (m : ℕ) (hm : 2 ≤ m)
    (r : EvenOrthogonalRootIndex.{u} (m + 2)) :
    evenOrthogonalRootWeight (k := k) (m + 2) (by omega)
        ((evenOrthogonalSeed m).neg r.down) =
      (evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down)⁻¹ := by
  let hn : 4 ≤ m + 2 := by omega
  let _ := (evenOrthogonalDiagonalTorus (k := k) (m + 2) hn).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
      (evenOrthogonalRootExponent (m + 2) ((evenOrthogonalSeed m).neg r.down)) =
    -(evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
      (evenOrthogonalRootExponent (m + 2) r.down))
  rw [evenOrthogonalRootExponent_neg (m := m) hm, map_neg]

lemma evenOrthogonalRootWeight_add (m : ℕ) (hm : 2 ≤ m)
    (r s t : EvenOrthogonalRootIndex.{u} (m + 2))
    (h : (evenOrthogonalSeed m).add r.down s.down = some t.down) :
    evenOrthogonalRootWeight (k := k) (m + 2) (by omega) t.down =
      evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down *
        evenOrthogonalRootWeight (k := k) (m + 2) (by omega) s.down := by
  let hn : 4 ≤ m + 2 := by omega
  let _ := (evenOrthogonalDiagonalTorus (k := k) (m + 2) hn).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
      (evenOrthogonalRootExponent (m + 2) t.down) =
    evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
      (evenOrthogonalRootExponent (m + 2) r.down) +
      evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
        (evenOrthogonalRootExponent (m + 2) s.down)
  rw [evenOrthogonalRootExponent_add hm r.down s.down t.down h, map_add]

lemma evenOrthogonalRootWeight_reflect (m : ℕ) (hm : 2 ≤ m)
    (r s : EvenOrthogonalRootIndex.{u} (m + 2)) :
    evenOrthogonalRootWeight (k := k) (m + 2) (by omega)
        ((evenOrthogonalSeed m).reflectionPerm r.down s.down) =
      evenOrthogonalRootWeight (k := k) (m + 2) (by omega) s.down *
        evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down ^
          (-evenOrthogonalRootPairingInt m s.down r.down) := by
  let hn : 4 ≤ m + 2 := by omega
  let _ := (evenOrthogonalDiagonalTorus (k := k) (m + 2) hn).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
      (evenOrthogonalRootExponent (m + 2)
        ((evenOrthogonalSeed m).reflectionPerm r.down s.down)) =
    evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
      (evenOrthogonalRootExponent (m + 2) s.down) +
      (-evenOrthogonalRootPairingInt m s.down r.down) •
        evenOrthogonalDiagonalCharacterAddEquiv (k := k) (m + 2) hn
          (evenOrthogonalRootExponent (m + 2) r.down)
  rw [evenOrthogonalRootExponent_reflect m hm r.down s.down, map_sub]
  simp only [map_zsmul, sub_eq_add_neg, neg_smul]

lemma evenOrthogonalRootData_add_eq_some_iff (m : ℕ) (hm : 2 ≤ m)
    (r s t : EvenOrthogonalRootIndex.{u} (m + 2)) :
    (evenOrthogonalRootData (k := k) m hm).add r s = some t ↔
      (evenOrthogonalSeed m).add r.down s.down = some t.down := by
  change Option.map ULift.up ((evenOrthogonalSeed m).add r.down s.down) = some t ↔ _
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    refine ⟨t.down, h, ?_⟩
    apply ULift.ext
    rfl

theorem evenOrthogonalRootData_isRealization (m : ℕ) (hm : 2 ≤ m) :
    (evenOrthogonalRootData (k := k) m hm).IsRealization := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s h
    apply ULift.ext
    exact evenOrthogonalRootWeight_injective (k := k) (m + 2) (by omega) h
  · apply Set.Subset.antisymm
    · rintro chi ⟨r, rfl⟩
      exact evenOrthogonalRootWeight_mem_torusRootSet (k := k) (m + 2) (by omega) r.down
    · intro chi hchi
      rw [← evenOrthogonalRootWeight_range (k := k) (m + 2) (by omega)] at hchi
      rcases hchi with ⟨r, rfl⟩
      exact ⟨ULift.up r, rfl⟩
  · intro r
    change IsTorusRootSubgroup
        (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
        (evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down) ∧
      RootWeightEquation
        (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
        (evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down)
        (evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down)
    exact ⟨⟨evenOrthogonalRootSubgroup_invariant (k := k) (m + 2) (by omega) r.down,
      evenOrthogonalRootSubgroup_isOneParameter (k := k) (m + 2) (by omega) r.down⟩,
      evenOrthogonalRootWeight_equation (k := k) (m + 2) (by omega) r.down⟩
  · exact evenOrthogonalRootWeight_neg (k := k) m hm
  · intro r s t h
    exact evenOrthogonalRootWeight_add (k := k) m hm r s t
      ((evenOrthogonalRootData_add_eq_some_iff (k := k) m hm r s t).mp h)
  · exact evenOrthogonalRootWeight_reflect (k := k) m hm
  · intro r
    exact (evenOrthogonalSeed m).cartan_self r.down
  · intro r s
    apply Int.cast_injective (α := ℝ)
    change (((characterCocharacterPairing
        (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
        (evenOrthogonalDiagonalCocharacter (k := k) (m + 2) (by omega)
          (evenOrthogonalRootExponent (m + 2) s.down))
        (Additive.ofMul (evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down))) : ℤ) : ℝ) =
      (evenOrthogonalRootPairingInt m r.down s.down : ℝ)
    rw [evenOrthogonalRootWeight_cocharacter_pairing_cast (k := k) m hm r.down s.down,
      evenOrthogonalRootPairingInt_cast]
  · intro r
    change (evenOrthogonalSeed m).height ((evenOrthogonalSeed m).neg r.down) =
      -(evenOrthogonalSeed m).height r.down
    exact (evenOrthogonalSeed m).height_neg r.down
  · intro r s t h
    exact (evenOrthogonalSeed m).height_add
      ((evenOrthogonalRootData_add_eq_some_iff (k := k) m hm r s t).mp h)
  · rfl
  · intro r
    change r.down ∈ (evenOrthogonalSeed m).simple ↔
      r.down ∈ (evenOrthogonalSeed m).positive ∧
        ∀ s t, (evenOrthogonalRootData (k := k) m hm).add s t = some r →
          ¬(s.down ∈ (evenOrthogonalSeed m).positive ∧
            t.down ∈ (evenOrthogonalSeed m).positive)
    rw [(evenOrthogonalSeed m).mem_simple_iff]
    constructor
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      intro s t hadd
      exact h s.down t.down
        ((evenOrthogonalRootData_add_eq_some_iff (k := k) m hm s t r).mp hadd)
    · rintro ⟨hr, h⟩
      refine ⟨hr, ?_⟩
      intro s t hadd
      let sl : EvenOrthogonalRootIndex.{u} (m + 2) := ULift.up s
      let tl : EvenOrthogonalRootIndex.{u} (m + 2) := ULift.up t
      exact h sl tl
        ((evenOrthogonalRootData_add_eq_some_iff (k := k) m hm sl tl r).mpr
          (by simpa using hadd))
  · intro chi r
    exact characterCocharacterPairing_spec
      (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega)) chi
      (evenOrthogonalRootCocharacter (k := k) (m + 2) (by omega) r)

theorem evenOrthogonalRootData_isActualBasedRootPairing (m : ℕ) (hm : 2 ≤ m) :
    IsActualBasedRootPairing
      (evenOrthogonalRootData (k := k) m hm)
      (typeDRootPairing m) (evenOrthogonalSeed m).base
      (evenOrthogonalRootIndexEquiv m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    exact evenOrthogonalRootPairingInt_cast m r.down s.down
  · intro r s
    rfl
  · intro r
    change (evenOrthogonalSeed m).neg r.down =
      (typeDRootPairing m).reflectionPerm r.down r.down
    rfl
  · intro r
    rfl

theorem evenOrthogonalRootData_isRootSystemRealization (m : ℕ) (hm : 2 ≤ m) :
    IsRootSystemRealization
      (evenOrthogonalRootData (k := k) m hm)
      (typeDRootPairing m) (evenOrthogonalRootIndexEquiv m)
      (evenOrthogonalSeed m).base := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (evenOrthogonalRootData_isActualBasedRootPairing (k := k) m hm).1
  · exact (evenOrthogonalRootData_isActualBasedRootPairing (k := k) m hm).2.1
  · exact (evenOrthogonalRootData_isActualBasedRootPairing (k := k) m hm).2.2.1
  · exact (evenOrthogonalRootData_isActualBasedRootPairing (k := k) m hm).2.2.2
  · intro r
    rfl

theorem evenOrthogonalRootData_isRootAdditionRealization (m : ℕ) (hm : 2 ≤ m) :
    IsRootAdditionRealization
      (evenOrthogonalRootData (k := k) m hm)
      (typeDRootPairing m) (evenOrthogonalRootIndexEquiv m) := by
  intro r s t
  change Option.map ULift.up ((evenOrthogonalSeed m).add r.down s.down) = some t ↔
    (typeDRootPairing m).root t.down =
      (typeDRootPairing m).root r.down + (typeDRootPairing m).root s.down
  rw [show Option.map ULift.up ((evenOrthogonalSeed m).add r.down s.down) = some t ↔
      (evenOrthogonalSeed m).add r.down s.down = some t.down by
    exact evenOrthogonalRootData_add_eq_some_iff (k := k) m hm r s t]
  exact (evenOrthogonalSeed m).add_eq_some_iff

theorem evenOrthogonalRootData_isActualBasedRootPairingULift (m : ℕ) (hm : 2 ≤ m) :
    IsActualBasedRootPairing
      (evenOrthogonalRootData (k := k) m hm)
      (typeDRootPairingULift m)
      (typeDRootPairingULiftBase m)
      (Equiv.refl (EvenOrthogonalRootIndex.{u} (m + 2))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    change (evenOrthogonalRootPairingInt m r.down s.down : ℝ) = _
    rw [evenOrthogonalRootPairingInt_cast]
    rfl
  · intro r s
    rfl
  · intro r
    change ULift.up ((evenOrthogonalSeed m).neg r.down) = _
    apply ULift.ext
    rfl
  · intro r
    change r.down ∈ (evenOrthogonalSeed m).base.support ↔
      r ∈ (typeDRootPairingULiftBase m).support
    have hmem := RootPairing.Base.mem_mapEquiv_support
      (RootPairing.Equiv.symm _ _ (typeDRootPairingULiftEquiv m))
      (evenOrthogonalSeed m).base r
    have heq :
        (RootPairing.Equiv.symm _ _
          (typeDRootPairingULiftEquiv m)).indexEquiv.symm r = r.down := rfl
    rw [heq] at hmem
    exact hmem.symm

noncomputable def standardEvenOrthogonalOmegaCarrierRootSystemModelULift
    (m : ℕ) (hm : 2 ≤ m) :
    RootSystemModel
      (typeDRootPairingULift m : RootPairing
        (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
          (TypeDRootSpaceULift.{u} (m + 2))
          (TypeDCorootSpaceULift.{u} (m + 2)))
      (evenSpinActionImageClosedSubgroup
        (hyperbolicForm (k := k) (m + 2))
        (standardHyperbolicSplit (m + 2))).carrierVariety where
  torus := evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega)
  maximalTorus := evenOrthogonalDiagonalTorus_isMaximalTorus (k := k) (m + 2) (by omega)
  rootData := evenOrthogonalRootData (k := k) m hm
  realization := evenOrthogonalRootData_isRealization (k := k) m hm
  base := typeDRootPairingULiftBase m
  rootEquiv := Equiv.refl (EvenOrthogonalRootIndex.{u} (m + 2))
  actual := evenOrthogonalRootData_isActualBasedRootPairingULift (k := k) m hm

noncomputable def standardEvenOrthogonalOmegaVersionULift (m : ℕ) (hm : 2 ≤ m) :
    SemisimpleVersion (k := k)
      (typeDRootPairingULift m : RootPairing
        (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
          (TypeDRootSpaceULift.{u} (m + 2))
          (TypeDCorootSpaceULift.{u} (m + 2))) where
  carrier :=
    (evenSpinActionImageClosedSubgroup
      (hyperbolicForm (k := k) (m + 2))
      (standardHyperbolicSplit (m + 2))).carrierVariety
  group :=
    (evenSpinActionImageClosedSubgroup
      (hyperbolicForm (k := k) (m + 2))
      (standardHyperbolicSplit (m + 2))).carrierAlgebraicGroup
  semisimple := evenSpinActionImageClosedSubgroup_isSemisimple
    (standardHyperbolicSplit (m + 2)) (by
      rw [standardHyperbolicSplit_rank]
      omega)
  rootModel := standardEvenOrthogonalOmegaCarrierRootSystemModelULift (k := k) m hm

noncomputable def standardEvenOrthogonalOmegaCarrierRootSystemModel
    {k₀ : Type} [Field k₀] [IsAlgClosed k₀]
    (m : ℕ) (hm : 2 ≤ m) :
    RootSystemModel (k := k₀) (typeDRootPairing m)
      (evenSpinActionImageClosedSubgroup
        (hyperbolicForm (k := k₀) (m + 2))
        (standardHyperbolicSplit (m + 2))).carrierVariety where
  torus := evenOrthogonalDiagonalTorus (k := k₀) (m + 2) (by omega)
  maximalTorus := evenOrthogonalDiagonalTorus_isMaximalTorus (k := k₀) (m + 2) (by omega)
  rootData := evenOrthogonalRootData (k := k₀) m hm
  realization := evenOrthogonalRootData_isRealization (k := k₀) m hm
  base := (evenOrthogonalSeed m).base
  rootEquiv := evenOrthogonalRootIndexEquiv m
  actual := evenOrthogonalRootData_isActualBasedRootPairing (k := k₀) m hm

noncomputable def standardEvenOrthogonalOmegaVersion
    {k₀ : Type} [Field k₀] [IsAlgClosed k₀]
    (m : ℕ) (hm : 2 ≤ m) :
    SemisimpleVersion (k := k₀) (typeDRootPairing m) where
  carrier :=
    (evenSpinActionImageClosedSubgroup
      (hyperbolicForm (k := k₀) (m + 2))
      (standardHyperbolicSplit (m + 2))).carrierVariety
  group :=
    (evenSpinActionImageClosedSubgroup
      (hyperbolicForm (k := k₀) (m + 2))
      (standardHyperbolicSplit (m + 2))).carrierAlgebraicGroup
  semisimple := evenSpinActionImageClosedSubgroup_isSemisimple
    (standardHyperbolicSplit (m + 2)) (by
      rw [standardHyperbolicSplit_rank]
      omega)
  rootModel := standardEvenOrthogonalOmegaCarrierRootSystemModel m hm

end
end
end Theory.AlgebraicGroup
