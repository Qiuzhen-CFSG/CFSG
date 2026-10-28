module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Candidates
public import Theory.AlgebraicGroup.RootSubgroups.PositiveContraction
public import Theory.AlgebraicGroup.Unipotent.Contraction.Unipotence
public import Theory.AlgebraicGroup.Borel.SolvableRootContainment
public import Theory.AlgebraicGroup.Jordan.ClosedSubgroup
public import Theory.AlgebraicGroup.Unipotent.Basic

/-!
# Unipotence and radicals of the literal F4 candidates

The inverse F4 Cartan matrix supplies an integral chamber functional with
value one on every simple root. Root addition makes it positive on all of the
original positive roots; its negative treats the opposite roots. Torus duality
constructs a regular contracting cocharacter, so the two actual root-generated
groups are unipotent. Adjoining the normalizing torus gives solvable candidates.
Their exact `T * U` factorizations and the trivial torus/unipotent intersection
identify `U` with the whole unipotent radical, including radical maximality.

Borel maximality and separation of opposite candidates are not asserted here.
The raw inverse-conjugation convention is retained, without changing the
representation coefficients or the positive root labels.
Source: GLS3, Theorem 1.11.2 (`refs/KGroup/GLS3/Chapter1.tex`), and Steinberg
(6.2)(a-b) (`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
open RootModel.Corrected
open scoped BigOperators
@[expose] public noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The row sums of the integral inverse F4 Cartan matrix. -/
def chamberCoefficients : Fin 4 → ℤ := ![11, 21, 15, 8]

/-- The integral chamber functional on the actual torus character group. -/
def chamberFunctional : Additive (TorusWeight (F4Chevalley.splitTorus (k := F))) →+ ℤ :=
  ∑ i : Fin 4, chamberCoefficients i •
    characterCocharacterPairing (F4Chevalley.splitTorus (k := F)) (rawSimpleCocharacter i)

omit [CharP F 2] in
/-- The chamber functional is evaluated on the corrected raw simple coroots. -/
lemma chamberFunctional_root (r : F4Chevalley.Root) :
    chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight r)) =
      ∑ i, chamberCoefficients i * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) := by
  have hpair (i : Fin 4) :
      characterCocharacterPairing (F4Chevalley.splitTorus (k := F))
        (rawSimpleCocharacter i) (Additive.ofMul (F4Chevalley.rootWeight r)) =
      typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) :=
    (weightCocharacterEquation_existsUnique _ _ _).unique
      (characterCocharacterPairing_spec _ _ _) (rootWeight_rawSimpleCocharacter r i)
  simp only [chamberFunctional, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
    zsmul_eq_mul, Int.cast_id, hpair]

omit [CharP F 2] in
/-- Every original numbered simple root has chamber value one. -/
lemma chamberFunctional_simple (i : Fin 4) :
    chamberFunctional (F := F)
      (Additive.ofMul (F4Chevalley.rootWeight (typeF4SimpleRootIndex i))) = 1 := by
  rw [chamberFunctional_root]
  have hcart (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j := by
    change typeF4RootPairing.pairingIn ℤ (typeF4RootPairing_baseEquiv i)
      (typeF4RootPairing_baseEquiv j) = _
    rw [← RootPairing.Base.cartanMatrixIn_def ℤ typeF4RootPairing_base]
    exact typeF4RootPairing_base_cartan_apply i j
  simp_rw [hcart]
  have hc : ∀ i : Fin 4, ∑ j, chamberCoefficients j * typeF4CartanMatrix i j = 1 := by decide
  exact hc i

private lemma chamberFunctional_root_add (r s q : F4Chevalley.Root)
    (hq : typeF4RootPairing.root q = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight q)) =
      chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight r)) +
      chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight s)) := by
  have ha : (rootData (F := F)).add ⟨r⟩ ⟨s⟩ = some ⟨q⟩ := by
    change (rootAdd r s).map ULift.up = some ⟨q⟩
    rw [(rootAdd_eq_some_iff r s q).mpr hq]
    rfl
  have he := (rootData_isRealization_charTwo (F := F)).2.2.2.2.1 ⟨r⟩ ⟨s⟩ ⟨q⟩ ha
  change F4Chevalley.rootWeight q = F4Chevalley.rootWeight r * F4Chevalley.rootWeight s at he
  rw [he]
  exact map_add (chamberFunctional (F := F)) _ _

/-- The chamber functional is strictly positive on the prescribed positive roots. -/
lemma chamberFunctional_root_positive (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) :
    0 < chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight r)) := by
  have hs (r : F4Chevalley.Root) (hr : r ∈ typeF4RootPairing_base.support) :
      chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight r)) = 1 := by
    obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have hi' : typeF4SimpleRootIndex i = r := congrArg Subtype.val hi
    rw [← hi']
    exact chamberFunctional_simple i
  apply hr.induction_on_add
  · intro r hr
    rw [hs r hr]
    decide
  · intro r s q hq hpos hs'
    rw [chamberFunctional_root_add r s q hq, hs s hs']
    omega

local instance unipotenceSubgroupAlgebraicGroup
    (S : ClosedSubgroup (F4Chevalley.Carrier (k := F))) :
    AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup

private lemma rootGenerated_isUnipotent_of_functional (A : Set (Roots F))
    (phi : Additive (TorusWeight (F4Chevalley.splitTorus (k := F))) →+ ℤ)
    (hphi : ∀ r ∈ A, 0 < phi (Additive.ofMul ((rootSystemModel (F := F)).rootData.rootWeight r))) :
    IsUnipotentAlgebraicGroup (rootGenerated F A).carrierVariety := by
  obtain ⟨lambda, hlambda⟩ := rootSubgroupGenerated_exists_contracting_cocharacter
    (rootSystemModel (F := F)).rootData rootData_isRealization_charTwo
    F4Chevalley.splitTorus_isSubtorus A phi hphi
  intro x
  have hx := ((rootGenerated F A).pointEquiv x).property
  have hg := (hlambda _ hx).isUnipotentElement
  have h := closedSubgroup_unipotent_of_ambient (rootGenerated F A) hx hg
  have heq : (rootGenerated F A).pointEquiv.symm
      ⟨((rootGenerated F A).pointEquiv x).val, hx⟩ = x := by
    apply (rootGenerated F A).pointEquiv.injective
    rw [Equiv.apply_symm_apply]
  rw [heq] at h
  exact h

/-- Every point of the actual positive root-generated group is unipotent. -/
lemma positiveUnipotent_isUnipotent :
    IsUnipotentAlgebraicGroup (positiveUnipotent F).carrierVariety :=
  rootGenerated_isUnipotent_of_functional (positiveRoots F) chamberFunctional
    (fun r hr => chamberFunctional_root_positive r.down hr)

/-- Negating the chamber functional contracts the actual negative root group. -/
lemma negativeUnipotent_isUnipotent :
    IsUnipotentAlgebraicGroup (negativeUnipotent F).carrierVariety := by
  apply rootGenerated_isUnipotent_of_functional (negativeRoots F) (-chamberFunctional)
  intro r hr
  have h := chamberFunctional_root_positive (F := F)
    ((rootSystemModel (F := F)).rootData.neg r).down hr
  have hneg := (rootData_isRealization_charTwo (F := F)).2.2.2.1 r
  change (rootSystemModel (F := F)).rootData.rootWeight
    ((rootSystemModel (F := F)).rootData.neg r) =
      ((rootSystemModel (F := F)).rootData.rootWeight r)⁻¹ at hneg
  change 0 < chamberFunctional (Additive.ofMul
    ((rootSystemModel (F := F)).rootData.rootWeight
      ((rootSystemModel (F := F)).rootData.neg r))) at h
  rw [hneg] at h
  change 0 < chamberFunctional (F := F) (-Additive.ofMul
    (F4Chevalley.rootWeight r.down)) at h
  change 0 < -(chamberFunctional (F := F) (Additive.ofMul (F4Chevalley.rootWeight r.down)))
  simpa only [map_neg] using h

private lemma candidate_solvable_of_unipotent (A : Set (Roots F))
    (hU : IsUnipotentAlgebraicGroup (rootGenerated F A).carrierVariety) :
    Group.IsSolvable (Variety.Point (torusRootGenerated F A).carrierVariety) := by
  let U := rootGenerated F A
  let C := torusRootGenerated F A
  let : Group.IsSolvable (Variety.Point U.carrierVariety) :=
    isSolvable_of_isUnipotentAlgebraicGroup hU
  have hsolv : Group.IsSolvable (RootSubgroupGenerated (rootSystemModel (F := F)).rootData A) :=
    Group.isSolvable_of_surjective (f := (Equiv.mulEquiv U.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv U.pointEquiv).surjective
  obtain ⟨B, hB, hTB, hUB⟩ := exists_borelSubgroup_containing_solvable_roots
    (rootSystemModel (F := F)).rootData rootData_isRealization_charTwo
    F4Chevalley.splitTorus_isSubtorus A hsolv
  have hCB : C.toSubgroup ≤ B.toSubgroup := sup_le hTB hUB
  let : Group.IsSolvable (Variety.Point B.carrierVariety) := hB.solvable
  let : Group.IsSolvable B.toSubgroup :=
    Group.isSolvable_of_surjective (f := (Equiv.mulEquiv B.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv B.pointEquiv).surjective
  let j := (Subgroup.inclusion hCB).comp (Equiv.mulEquiv C.pointEquiv).toMonoidHom
  exact Group.isSolvable_of_isSolvable_injective (f := j)
    ((Subgroup.inclusion_injective hCB).comp (Equiv.mulEquiv C.pointEquiv).injective)

/-- The positive torus/root candidate is solvable. -/
lemma positiveCandidate_solvable :
    Group.IsSolvable (Variety.Point (positiveCandidate F).carrierVariety) :=
  candidate_solvable_of_unipotent _ positiveUnipotent_isUnipotent

/-- The opposite torus/root candidate is solvable. -/
lemma negativeCandidate_solvable :
    Group.IsSolvable (Variety.Point (negativeCandidate F).carrierVariety) :=
  candidate_solvable_of_unipotent _ negativeUnipotent_isUnipotent

private lemma candidate_radical_of_unipotent (A : Set (Roots F))
    (hU : IsUnipotentAlgebraicGroup (rootGenerated F A).carrierVariety) :
    IsUnipotentRadicalOf (torusRootGenerated F A) (rootGenerated F A) := by
  have hc := torusRootGenerated_connected F A
  have hs := candidate_solvable_of_unipotent A hU
  obtain ⟨W, hW, _⟩ :=
    exists_unipotentRadical_of_connected_solvable (torusRootGenerated F A) hc hs
  have hUW : rootGenerated F A ≤ W :=
    hW.contains_unipotent_closedSubgroup hc hs
      (rootGenerated_le_torusRootGenerated F A) hU
  have hWU : W ≤ rootGenerated F A := by
    intro x hx
    obtain ⟨t, v, ht, hv, htv⟩ :=
      (mem_torusRootGenerated_iff F A x).mp (hW.1 hx)
    have htW : t ∈ W.toSubgroup := by
      have h := W.toSubgroup.mul_mem hx (W.toSubgroup.inv_mem (hUW hv))
      simpa only [htv, mul_inv_cancel_right] using h
    have ht1 : t = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← subtorus_inf_unipotent_eq_bot (F4Chevalley.splitTorus (k := F)) W
        F4Chevalley.splitTorus_isSubtorus hW.2.1]
      exact ⟨ht, htW⟩
    rw [htv, ht1, one_mul]
    exact hv
  have heq : W = rootGenerated F A :=
    SetLike.coe_injective (Set.Subset.antisymm hWU hUW)
  rwa [heq] at hW

/-- The positive root-generated group is exactly the candidate radical. -/
lemma positiveCandidate_unipotentRadical :
    IsUnipotentRadicalOf (positiveCandidate F) (positiveUnipotent F) :=
  candidate_radical_of_unipotent _ positiveUnipotent_isUnipotent

/-- The negative root-generated group is exactly the opposite candidate radical. -/
lemma negativeCandidate_unipotentRadical :
    IsUnipotentRadicalOf (negativeCandidate F) (negativeUnipotent F) :=
  candidate_radical_of_unipotent _ negativeUnipotent_isUnipotent

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
