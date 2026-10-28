module

public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Borel
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Solvable Sylow two-normalizers in derived G₂

For every finite field F of characteristic two, put D = G₂(F)′. The
positive-root Sylow subgroup U restricts to a Sylow subgroup of D, and its
normalizer in D is exactly B ∩ D, where B is the concrete root-defined
Borel. Borel solvability and Sylow conjugacy give solvability for every
Sylow two-normalizer in D.

Above field order two, perfectness identifies D with the full octonion
automorphism group. At order two, the separate binary calculation is
transported coefficientwise, preserving both U and the commutator subgroup,
before restricting the normalizer to D. In particular this argument does
not require a simplicity or quasisimplicity certificate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.4.2(4), printed p.86; B.5.5(1)(iv) and B.5.6,
printed pp.104–105; and the Borel in the proof of 15.3.49(k), printed p.1144.
The octonion model and root computations are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.DerivedNormalizerSolvable
open Subgroup LieParabolicSetup
variable {F K : Type*} [Field F] [Field K]

/-- Field transport preserves the intersection with the actual commutator. -/
theorem field_map_derivedUnipotent (e : F ≃+* K) :
    (unipotent ⊓ commutator (Model F)).map (fieldEquiv e).toMonoidHom =
      unipotent ⊓ commutator (Model K) := by
  rw [map_inf _ _ _ (fieldEquiv e).injective, SylowNormalizer.field_map_unipotent,
    map_commutator_eq, MonoidHom.range_eq_top.mpr (fieldEquiv e).surjective]
  rfl

/-- The ambient normalizer of the restricted positive roots is the Borel. -/
theorem normalizer_derivedUnipotent [Finite F] [CharP F 2] :
    normalizer ((unipotent ⊓ commutator (Model F) : Subgroup (Model F)) :
      Set (Model F)) = borel := by
  by_cases hq : Nat.card F = 2
  · let _ := Fintype.ofFinite F
    let k : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hq)).symm
    let e := fieldEquiv k
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_equiv_normalizer_eq]
    have hR : (unipotent ⊓ commutator (Model F)).map e.toMonoidHom =
        BinaryParabolicPair.derivedSylowAmbient := field_map_derivedUnipotent k
    rw [hR, binary_normalizer_derivedSylowAmbient,
      borel_eq_unipotent_of_card_two hq]
    exact (SylowNormalizer.field_map_unipotent k).symm
  · let : Group.IsPerfect (Model F) := isPerfect (by
      have := Finite.one_lt_card (α := F)
      omega)
    rw [Group.IsPerfect.commutator_eq_top, inf_top_eq]
    exact SylowNormalizer.normalizer_unipotent

/-- The normalizer inside the derived carrier is the restricted Borel. -/
theorem normalizer_restricted_unipotent [Finite F] [CharP F 2] :
    normalizer (unipotent.subgroupOf (commutator (Model F)) :
      Set (commutator (Model F))) = borel.subgroupOf (commutator (Model F)) := by
  rw [← inf_subgroupOf_right unipotent (commutator (Model F)),
    ← subgroupOf_normalizer_eq inf_le_right, normalizer_derivedUnipotent]

/-- All Sylow two-normalizers of the derived octonion model are solvable. -/
theorem isSolvable_normalizer [Finite F] [CharP F 2]
    (S : Sylow 2 (commutator (Model F))) :
    Group.IsSolvable (normalizer (S : Set (commutator (Model F)))) := by
  let D := commutator (Model F)
  obtain ⟨P, hP⟩ := (sylow (F := F)).exists_subgroupOf_eq_of_normal D
  have hN : normalizer (P : Set D) = borel.subgroupOf D := by
    change normalizer ((P : Subgroup D) : Set D) = _
    rw [hP, sylow_coe]
    exact normalizer_restricted_unipotent
  let : Group.IsSolvable (borel (K := F)) := isSolvable_borel
  let : Group.IsSolvable (normalizer (P : Set D)) := by
    rw [hN]
    apply Group.isSolvable_of_isSolvable_injective (f := D.subtype.subgroupComap borel)
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : borel (K := F) => z.val) h))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P S
  have hS : (P : Subgroup D).map (MulAut.conj g).toMonoidHom =
      (S : Subgroup D) := congrArg Sylow.toSubgroup hg
  change Group.IsSolvable (normalizer ((S : Subgroup D) : Set D))
  rw [← hS, ← map_equiv_normalizer_eq]
  exact Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)

/-- The power-of-two parameter form used by the concrete model catalogue. -/
theorem isSolvable_normalizer_of_card [Finite F] {e : ℕ} (_he : 1 ≤ e)
    (hcard : Nat.card F = 2 ^ e) (S : Sylow 2 (commutator (Model F))) :
    Group.IsSolvable (normalizer (S : Set (commutator (Model F)))) := by
  let _ := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact isSolvable_normalizer S

end Atlas.G2.DerivedNormalizerSolvable
