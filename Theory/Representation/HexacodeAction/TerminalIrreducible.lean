module

public import Theory.Representation.HexacodeAction.Field
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility of the concrete terminal hexacode model

The even group is perfect. Consequently the determinant of its action on
any invariant field subspace is one. Its central cubic generator acts as
multiplication by the primitive scalar omega, so the subspace dimension
is zero or three. Every invariant binary subspace is stable under this
generator and hence under all four field scalars. This proves binary
irreducibility for both the even cover and the full hexacode group.

These are model eligibility facts for the terminal action recognition.
They do not classify arbitrary six-dimensional representations or identify
their extensions across the odd coset.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453, and the terminal use on p.1155. The concrete code and cover
are the licensed ATLAS ports documented in `HexacodeAction.Cover`; the
field realization is `HexacodeAction.Field`.
-/

@[expose] public section

open Atlas.Codes

namespace Representation.Hexacode

/-- The even cover is intrinsically the commutator subgroup of the full group.
The sign kills all commutators, and perfectness gives the reverse inclusion. -/
theorem commutator_eq_even : commutator HexAutomorphisms = hexSign.ker := by
  apply le_antisymm
  · exact Abelianization.commutator_subset_ker hexSign
  · let _ : Group.IsPerfect HexEvenAutomorphisms := even_isPerfect
    have h := hexSign.ker.map_subtype_commutator
    rw [Group.IsPerfect.commutator_eq_top] at h
    have hm : (⊤ : Subgroup HexEvenAutomorphisms).map hexSign.ker.subtype = hexSign.ker := by
      ext x
      simp
    rw [hm] at h
    exact h.trans_le (Subgroup.commutator_mono le_top le_top)

/-- Changing the actor coordinates by an automorphism preserves the even cover. -/
theorem even_map_automorphism (a : MulAut HexAutomorphisms) :
    hexSign.ker.map a.toMonoidHom = hexSign.ker := by
  calc
    _ = (commutator HexAutomorphisms).map a.toMonoidHom :=
      congrArg (Subgroup.map a.toMonoidHom) commutator_eq_even.symm
    _ = commutator HexAutomorphisms := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.surjective]
      rfl
    _ = _ := commutator_eq_even

/-- The field-linear even action, expressed as a representation. -/
noncomputable def evenFieldRepresentation : Representation F HexEvenAutomorphisms hexacode :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp evenFieldAction

/-- Restriction of the binary code action to the actual even cover. -/
def evenAction : Representation Bit HexEvenAutomorphisms hexacode :=
  action.comp hexSign.ker.subtype

private theorem determinant_one {W : Type*} [AddCommGroup W] [Module F W]
    (σ : Representation F HexEvenAutomorphisms W) (g : HexEvenAutomorphisms) :
    LinearMap.det (σ g) = 1 := by
  let f : HexEvenAutomorphisms →* Fˣ := MonoidHom.toHomUnits (LinearMap.det.comp σ)
  let _ : Group.IsPerfect HexEvenAutomorphisms := even_isPerfect
  let _ : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (⟨f g, ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : f.range => (x.val : F)) h

/-- Every invariant field subspace has dimension zero or three: its scalar
operator has determinant one because the even group is perfect. -/
theorem evenFieldRepresentation_isIrreducible : IsIrreducible evenFieldRepresentation := by
  have : Nontrivial hexacode := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank F hexacode by rw [field_finrank]; decide)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let _ : Module.Free F P.toSubmodule := Module.Free.of_divisionRing F P.toSubmodule
  have hs : P.toRepresentation hexEvenZ = omega • (1 : Module.End F P.toSubmodule) := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact scalar_eq_omega_smul w.val
  have hd := determinant_one (W := P.toSubmodule) P.toRepresentation hexEvenZ
  rw [hs, LinearMap.det_smul, map_one, mul_one] at hd
  have hn : Module.finrank F P.toSubmodule ≤ 3 := by
    simpa only [field_finrank] using P.toSubmodule.finrank_le
  have he : Module.finrank F P.toSubmodule = 0 ∨ Module.finrank F P.toSubmodule = 3 := by
    interval_cases h : Module.finrank F P.toSubmodule
    · exact Or.inl rfl
    · exact False.elim ((by decide : (omega : F) ^ 1 ≠ 1) hd)
    · exact False.elim ((by decide : (omega : F) ^ 2 ≠ 1) hd)
    · exact Or.inr rfl
  rcases he with h | h
  · left
    exact Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (Submodule.eq_top_of_finrank_eq (h.trans field_finrank.symm))

/-- A binary invariant subspace is scalar-stable, hence a field subspace.
The even hexacode group therefore acts irreducibly over the binary field. -/
theorem evenAction_isIrreducible : IsIrreducible evenAction := by
  have : Nontrivial hexacode := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank Bit hexacode by rw [hexacode_finrank]; decide)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  have hP : hexZ ∈ BinaryOffender.subspaceStabilizer action P.toSubmodule :=
    BinaryOffender.le_subspaceStabilizer action P.toSubmodule
      (fun g hg _ hw => P.apply_mem_toSubmodule ⟨g, hg⟩ hw) hexSign_Z
  let Q : Subrepresentation evenFieldRepresentation :=
    ⟨scalarSubmodule P.toSubmodule hP, fun g _ hw => P.apply_mem_toSubmodule g hw⟩
  rcases evenFieldRepresentation_isIrreducible.eq_bot_or_eq_top Q with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro w hw
    have hq : w ∈ Q := hw
    rw [h] at hq
    exact hq
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro w _
    have hq : w ∈ Q := by rw [h]; trivial
    exact hq

/-- Irreducibility on the even subgroup implies irreducibility on the full group. -/
theorem action_isIrreducible : IsIrreducible action := by
  have : Nontrivial hexacode := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank Bit hexacode by rw [hexacode_finrank]; decide)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let Q : Subrepresentation evenAction :=
    ⟨P.toSubmodule, fun g _ hw => P.apply_mem_toSubmodule g.val hw⟩
  rcases evenAction_isIrreducible.eq_bot_or_eq_top Q with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun R : Subrepresentation evenAction => R.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun R : Subrepresentation evenAction => R.toSubmodule) h)

end Representation.Hexacode
