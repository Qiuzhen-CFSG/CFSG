module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Setup
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary

/-!
# Removing the central cover in K.3.4

Odd-primary transfer for the actual symplectic matrix group makes the center
of a perfect cover a two-group. A normal two-subgroup acts trivially on an
irreducible binary representation, so faithfulness kills that center.
The resulting equivalence retains the given central quotient map.

This proves the first reduction on printed p.456 of Aschbacher–Smith,
K.3.4, without assuming simplicity of the cover or a multiplier table.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour

variable {F E V : Type*} [Field F] [Finite F] [CharP F 2]
  [Group E] [Finite E] [Group.IsPerfect E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The literal central quotient makes the center a two-group. -/
theorem center_isTwoGroup (e : E ⧸ center E ≃* Sp F) : IsPGroup 2 (center E) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hprime⟩
  have heq : p = 2 := by
    by_contra hn
    have he := CentralCovers.OddPrimary.not_dvd_card_kernel hn f hf hk.le
    rw [hk] at he
    exact he (Nat.dvd_of_mem_primeFactors hp)
  simp [heq, Nat.prime_two]

/-- Faithful irreducibility removes the entire central kernel. -/
theorem center_eq_bot (ρ : Representation (ZMod 2) E V) [IsIrreducible ρ]
    (hfaith : Function.Injective ρ) (e : E ⧸ center E ≃* Sp F) : center E = ⊥ := by
  have hk := normal_p_subgroup_le_ker ρ (center E) (center_isTwoGroup e)
  rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hfaith] at hk
  exact le_bot_iff.mp hk

/-- The isomorphism uses the original quotient map, not an unmarked group label. -/
@[expose] noncomputable def coverEquiv (ρ : Representation (ZMod 2) E V) [IsIrreducible ρ]
    (hfaith : Function.Injective ρ) (e : E ⧸ center E ≃* Sp F) : E ≃* Sp F :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (center E)))
    ⟨e.injective.comp ((MonoidHom.ker_eq_bot_iff _).mp
      ((QuotientGroup.ker_mk' _).trans (center_eq_bot ρ hfaith e))),
      e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

/-- Compatibility with the literal central quotient. -/
theorem coverEquiv_apply (ρ : Representation (ZMod 2) E V) [IsIrreducible ρ]
    (hfaith : Function.Injective ρ) (e : E ⧸ center E ≃* Sp F) (x : E) :
    coverEquiv ρ hfaith e x = e (QuotientGroup.mk' (center E) x) := rfl

omit [Group.IsPerfect E] in
/-- A quasisimple cover with this faithful binary action is simple. -/
theorem cover_isSimple [IsQuasisimple E] (ρ : Representation (ZMod 2) E V)
    [IsIrreducible ρ] (hfaith : Function.Injective ρ)
    (e : E ⧸ center E ≃* Sp F) : IsSimpleGroup E := by
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : IsSimpleGroup (Sp F) := e.symm.isSimpleGroup
  exact (coverEquiv ρ hfaith e).isSimpleGroup

variable {G : Type*} [Group G] [Finite G]

/-- Application to the actual generalized Fitting subgroup in Chapter K. -/
theorem source_cover_isSimple {K : GroupClass} {ρ : Representation (ZMod 2) G V}
    {L : Subgroup G} (h : SourceHypothesis K ρ L)
    (e : L ⧸ center L ≃* Sp F) :
    center L = ⊥ ∧ IsSimpleGroup L ∧ Nonempty (L ≃* Sp F) := by
  let : IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hf : Function.Injective (ρ.comp L.subtype) := h.faithful.comp Subtype.val_injective
  exact ⟨center_eq_bot _ hf e, cover_isSimple _ hf e, ⟨coverEquiv _ hf e⟩⟩

end CFSG.Quasithin.ChapterK.Symplectic
