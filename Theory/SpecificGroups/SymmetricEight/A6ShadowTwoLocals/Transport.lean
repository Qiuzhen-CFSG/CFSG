module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow

/-!
# Transport of the two block overgroups

Injective homomorphisms carry intrinsic two-cores to the cores of their
images and preserve the relative core-centralizer condition. Sylow conjugacy
then transports the standard pair of block stabilizers to any Sylow subgroup.

The assembly theorem in this module is conditional on the remaining
finite permutation calculations: maximality and characteristic two for
each standard overgroup.
Source: Aschbacher–Smith, Lemma 2.5.26, printed p.569.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup

variable {A B : Type*} [Group A] [Group B]

/-- The intrinsic core commutes with an injective change of ambient group. -/
theorem map_pCoreIn (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) (p : ℕ) :
    (H.pCoreIn p).map f = (H.map f).pCoreIn p := by
  let e : H ≃* H.map f := H.equivMapOfInjective f hf
  unfold Subgroup.pCoreIn
  rw [← pCore_map_iso p e, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- Characteristic two is an intrinsic property of the subgroup, so only
injectivity of the ambient homomorphism is needed. -/
theorem map_core_centralizer_le (f : A →* B) (hf : Function.Injective f)
    (H : Subgroup A) (p : ℕ)
    (hH : H ⊓ centralizer (H.pCoreIn p : Set A) ≤ H.pCoreIn p) :
    H.map f ⊓ centralizer ((H.map f).pCoreIn p : Set B) ≤ (H.map f).pCoreIn p := by
  rintro y ⟨⟨x, hx, rfl⟩, hc⟩
  rw [← map_pCoreIn f hf]
  apply mem_map_of_mem
  apply hH
  refine ⟨hx, ?_⟩
  intro z hz
  apply hf
  have hz' : f z ∈ (H.map f).pCoreIn p := by
    rw [← map_pCoreIn f hf]
    exact mem_map_of_mem f hz
  simpa only [map_mul] using hc (f z) hz'

theorem map_pCoreIn_ne_bot (f : A →* B) (hf : Function.Injective f)
    (H : Subgroup A) (p : ℕ) (hH : H.pCoreIn p ≠ ⊥) :
    (H.map f).pCoreIn p ≠ ⊥ := by
  rw [← map_pCoreIn f hf]
  exact fun h => hH ((Subgroup.map_eq_bot_iff_of_injective (H.pCoreIn p) hf).mp h)

/-- Every Sylow subgroup is contained in two proper generating overgroups
with nontrivial two-cores. This part needs no maximality or characteristic-two
calculation. -/
theorem exists_proper_generating_overgroups (P : Sylow 2 X) :
    ∃ L₁ L₂ : Subgroup X,
      L₁ ≠ ⊤ ∧ L₂ ≠ ⊤ ∧
      (P : Subgroup X) ≤ L₁ ∧ (P : Subgroup X) ≤ L₂ ∧ L₁ ⊔ L₂ = ⊤ ∧
      L₁.pCoreIn 2 ≠ ⊥ ∧ L₂.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X standardSylow P
  let e := MulAut.conj g
  have he : e.mapSubgroup standardTwoGroup = (P : Subgroup X) := by
    change ((g • standardSylow : Sylow 2 X) : Subgroup X) = (P : Subgroup X)
    rw [hg]
  have hproper (H : Subgroup X) (hH : H ≠ ⊤) : e.mapSubgroup H ≠ ⊤ := by
    intro hh
    apply hH
    apply e.mapSubgroup.injective
    rw [hh, e.mapSubgroup.map_top]
  refine ⟨e.mapSubgroup pairOvergroup, e.mapSubgroup fourOvergroup,
    hproper _ pairOvergroup_ne_top, hproper _ fourOvergroup_ne_top,
    he ▸ e.mapSubgroup.monotone standardSylow_le_pairOvergroup,
    he ▸ e.mapSubgroup.monotone standardSylow_le_fourOvergroup, ?_,
    map_pCoreIn_ne_bot e.toMonoidHom e.injective _ 2 pairOvergroup_pCoreIn_ne_bot,
    map_pCoreIn_ne_bot e.toMonoidHom e.injective _ 2 fourOvergroup_pCoreIn_ne_bot⟩
  rw [← e.mapSubgroup.map_sup, overgroups_sup, e.mapSubgroup.map_top]

/-- Conditional assembly from the specific standard block calculations.
Both characteristic-two/maximality premises still require
proof before this yields the source's unconditional geometry. -/
theorem exists_overgroups_of_standard
    (hpairMax : IsCoatom pairOvergroup) (hfourMax : IsCoatom fourOvergroup)
    (hpair : pairOvergroup ⊓ centralizer (pairOvergroup.pCoreIn 2 : Set X) ≤
      pairOvergroup.pCoreIn 2)
    (hfour : fourOvergroup ⊓ centralizer (fourOvergroup.pCoreIn 2 : Set X) ≤
      fourOvergroup.pCoreIn 2)
    (P : Sylow 2 X) :
    ∃ L₁ L₂ : Subgroup X,
      IsCoatom L₁ ∧ IsCoatom L₂ ∧
      (P : Subgroup X) ≤ L₁ ∧ (P : Subgroup X) ≤ L₂ ∧ L₁ ⊔ L₂ = ⊤ ∧
      (L₁ ⊓ centralizer (L₁.pCoreIn 2 : Set X) ≤ L₁.pCoreIn 2) ∧
      (L₂ ⊓ centralizer (L₂.pCoreIn 2 : Set X) ≤ L₂.pCoreIn 2) ∧
      L₁.pCoreIn 2 ≠ ⊥ ∧ L₂.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X standardSylow P
  let e := MulAut.conj g
  have he : e.mapSubgroup standardTwoGroup = (P : Subgroup X) := by
    change ((g • standardSylow : Sylow 2 X) : Subgroup X) = (P : Subgroup X)
    rw [hg]
  refine ⟨e.mapSubgroup pairOvergroup, e.mapSubgroup fourOvergroup,
    (e.mapSubgroup.isCoatom_iff _).mpr hpairMax,
    (e.mapSubgroup.isCoatom_iff _).mpr hfourMax,
    he ▸ e.mapSubgroup.monotone standardSylow_le_pairOvergroup,
    he ▸ e.mapSubgroup.monotone standardSylow_le_fourOvergroup, ?_,
    map_core_centralizer_le e.toMonoidHom e.injective _ 2 hpair,
    map_core_centralizer_le e.toMonoidHom e.injective _ 2 hfour,
    map_pCoreIn_ne_bot e.toMonoidHom e.injective _ 2 pairOvergroup_pCoreIn_ne_bot,
    map_pCoreIn_ne_bot e.toMonoidHom e.injective _ 2 fourOvergroup_pCoreIn_ne_bot⟩
  rw [← e.mapSubgroup.map_sup, overgroups_sup, e.mapSubgroup.map_top]

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
