module

public import Theory.Representation.BinaryNaturalDual.GeneratedCore
public import Theory.Representation.BinaryNaturalDual.Action

/-!
# Natural-plus-dual cores for block-unipotent radicals

For a subgroup of the unipotent radical at `U`, every pure natural vector
has its displacement in `U`, and every pure dual vector has its displacement
in the annihilator of `U`. Bounding these two dimensions puts both summands
in the generated core. Thus the core is the full natural-plus-dual space.

Rank-one transvections also identify the full radical's fixed space as
`U × ann(U)`, whose dimension is the dimension of the original natural space.
These calculations apply to arbitrary subspaces, without any chosen flag.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the radical
calculations in H.9.2(4–5) and H.9.3(4), printed pp.390–391. Classification
of arbitrary elementary actors as radical subgroups is a separate result.
-/

@[expose] public section

namespace BinaryNaturalDual
open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Small natural and dual displacement spaces generate the whole paired module. -/
theorem generatedCore_eq_top_of_le_radical [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ radical U)
    {k : ℕ} (hU : Module.finrank (ZMod 2) U ≤ k)
    (hUd : Module.finrank (ZMod 2) U.dualAnnihilator ≤ k) :
    generatedCore (naturalDualRepresentation.comp A.subtype) k = ⊤ := by
  apply top_unique
  intro v _
  have hfst : (v.1, 0) ∈ generatedCore (naturalDualRepresentation.comp A.subtype) k := by
    apply mem_generatedCore_of_displacement _ _
      (U.map (LinearMap.inl (ZMod 2) V (Module.Dual (ZMod 2) V)))
    · exact (Submodule.finrank_map_le _ _).trans hU
    · intro a
      refine ⟨a.val v.1 - v.1, (hA a.property).2 v.1, ?_⟩
      rw [MonoidHom.comp_apply, naturalDualRepresentation_apply]
      change (a.val v.1 - v.1, 0) = (a.val v.1 - v.1, a.val.symm.dualMap 0 - 0)
      simp
  have hsnd : (0, v.2) ∈ generatedCore (naturalDualRepresentation.comp A.subtype) k := by
    apply mem_generatedCore_of_displacement _ _
      (U.dualAnnihilator.map (LinearMap.inr (ZMod 2) V (Module.Dual (ZMod 2) V)))
    · exact (Submodule.finrank_map_le _ _).trans hUd
    · intro a
      refine ⟨a.val.symm.dualMap v.2 - v.2, ?_, ?_⟩
      · apply (Submodule.mem_dualAnnihilator _).mpr
        intro w hw
        change v.2 (a.val.symm w) - v.2 w = 0
        have hfix : a.val.symm w = w := ((radical U).inv_mem (hA a.property)).1 w hw
        rw [hfix, sub_self]
      · rw [MonoidHom.comp_apply, naturalDualRepresentation_apply]
        change (0, a.val.symm.dualMap v.2 - v.2) =
          (a.val 0 - 0, a.val.symm.dualMap v.2 - v.2)
        simp
  simpa using (generatedCore (naturalDualRepresentation.comp A.subtype) k).add_mem hfst hsnd

/-- The dual fixed space of a proper radical is its defining annihilator. -/
theorem dual_fixed_radical_iff (U : Submodule (ZMod 2) V) (hU : U ≠ ⊤)
    (f : Module.Dual (ZMod 2) V) :
    (∀ g ∈ radical U, g.symm.dualMap f = f) ↔ f ∈ U.dualAnnihilator := by
  constructor
  · intro hf
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hU)
    obtain ⟨q, hqx, hq⟩ := U.exists_le_ker_of_notMem hx
    have hq1 : q x = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hqx
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro w hw
    have he := LinearMap.congr_fun
      (hf (transvection w q (hq hw)) (transvection_mem hw hq)) x
    change f (x + q x • w) = f x at he
    simpa [hq1] using he
  · intro hf g hg
    ext x
    change f (g.symm x) = f x
    have h := (Submodule.mem_dualAnnihilator f).mp hf (g.symm x - x)
      (((radical U).inv_mem hg).2 x)
    simpa only [map_sub, sub_eq_zero] using h

/-- The full radical fixes exactly the product of its defining space and annihilator. -/
theorem fixedSpace_radical (U : Submodule (ZMod 2) V) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    Representation.BinaryOffender.fixedSpace
      (naturalDualRepresentation.comp (radical U).subtype) ⊤ = U.prod U.dualAnnihilator := by
  ext v
  change (∀ g : (⊤ : Subgroup (radical U)),
    NaturalDualFlag.action g.val.val v = v) ↔ v.1 ∈ U ∧ v.2 ∈ U.dualAnnihilator
  constructor
  · intro h
    refine ⟨(mem_iff_fixed_radical hU _).mpr ?_, (dual_fixed_radical_iff U hUt _).mp ?_⟩
    · intro g hg
      exact (NaturalDualFlag.action_fst g v).symm.trans
        (congrArg Prod.fst (h ⟨⟨g, hg⟩, Subgroup.mem_top _⟩))
    · intro g hg
      ext x
      exact (NaturalDualFlag.action_snd g v x).symm.trans
        (LinearMap.congr_fun (congrArg Prod.snd
          (h ⟨⟨g, hg⟩, Subgroup.mem_top _⟩)) x)
  · rintro ⟨hx, hf⟩ g
    apply Prod.ext
    · rw [NaturalDualFlag.action_fst]
      exact g.val.property.1 _ hx
    · ext x
      rw [NaturalDualFlag.action_snd]
      exact LinearMap.congr_fun
        ((dual_fixed_radical_iff U hUt _).mpr hf g.val.val g.val.property) x

/-- The radical fixed space has dimension equal to the natural degree. -/
theorem finrank_prod_dualAnnihilator [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (U.prod U.dualAnnihilator) = Module.finrank (ZMod 2) V := by
  let e : (U × U.dualAnnihilator) ≃ₗ[ZMod 2] U.prod U.dualAnnihilator := {
    toFun w := ⟨(w.1.val, w.2.val), w.1.property, w.2.property⟩
    invFun w := (⟨w.val.1, w.property.1⟩, ⟨w.val.2, w.property.2⟩)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  rw [← e.finrank_eq, Module.finrank_prod]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq U

/-- A radical at a three-space in degree five has full generated core at corank three,
as does every subgroup of that radical. -/
theorem generatedCore_five_radical [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 5)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ radical U) :
    generatedCore (naturalDualRepresentation.comp A.subtype) 3 = ⊤ := by
  apply generatedCore_eq_top_of_le_radical U A hA (by omega)
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega

/-- A radical at a two-space in degree four has full generated core at corank two,
as does every subgroup of that radical. -/
theorem generatedCore_four_radical [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 4)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 2)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ radical U) :
    generatedCore (naturalDualRepresentation.comp A.subtype) 2 = ⊤ := by
  apply generatedCore_eq_top_of_le_radical U A hA (by omega)
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega

end BinaryNaturalDual
