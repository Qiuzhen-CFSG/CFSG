module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The two-core of a full elementary normalizer

If the ambient normalizer of an elementary abelian two-group induces all
its automorphisms, its two-core equals the two-core of the full centralizer.
The automorphism group has trivial two-core, so the normalizer's two-core
acts trivially. Normal restriction and characteristic-core normalization
then give both containments. The full centralizer kernel is retained.
-/

public section
open Subgroup
open scoped IsMulCommutative

/-- The full automorphism group of a finite elementary two-group has trivial two-core. -/
theorem MulAut.twoCore_eq_bot_of_elementary_two
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E] :
    pCore 2 (MulAut E) = ⊥ := by
  let e : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      invFun := fun a => MulEquiv.toAdditive.symm a.toAddEquiv
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intro a b; ext; rfl }
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso]
  exact BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot

/-- A full elementary automorphism action identifies the normalizer two-core
with the two-core of its full centralizer kernel. -/
theorem Subgroup.normalizer_twoCore_eq_centralizer_twoCore_of_full_action {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hfull : Function.Surjective U.normalizerMonoidHom) :
    (normalizer (U : Set G)).pCoreIn 2 = (centralizer (U : Set G)).pCoreIn 2 := by
  let A := normalizer (U : Set G)
  let C := centralizer (U : Set G)
  have hCA : C ≤ A := Subgroup.centralizer_le_normalizer _
  have hAC : A ≤ normalizer (C : Set G) := normalizer_le_normalizer_centralizer U
  have hmap : (pCore 2 A).map U.normalizerMonoidHom ≤ pCore 2 (MulAut U) :=
    le_sSup ⟨Normal.map inferInstance U.normalizerMonoidHom hfull,
      pCore_isPGroup.map U.normalizerMonoidHom⟩
  rw [MulAut.twoCore_eq_bot_of_elementary_two U] at hmap
  have hcoreC : A.pCoreIn 2 ≤ C := by
    rintro x ⟨a, ha, rfl⟩
    have hk : a ∈ U.normalizerMonoidHom.ker :=
      hmap (mem_map_of_mem U.normalizerMonoidHom ha)
    rwa [normalizerMonoidHom_ker] at hk
  exact le_antisymm
    ((le_inf hcoreC le_rfl).trans (inf_pCoreIn_le_of_le 2 hCA))
    (pCoreIn_mono_of_normalizes hCA hAC)

end
