module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ResidualAction
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Solvability of the actual marked local overgroup

The action of C_L(v) has two-group kernel and proper image in A₅: every
image fixes the marked vector v, whereas the displayed a-conjugator does
not. Thus C_L(v), its two-residual, and the extension of that residual by
the normalizing Sylow two-subgroup are solvable. These are properties of
the actual subgroups, rather than extra premises for Borel placement.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.926–927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The marking itself supplies solvability of C_L(v). -/
theorem marked_local_isSolvable (s : Marking L V) (hk : IsPGroup 2 s.action.ker) :
    Group.IsSolvable (L ⊓ Gv (markedV s) : Subgroup G) := by
  let D := L ⊓ Gv (markedV s)
  let f : D →* alternatingGroup (Fin 5) := s.action.comp (inclusion inf_le_left)
  have hf (c : D) : act (f c) v = v := by
    have he := s.equivariant (inclusion inf_le_left c) v
    have hc : MulAut.conj c.val (markedV s) = markedV s := by
      change c.val * markedV s * c.val⁻¹ = markedV s
      rw [mem_centralizer_singleton_iff.mp c.property.2, mul_inv_cancel_right]
    exact congrArg Multiplicative.toAdd (s.injective (he.symm.trans hc))
  have hproper : f.range ≠ ⊤ := by
    intro heq
    obtain ⟨c, hc⟩ := heq ▸ (show aConjugator ∈ (⊤ : Subgroup (alternatingGroup (Fin 5))) from trivial)
    have hfix := hc ▸ hf c
    have he := congrArg (fun x : Space => x.val 0) hfix
    exact (by decide : (act aConjugator v).val 0 ≠ v.val 0) he
  let : Group.IsSolvable f.range := alternatingGroup.isSolvable_subgroup_five_of_ne_top _ hproper
  let i : f.ker →* s.action.ker := {
    toFun x := ⟨inclusion inf_le_left x.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a : s.action.ker => a.val.val) h))
  let : Group.IsNilpotent f.ker := (hk.of_injective i hi).isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by simp)

/-- Solvability descends to the literal local residual in Gᵥ. -/
theorem residual_isSolvable (s : Marking L V) (hk : IsPGroup 2 s.action.ker) :
    Group.IsSolvable (residual s) := by
  let : Group.IsSolvable (L ⊓ Gv (markedV s) : Subgroup G) := marked_local_isSolvable s hk
  have hDL : Lv L (markedV s) ≤ L := (map_subtype_le _).trans inf_le_left
  let i : residual s →* (L ⊓ Gv (markedV s) : Subgroup G) := {
    toFun x := ⟨x.val.val, hDL x.property, x.val.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := i) (by
    intro x y h
    exact Subtype.ext (Subtype.ext
      (congrArg (fun a : (L ⊓ Gv (markedV s) : Subgroup G) => a.val) h)))

omit [Finite G] in
/-- T-normalization of L gives actual normalization of its local residual. -/
theorem localT_normalizes_residual (s : Marking L V) (T : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) :
    localT T (markedV s) ≤ normalizer (residual s : Set (Gv (markedV s))) := by
  have hnorm : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G) := by
    apply le_trans _ (normalizer_le_normalizer_characteristic_image
      (L ⊓ Gv (markedV s)) (pResidual 2 (L ⊓ Gv (markedV s) : Subgroup G)))
    exact (le_inf (inf_le_left.trans hTL) (inf_le_right.trans (Gv (markedV s)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  apply le_normalizer_iff.mpr
  intro t ht d hd
  exact le_normalizer_iff.mp hnorm t.val ⟨ht, t.property⟩ d.val hd

/-- The whole source solvable overgroup LᵥTᵥ, before taking its action image. -/
theorem residual_sup_localT_isSolvable (s : Marking L V) (T : Subgroup G)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (hT : IsPGroup 2 (localT T (markedV s))) :
    Group.IsSolvable (residual s ⊔ localT T (markedV s) : Subgroup (Gv (markedV s))) := by
  let D := residual s
  let P := localT T (markedV s)
  let A := D ⊔ P
  let : Group.IsSolvable D := residual_isSolvable s hk
  let : Group.IsNilpotent P := hT.isNilpotent
  let : (D.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le D.le_normalizer (localT_normalizes_residual s T hTL))
  let : Group.IsSolvable (D.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show D ≤ A from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show D ≤ A from le_sup_left)).injective
  let : Group.IsSolvable (P.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show P ≤ A from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show P ≤ A from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top (D.subgroupOf A) (P.subgroupOf A)
  apply map_injective A.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right,
    ← MonoidHom.range_eq_map, range_subtype]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
