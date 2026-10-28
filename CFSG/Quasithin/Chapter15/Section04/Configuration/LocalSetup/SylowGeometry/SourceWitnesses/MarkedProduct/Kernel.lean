module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Action
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The kernel of the original marked product action

The restricted X action has kernel O₂(X), by the original member projection.
A two-group supplement makes the kernel on XS an extension of two-groups.
Surjectivity onto the centerless symmetric-three product then identifies this
kernel with O₂(XS). Restriction to a normal factor preserves its actual core.

Source: Aschbacher–Smith, 15.4.12(6) and 15.4.20, pp.1160–1164.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

omit [Finite G] in
theorem SourceAction.member_action (d : SourceAction T M X) :
    vectorAction.comp (d.actor.comp (inclusion d.member_le)) =
      (MulAut.congr d.coordinates).toMonoidHom.comp
        (d.cubic_actor.comp (memberProjection M X d.member_le)) := by
  apply MonoidHom.ext
  intro x
  apply MulEquiv.ext
  intro v
  apply d.coordinates.symm.injective
  apply Subtype.ext
  have ha := d.intertwines (inclusion d.member_le x) (d.coordinates.symm v)
  rw [d.coordinates.apply_symm_apply] at ha
  change _ = (d.coordinates.symm (d.coordinates
    (d.cubic_actor (memberProjection M X d.member_le x) (d.coordinates.symm v))) : G)
  rw [d.coordinates.symm_apply_apply]
  exact ha.trans (d.cubic_conjugation x (d.coordinates.symm v)).symm

theorem SourceAction.member_kernel (d : SourceAction T M X) (h : Input K T M X 2) :
    (d.actor.comp (inclusion d.member_le)).ker = pCore 2 X := by
  have he := congrArg MonoidHom.ker d.member_action
  rw [MonoidHom.ker_comp_of_injective _ _ vectorAction_injective,
    MonoidHom.ker_comp_of_injective (d.cubic_actor.comp (memberProjection M X d.member_le))
      (MulAut.congr d.coordinates).toMonoidHom (MulAut.congr d.coordinates).injective,
    MonoidHom.ker_comp_of_injective (memberProjection M X d.member_le) d.cubic_actor d.cubic_faithful] at he
  rw [he]
  obtain ⟨e,heq⟩ := member_quotient_compatible d.member_le h.normal
  have he' : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)) =
      memberProjection M X d.member_le := by
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (heq x)
  rw [←he', MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

omit [Finite G] in
theorem restricted_kernel_eq_core {B : Type*} [Group B]
    (L H : Subgroup G) (hLH : L ≤ H) (hn : H ≤ normalizer (L : Set G))
    (f : H →* B) (hf : f.ker = pCore 2 H) :
    (f.comp (inclusion hLH)).ker = pCore 2 L := by
  apply le_antisymm
  · have he : (f.comp (inclusion hLH)).ker = (pCore 2 H).comap (inclusion hLH) := by
      change f.ker.comap (inclusion hLH) = _
      rw [hf]
    rw [he]
    exact le_sSup ⟨inferInstance,
      pCore_isPGroup.comap_of_injective (inclusion hLH) (inclusion_injective hLH)⟩
  · have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans hLH)
      (hn.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    intro x hx
    obtain ⟨y,hy,he⟩ := hc (mem_map.mpr ⟨x,hx,rfl⟩)
    have hyx : y = inclusion hLH x := Subtype.ext he
    rw [hyx] at hy
    exact hf.ge hy

omit [Finite G] in
theorem image_card_of_restricted_kernel {B : Type*} [Group B]
    (L H : Subgroup G) (hLH : L ≤ H) (f : H →* B)
    (hf : (f.comp (inclusion hLH)).ker = pCore 2 L) :
    Nat.card ((L.subgroupOf H).map f) = Nat.card (L ⧸ pCore 2 L) := by
  let g := f.comp (inclusion hLH)
  have e := QuotientGroup.quotientKerEquivRange g
  have he := Nat.card_congr e.toEquiv
  rw [hf, MonoidHom.range_comp, inclusion_range] at he
  exact he.symm

omit [Finite G] in
private theorem join_action_kernel_isPGroup
    {H : Type*} [Group H] (X S : Subgroup G) (hn : S ≤ normalizer (X : Set G))
    (hS : IsPGroup 2 S) (f : (X ⊔ S : Subgroup G) →* H)
    (hf : (f.comp (inclusion le_sup_left)).ker = pCore 2 X) : IsPGroup 2 f.ker := by
  let U := X ⊔ S
  let N := X.subgroupOf U
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le X.le_normalizer hn)
  have hgen : N ⊔ S.subgroupOf U = ⊤ := by
    apply map_injective U.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (U ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (S.subgroupOf U) hS.comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* X :=
      (U.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict X (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 X := by
      intro x
      exact hf.le x.val.property
    let r' : q.ker →* pCore 2 X := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 X => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

theorem SourceAction.join_kernel_isPGroup (d : SourceAction T M X) (h : Input K T M X 2) :
    IsPGroup 2 (d.actor.comp (inclusion (sup_le d.member_le
      (inf_le_left.trans h.sylow_le : ChapterB.baumann (T : Subgroup G) ≤ M)))).ker := by
  apply join_action_kernel_isPGroup X (ChapterB.baumann (T : Subgroup G))
    (inf_le_left.trans (YFamily.invariant h.member)) (T.isPGroup'.to_le inf_le_left)
  exact d.member_kernel h

theorem product_twoCore_eq_bot : pCore 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = ⊥ := by
  have hc : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have he := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa using he.symm
  rw [pCore_prod, hc, bot_prod_bot]

theorem product_kernel_eq_core
    {H : Type*} [Group H] [Finite H]
    (f : H →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) : f.ker = pCore 2 H := by
  have he := f.comap_pCore_of_ker_isPGroup hf hk
  rw [product_twoCore_eq_bot, MonoidHom.comap_bot] at he
  exact he

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
