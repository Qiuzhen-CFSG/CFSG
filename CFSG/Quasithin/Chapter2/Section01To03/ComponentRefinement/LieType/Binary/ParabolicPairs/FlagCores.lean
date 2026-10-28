module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection

/-!
# Two-cores of the binary flag stabilizers

For any subspace W in a proper flag, the radical of W fixes every subspace
in that flag: each is either contained in W or contains W. Thus the radical
is normal relative to the flag stabilizer, and its centralizer is contained
in itself. This proves that the intrinsic flag stabilizer has characteristic
two. If the stabilizer contains a component Sylow subgroup, its two-core
also contains every element centralizing that Sylow subgroup, in particular
the source's involution projection.

These intrinsic assertions supply inputs for the ambient overgroups in
Aschbacher–Smith 2.3.9(7), printed pp.525–526. They do not by themselves
establish characteristic two after adjoining all of S.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} [NeZero n]

/-- The actual block-unipotent radical, transported to the component. -/
noncomputable def subspaceRadical (e : L ≃* PSL n) (W : Space n) : Subgroup L :=
  (BinaryLinear.radical W).comap (linearModel e).toMonoidHom

omit [NeZero n] in
private theorem radical_le_comparable_parabolic (W W' : Space n)
    (h : W ≤ W' ∨ W' ≤ W) : BinaryLinear.radical W ≤ BinaryLinear.parabolic W' := by
  intro x hx v
  rcases h with h | h
  · constructor
    · intro hv
      have he := W'.sub_mem hv (h (hx.2 v))
      simpa using he
    · intro hv
      simpa only [sub_add_cancel] using (W'.add_mem (h (hx.2 v)) hv)
  · constructor
    · intro hv
      have he : x v = v := x.injective (hx.1 (x v) (h hv))
      rwa [he] at hv
    · intro hv
      rwa [hx.1 v (h hv)]

theorem subspaceRadical_le_flagStabilizer (e : L ≃* PSL n) (F : Flag n)
    {W : Space n} (hW : W ∈ F.spaces) : subspaceRadical e W ≤ flagStabilizer e F := by
  intro x hx
  rw [mem_flagStabilizer]
  intro W' hW'
  exact radical_le_comparable_parabolic W W' (F.chain W hW W' hW') hx

theorem subspaceRadical_isPGroup (e : L ≃* PSL n) (W : Space n) :
    IsPGroup 2 (subspaceRadical e W) := by
  rw [subspaceRadical, Subgroup.comap_equiv_eq_map_symm']
  exact (BinaryLinear.radical_two W).map (linearModel e).symm.toMonoidHom

theorem flagStabilizer_normalizes_subspaceRadical (e : L ≃* PSL n) (F : Flag n)
    {W : Space n} (hW : W ∈ F.spaces) :
    flagStabilizer e F ≤ normalizer (subspaceRadical e W : Set L) := by
  rw [le_set_normalizer_iff]
  intro x hx r hr
  have hxW : linearModel e x ∈ BinaryLinear.parabolic W :=
    (mem_flagStabilizer e F x).mp hx W hW
  have hn := BinaryLinear.parabolic_le_normalizer W hxW
  change linearModel e (x * r * x⁻¹) ∈ BinaryLinear.radical W
  simpa only [map_mul, map_inv, SetLike.mem_coe] using (hn (linearModel e r)).mp hr

theorem centralizer_subspaceRadical_le (e : L ≃* PSL n) {W : Space n}
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) :
    centralizer (subspaceRadical e W : Set L) ≤ subspaceRadical e W := by
  intro x hx
  apply BinaryLinear.centralizer_radical_le hW hWt
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨y, rfl⟩ := (linearModel e).surjective y
  change linearModel e y * linearModel e x = linearModel e x * linearModel e y
  simpa only [map_mul] using congrArg (linearModel e) (mem_centralizer_iff.mp hx y hy)

/-- Every proper binary flag stabilizer has self-centralizing two-core. -/
theorem flagStabilizer_selfCentralizingCore (e : L ≃* PSL n) (F : Flag n) :
    centralizer (pCore 2 (flagStabilizer e F) : Set (flagStabilizer e F)) ≤
      pCore 2 (flagStabilizer e F) := by
  obtain ⟨W, hW⟩ := F.nonempty
  exact centralizer_pCore_le_of_normalized 2 (subspaceRadical e W) (flagStabilizer e F)
    (subspaceRadical_isPGroup e W) (subspaceRadical_le_flagStabilizer e F hW)
    (flagStabilizer_normalizes_subspaceRadical e F hW)
    (centralizer_subspaceRadical_le e (F.proper W hW).1 (F.proper W hW).2)

/-- A centralizer of the component Sylow lies in the flag stabilizer's intrinsic two-core. -/
theorem central_sylow_mem_flagStabilizer_core (e : L ≃* PSL n) (F : Flag n)
    (T : Sylow 2 L) (hT : (T : Subgroup L) ≤ flagStabilizer e F) {t : L}
    (hc : ∀ x : L, x ∈ T → x * t = t * x) :
    t ∈ (flagStabilizer e F).pCoreIn 2 := by
  obtain ⟨W, hW⟩ := F.nonempty
  have hnorm := flagStabilizer_normalizes_subspaceRadical e F hW
  have hp := subspaceRadical_isPGroup e W
  have hRT : subspaceRadical e W ≤ (T : Subgroup L) := by
    have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hp
      (hT.trans hnorm)) le_sup_left
    exact he ▸ le_sup_right
  have htR : t ∈ subspaceRadical e W :=
    centralizer_subspaceRadical_le e (F.proper W hW).1 (F.proper W hW).2
      (mem_centralizer_iff.mpr (fun x hx => hc x (hRT hx)))
  exact le_pCoreIn_of_normalizes hp (subspaceRadical_le_flagStabilizer e F hW) hnorm htR

/-- The source projection belongs to the intrinsic core of every flag
stabilizer containing the actual component Sylow intersection. -/
theorem projection_mem_flagStabilizer_core {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2)
    (F : Flag n)
    (hF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F) :
    t ∈ (flagStabilizer e F).pCoreIn 2 := by
  obtain ⟨T, hT⟩ := exists_component_sylow h
  apply central_sylow_mem_flagStabilizer_core e F T (hT.symm ▸ hF)
  exact (projection_mem_center_component_sylow h e ht ht2 T hT).2

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
