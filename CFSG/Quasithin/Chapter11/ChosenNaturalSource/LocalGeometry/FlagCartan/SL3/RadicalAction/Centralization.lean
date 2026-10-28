module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The original SL₃ plane radical and its action kernel

The actual action of L₂T on V₂ is irreducible over the binary field, by the
proved natural SL₂ plane action. A normal two-subgroup therefore fixes this
plane. Conversely, the action kernel intersects L₂ in O₂(L₂), while its
remaining quotient embeds in L₂T/L₂. It is consequently a two-group and is
exactly O₂(L₂T). This identifies C_T(V₂) with the literal source radical R₂.
All actions here are original ambient conjugation, on the original V₂.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770 of
`refs/quasithin.pdf`. The shear and commutator applications follow in Action
and Identities.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction
open PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

def localJoin : Subgroup G := (flag D S m).Li 1 ⊔ (T : Subgroup G)

theorem localJoin_normalizes_plane : localJoin D S m ≤ normalizer ((flag D S m).Vi 1 : Set G) :=
  sup_le ((localResidual_le _).trans inf_le_right) ((flag D S m).invariant 1)

/-- The original conjugation action of L₂T on the actual plane. -/
def joinPlaneAction : Representation (ZMod 2) (localJoin D S m) (Additive ((flag D S m).Vi 1)) :=
  (Components.flagAction (flag D S m) 1).comp (inclusion (localJoin_normalizes_plane D S m))

theorem joinPlaneAction_irreducible : (joinPlaneAction D S m).IsIrreducible := by
  let : Nontrivial (Additive ((flag D S m).Vi 1)) :=
    (planeEquiv D S m).toEquiv.nontrivial
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hz : W = ⊥
  · exact Or.inl hz
  right
  have hz' : W.toSubmodule ≠ ⊥ := fun h => hz (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz'
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ W.toSubmodule.zero_mem
  obtain ⟨l,hl⟩ := plane_nonzero_transitive D S m v w hv0 hw
  exact hl ▸ W.apply_mem_toSubmodule (⟨l,mem_sup_left l.property⟩ : localJoin D S m) hv

/-- The normal two-core fixes the entire irreducible plane. -/
theorem radical_centralizes_plane :
    (flag D S m).Ri 1 ≤ centralizer ((flag D S m).Vi 1 : Set G) := by
  let ρ := joinPlaneAction D S m
  let := joinPlaneAction_irreducible D S m
  have hk := normal_p_subgroup_le_ker ρ (pCore 2 (localJoin D S m)) pCore_isPGroup
  rintro x ⟨a,ha,rfl⟩ v hv
  have he := LinearMap.congr_fun (hk ha) (Additive.ofMul ⟨v,hv⟩)
  have he' := congrArg (fun w : Additive ((flag D S m).Vi 1) => (w.toMul : G)) he
  change (a : G) * v * (a : G)⁻¹ = v at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

private theorem plane_core_of_fixes (l : (flag D S m).Li 1)
    (hl : ∀ v, Components.flagAction (flag D S m) 1
      ⟨l,(localResidual_le _ l.property).2⟩ v = v) :
    l ∈ pCore 2 ((flag D S m).Li 1) := by
  rw [← planeProjection_ker D S m]
  change planeProjection D S m l = 1
  apply specialLinearNatural_injective 2
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := (planeEquiv D S m).surjective w
  rw [← planeEquiv_intertwines,hl,map_one,Module.End.one_apply]

/-- The kernel is a two-group: its intersection with L₂ is O₂(L₂),
and its remaining quotient embeds in L₂T/L₂. -/
theorem joinPlaneAction_kernel_isTwoGroup : IsPGroup 2 (joinPlaneAction D S m).ker := by
  let J := localJoin D S m
  let N := ((flag D S m).Li 1).subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le ((flag D S m).Li 1).le_normalizer ((flag D S m).sylow_normalizes_Li 1))
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show (flag D S m).Li 1 ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen
  let ρ := joinPlaneAction D S m
  let q := (QuotientGroup.mk' N).comp ρ.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* (flag D S m).Li 1 :=
      (J.subtype.comp (ρ.ker.subtype.comp q.ker.subtype)).codRestrict _ (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 ((flag D S m).Li 1) := by
      intro x
      apply plane_core_of_fixes D S m
      intro v
      exact LinearMap.congr_fun x.val.property v
    let r' : q.ker →* pCore 2 ((flag D S m).Li 1) := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 ((flag D S m).Li 1) => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

/-- The action kernel on the original plane is precisely the intrinsic two-core. -/
theorem joinPlaneAction_ker :
    (joinPlaneAction D S m).ker = pCore 2 (localJoin D S m) := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,joinPlaneAction_kernel_isTwoGroup D S m⟩
  · let := joinPlaneAction_irreducible D S m
    exact normal_p_subgroup_le_ker _ _ pCore_isPGroup

/-- The source Sylow plane centralizer is the literal radical R₂. -/
theorem sylow_centralizer_plane :
    (T : Subgroup G) ⊓ centralizer ((flag D S m).Vi 1 : Set G) =
      (flag D S m).Ri 1 := by
  apply le_antisymm
  · intro x hx
    let a : localJoin D S m := ⟨x,mem_sup_right hx.1⟩
    have ha : a ∈ (joinPlaneAction D S m).ker := by
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hx.2 v.toMul v.toMul.property).symm
    rw [joinPlaneAction_ker] at ha
    exact mem_map_of_mem _ ha
  · exact le_inf (localRadical_le_sylow _) (radical_centralizes_plane D S m)

/-- Application to the actual subgroups occurring in 11.2.4. -/
theorem subgroup_centralizes_plane {A : Subgroup G} (hA : A ≤ (flag D S m).Ri 1) :
    A ≤ centralizer ((flag D S m).Vi 1 : Set G) :=
  hA.trans (radical_centralizes_plane D S m)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction
