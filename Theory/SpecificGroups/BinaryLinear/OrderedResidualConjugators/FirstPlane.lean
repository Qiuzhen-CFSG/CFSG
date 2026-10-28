module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.FullFlagSylow
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The first minimal parabolic on its marked plane

The cubic element in the first node residual moves the entire first plane.
Restriction of the first minimal parabolic onto that plane is surjective.
Its kernel fixes the first line, hence lies in the full flag two-group.
Since the binary general linear group of the plane has trivial two-core,
this kernel is exactly the first parabolic's two-core.

These calculations retain an arbitrary common basis and work in every
ambient dimension at least three. The source application is the movement
and two-core calculation in Aschbacher--Smith, 15.1.29, printed
pp.1103--1104 of `refs/quasithin.pdf`.
-/

@[expose] public section
open Subgroup
namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

/-- The first cubic Levi actor moves the entire first two-dimensional cut. -/
theorem first_plane_le_of_residual_differences {m : ℕ} (hm : 2 ≤ m)
    (b : Basis m) (W : Submodule (ZMod 2) (Space (m + 1)))
    (hd : ∀ g ∈ nodeResidual b ⟨0,by omega⟩,
      ∀ v ∈ cutSpace b ⟨1,by omega⟩, g v - v ∈ W) :
    cutSpace b ⟨1,by omega⟩ ≤ W := by
  let i : Fin m := ⟨0,by omega⟩
  let r := i.castSucc
  let s := i.succ
  have hrs : r ≠ s := by simp [r,s,Fin.ext_iff]
  let c := cubic b r s hrs
  have hc : c ∈ nodeResidual b i := cubic_mem_nodeResidual b i
  have hr : b r ∈ cutSpace b ⟨1,by omega⟩ :=
    (basis_mem_cutSpace b _ r).mpr (by simp [r,i])
  have hs : b s ∈ cutSpace b ⟨1,by omega⟩ :=
    (basis_mem_cutSpace b _ s).mpr (by simp [s,i])
  have hcr : c (b r) = b s := by
    change root b r s hrs (root b s r hrs.symm (b r)) = _
    rw [root_basis,if_pos rfl,map_add,root_basis,root_basis,
      if_neg hrs,if_pos rfl]
    rw [add_left_comm, show b r + b r = 0 by
      ext j
      exact CharTwo.add_self_eq_zero _, add_zero]
  have hcs : c (b s) = b s + b r := by
    change root b r s hrs (root b s r hrs.symm (b s)) = _
    rw [root_basis,if_neg hrs.symm,root_basis,if_pos rfl]
  have hrW : b r ∈ W := by
    have hh := hd c hc (b s) hs
    rw [hcs,add_sub_cancel_left] at hh
    exact hh
  have hsW : b s ∈ W := by
    have hh := hd c hc (b r) hr
    rw [hcr] at hh
    simpa only [sub_add_cancel] using W.add_mem hh hrW
  apply Submodule.span_le.mpr
  rintro _ ⟨k,hk,rfl⟩
  have hk' : k.val = 0 ∨ k.val = 1 := by change k.val ≤ 1 at hk; omega
  rcases hk' with hk' | hk'
  · have he : k = r := Fin.ext hk'
    exact he.symm ▸ hrW
  · have he : k = s := Fin.ext hk'
    exact he.symm ▸ hsW

open OuterCyclic InvariantNodeActions SmallParabolicLevi

variable {m : ℕ} (hm : 2 ≤ m) (b : Basis m)

theorem first_le_plane_stabilizer :
    minimalParabolic b ⟨0,by omega⟩ ≤ parabolic (cutSpace b ⟨1,by omega⟩) := by
  intro g hg
  exact (mem_cutStabilizer b _ g).mp hg _ (by simp)

/-- Restriction to the first plane, on the literal first minimal parabolic. -/
noncomputable def firstPlaneAction :
    minimalParabolic b ⟨0,by omega⟩ →* BinaryLinear.GL (cutSpace b ⟨1,by omega⟩) :=
  (subspaceAction _).comp (inclusion (first_le_plane_stabilizer hm b))

theorem firstPlaneAction_surjective : Function.Surjective (firstPlaneAction hm b) := by
  intro x
  let W := cutSpace b ⟨1,by omega⟩
  obtain ⟨g,hg⟩ := blockAction_surjective W (x,1)
  have hq : quotientAction W g = 1 := congrArg Prod.snd hg
  have hd (v : Space (m + 1)) : g.val v - v ∈ W := by
    apply (Submodule.Quotient.eq W).mp
    have he := LinearEquiv.congr_fun hq (W.mkQ v)
    exact he
  have hn : g.val ∈ minimalParabolic b ⟨0,by omega⟩ := by
    apply (mem_cutStabilizer_maps b {⟨0,by omega⟩}ᶜ (g.val : LinearGroup (m + 1))).mpr
    intro j hj v hv
    have hj0 : j.val ≠ 0 := by
      intro he
      exact hj (Fin.ext he)
    have hW : W ≤ cutSpace b j := cutSpace_mono b (show (⟨1,by omega⟩ : Fin m) ≤ j by
      change 1 ≤ j.val
      omega)
    simpa only [sub_add_cancel] using (cutSpace b j).add_mem (hW (hd v)) hv
  refine ⟨⟨g.val,hn⟩,?_⟩
  exact congrArg Prod.fst hg

theorem firstPlaneAction_kernel_two : IsPGroup 2 (firstPlaneAction hm b).ker := by
  have hle : ((firstPlaneAction hm b).ker).map
      (minimalParabolic b ⟨0,by omega⟩).subtype ≤ cutStabilizer b Set.univ := by
    rintro _ ⟨g,hg,rfl⟩
    rw [mem_cutStabilizer]
    intro j _ v
    by_cases hj : j = ⟨0,by omega⟩
    · subst j
      have hc : ∀ w ∈ cutSpace b ⟨1,by omega⟩, g.val w = w := by
        intro w hw
        exact congrArg Subtype.val
          (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨w,hw⟩)
      have h0 : cutSpace b ⟨0,by omega⟩ ≤ cutSpace b ⟨1,by omega⟩ :=
        cutSpace_mono b (by change (0 : ℕ) ≤ 1; omega)
      constructor
      · intro hv
        have he := hc (g.val v) (h0 hv)
        have he' : g.val v = v := g.val.injective he
        exact he' ▸ hv
      · intro hv
        change g.val v ∈ _
        rw [hc v (h0 hv)]
        exact hv
    · exact (mem_cutStabilizer b _ g.val).mp g.property j hj v
  exact ((fullFlag_isPGroup b).to_le hle).of_equiv
    (((firstPlaneAction hm b).ker).equivMapOfInjective
      (minimalParabolic b ⟨0,by omega⟩).subtype
      (minimalParabolic b ⟨0,by omega⟩).subtype_injective).symm


theorem ker_firstPlaneAction : (firstPlaneAction hm b).ker =
    pCore 2 (minimalParabolic b ⟨0,by omega⟩) := by
  let : Finite (LinearGroup (m + 1)) := Finite.of_injective
    (fun g : LinearGroup (m + 1) => (g : Space (m + 1) → Space (m + 1)))
    DFunLike.coe_injective
  let W := cutSpace b (⟨1,by omega⟩ : Fin m)
  let : Finite (BinaryLinear.GL W) := Finite.of_injective
    (fun g : BinaryLinear.GL W => (g : W → W)) DFunLike.coe_injective
  have hh := (firstPlaneAction hm b).comap_pCore_of_ker_isPGroup
    (firstPlaneAction_surjective hm b) (firstPlaneAction_kernel_two hm b)
  rw [linearGroup_twoCore_eq_bot] at hh
  exact hh

theorem mem_first_core_iff (g : LinearGroup (m + 1)) :
    g ∈ (minimalParabolic b ⟨0,by omega⟩).pCoreIn 2 ↔
      g ∈ minimalParabolic b ⟨0,by omega⟩ ∧
        ∀ w ∈ cutSpace b ⟨1,by omega⟩, g w = w := by
  constructor
  · rintro ⟨g,hg,rfl⟩
    refine ⟨g.property,?_⟩
    rw [← ker_firstPlaneAction hm b] at hg
    intro w hw
    exact congrArg Subtype.val
      (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨w,hw⟩)
  · rintro ⟨hg,he⟩
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    rw [← ker_firstPlaneAction hm b]
    apply MonoidHom.mem_ker.mpr
    apply LinearEquiv.ext
    intro w
    exact Subtype.ext (he w w.property)


end BinaryLinear.OrderedResidualConjugators
