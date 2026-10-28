module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.FourOuter
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PerfectCentralModSolvable

/-!
# Inner actions above a binary four-dimensional component

A Sylow-preserving automorphism of SL₄(2) which preserves a proper
nonsolvable Sylow-normalized subgroup is inner. This constructs a
surjective ambient action on SL₄(2), with a two-group kernel.
The same construction works for a normal component with that two-core
quotient: perfect containment reflects through the two-core, which lies
in the original Sylow and normalizes the specified subgroup.

The original terminal application is TerminalComponentProperEight.
Source: Aschbacher–Smith, 12.2.7, printed pp.797–798, as used in 12.3.12,
printed p.811. All maps retain the actual component and quotient.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions
private instance : Finite (LinearGroup 4) := Finite.of_injective
  (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective

private theorem conjugation_injective_four :
    Function.Injective (MulAut.conj : LinearGroup 4 →* MulAut (LinearGroup 4)) := by
  let e : LinearGroup 4 ≃* alternatingGroup (Fin 8) :=
    (projectiveEquivLinear (by decide : 0 < 4)).symm.trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm
  apply (MulAut.conj : LinearGroup 4 →* MulAut (LinearGroup 4)).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have hz : e x ∈ center (alternatingGroup (Fin 8)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    apply Eq.symm
    rw [←map_mul,←map_mul]
    apply congrArg e
    have h := congrArg (fun a : MulAut (LinearGroup 4) => a z) hx
    exact mul_inv_eq_iff_eq_mul.mp h
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hz
  exact e.map_eq_one_iff.mp hz

/-- A normal binary-four supplement with a proper nonsolvable
Sylow-normalized subgroup induces the full inner action. -/
theorem exists_inner_four_action
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [C.Normal] (e : C ≃* LinearGroup 4)
    (S : Sylow 2 G) (hgen : C ⊔ (S : Subgroup G) = ⊤)
    (B : Subgroup G) (hBC : B ≤ C) (hne : B ≠ C)
    (hns : ¬ Group.IsSolvable B)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ f : G →* LinearGroup 4, Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      ∀ c : C, f c = e c := by
  let D := B.subgroupOf C
  let R := D.map e.toMonoidHom
  let a := componentAction C e
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal C
  let Q := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUR : (U : Subgroup C) ≤ normalizer (D : Set C) := by
    rw [hU]
    exact (comap_mono hSB).trans (le_normalizer_comap C.subtype)
  have hQR : (Q : Subgroup (LinearGroup 4)) ≤ normalizer (R : Set (LinearGroup 4)) :=
    (map_mono hUR).trans (D.le_normalizer_map e.toMonoidHom)
  have hnR : R ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) he
    change (D.map e.toMonoidHom).map e.symm.toMonoidHom = _ at hh
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id C := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [map_map, hcomp, map_id, map_top_of_surjective _ e.symm.surjective] at hh
    exact hne (le_antisymm hBC (subgroupOf_eq_top.mp hh))
  have hnsR : ¬ Group.IsSolvable R := by
    intro hs
    let := hs
    let c : B ≃* R := (subgroupOfEquivOfLe hBC).symm.trans (e.subgroupMap D)
    exact hns (Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective)
  have hI : ((S : Subgroup G) ⊓ C).subgroupOf C = (U : Subgroup C) := by
    rw [hU]
    ext x
    exact and_iff_left x.property
  have hnI : (S : Subgroup G) ≤ normalizer ((S : Subgroup G) ⊓ C : Set G) :=
    (le_inf (S : Subgroup G).le_normalizer (by rw [normalizer_eq_top]; exact le_top)).trans
      inf_normalizer_le_normalizer_inf
  have hsinner (s : S) : a s ∈ MulAut.innerSubgroup (LinearGroup 4) := by
    apply inner_of_preserves_nonsolvable_normalized_four Q R hQR hnR hnsR
    · have h := componentAction_map_subgroup C e ((S : Subgroup G) ⊓ C)
        inf_le_right s (hnI s.property)
      change ((U : Subgroup C).map e.toMonoidHom).map (a s).toMonoidHom = _
      change ((U : Subgroup C).map e.toMonoidHom).map (a s).toMonoidHom =
        (U : Subgroup C).map e.toMonoidHom
      simpa only [hI] using h
    · exact componentAction_map_subgroup C e B hBC s (hSB s.property)
  have ha : ∀ x : G, a x ∈ MulAut.innerSubgroup (LinearGroup 4) := by
    have hh : C ⊔ (S : Subgroup G) ≤ (MulAut.innerSubgroup (LinearGroup 4)).comap a := by
      refine sup_le ?_ ?_
      · intro c hc
        refine ⟨e ⟨c,hc⟩, ?_⟩
        change MulAut.conj (e ⟨c,hc⟩) = (MulAut.congr e) (MulAut.conjNormal c)
        rw [show MulAut.conjNormal c = MulAut.conj (⟨c,hc⟩ : C) from by ext x; rfl,
          MulAut.congr_conj]
      · intro s hs
        exact hsinner ⟨s,hs⟩
    rw [hgen] at hh
    exact fun x => hh (mem_top x)
  let i := MonoidHom.ofInjective conjugation_injective_four
  let f := i.symm.toMonoidHom.comp (a.codRestrict (MulAut.innerSubgroup _) ha)
  have hfC (c : C) : f c = e c := by
    apply conjugation_injective_four
    have hh := congrArg Subtype.val (i.apply_symm_apply (a.codRestrict _ ha c))
    change MulAut.conj (f c) = a c at hh
    rw [hh]
    change (MulAut.congr e) (MulAut.conjNormal (c : G)) = _
    rw [MulAut.conjNormal_val,MulAut.congr_conj]
  refine ⟨f,?_,?_,hfC⟩
  · intro x
    obtain ⟨c,rfl⟩ := e.surjective x
    exact ⟨c,hfC c⟩
  · apply f.kernel_isPGroup_of_normal_supplement C S S.isPGroup' hgen
    have he : f.comp C.subtype = e.toMonoidHom := by apply MonoidHom.ext; intro c; exact hfC c
    rw [he,e.toMonoidHom.ker_eq_bot e.injective]
    exact IsPGroup.of_card (n := 0) (by simp)

/-- Lift the inner action through the actual ambient two-core. -/
theorem exists_inner_four_core_action
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [C.Normal] [Group.IsPerfect C]
    (e : (C ⧸ pCore 2 C) ≃* LinearGroup 4)
    (S : Sylow 2 G) (hgen : C ⊔ (S : Subgroup G) = ⊤)
    (B : Subgroup G) [Group.IsPerfect B] (hBC : B ≤ C) (hne : B ≠ C)
    (hns : ¬ Group.IsSolvable B)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ f : G →* LinearGroup 4, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := pCore 2 G
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let C' := C.map q
  let B' := B.map q
  let S' := S.mapSurjective hq
  let e' : C' ≃* LinearGroup 4 := (coreQuotientEquivImage 2 C).symm.trans e
  let : C'.Normal := Subgroup.Normal.map inferInstance q hq
  let : Group.IsNilpotent N := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  have hgen' : C' ⊔ (S' : Subgroup (G ⧸ N)) = ⊤ := by
    change C.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hne' : B' ≠ C' := by
    intro he
    apply hne
    apply le_antisymm hBC
    apply perfect_le_of_map_le_of_kernel_central_mod_solvable q N
      (by rw [QuotientGroup.ker_mk'])
      (by rw [QuotientGroup.ker_mk',QuotientGroup.map_mk'_self]; exact bot_le)
      C B ((pCore_isPGroup.le_sylow_of_normal S).trans hSB)
    exact he.ge
  have hns' : ¬ Group.IsSolvable B' := by
    intro hs
    exact hns ((Group.isSolvable_map_iff_of_solvable_ker q B).mp hs)
  have hn' : (S' : Subgroup (G ⧸ N)) ≤ normalizer (B' : Set (G ⧸ N)) :=
    (map_mono hSB).trans (le_normalizer_map q)
  obtain ⟨a,ha,hka,_⟩ := exists_inner_four_action C' e' S' hgen' B'
    (map_mono hBC) hne' hns' hn'
  refine ⟨a.comp q,ha.comp hq,?_⟩
  exact hka.comap_of_ker_isPGroup q hk
end BinaryLinear.SylowFlagOvergroups

