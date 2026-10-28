module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawConstrainedSource
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.CubicResidual

/-!
# The original binary-linear intersection lies in the partner

The full original component Sylow lies in M intersection L. In a binary
linear core quotient, its Sylow overgroup has equal two-residual and
prime-to-three residual. This equality lifts through the actual two-core
kernel. The original quintic source centralizes V on the latter residual;
the original Sylow supplement lies in Mc. Thus the literal M intersection L
lies in Mc. No generation of L or M is assumed in this deduction.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem raw_binaryLinear_residuals
    (T : Sylow 2 G) {M Z1 L : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hs : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    pResidual 2 (M ⊓ L : Subgroup G) = primeToResidual 3 (M ⊓ L : Subgroup G) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let A := BinaryLinear.OuterCyclic.LinearGroup (m+1)
  let el := e.trans (BinaryLinear.OuterCyclic.slEquivLinear (m+1))
  let f := el.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := el.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ el.injective,QuotientGroup.ker_mk']
  let P := M ⊓ L
  let j : P →* L := inclusion inf_le_right
  let g := f.comp j
  have hgk : IsPGroup 2 g.ker := by
    let a : g.ker →* pCore 2 L := {
      toFun := fun x => ⟨j x.val,hk ▸ x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective a
    intro x y he
    apply Subtype.ext
    exact (inclusion_injective inf_le_right) (congrArg Subtype.val he)
  obtain ⟨Q,hQ⟩ := hs
  let S := Q.mapSurjective hf
  have hS : (S : Subgroup A) ≤ g.range := by
    rintro _ ⟨x,hx,rfl⟩
    have hxSL : (x : G) ∈ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L :=
      hQ ▸ mem_map_of_mem L.subtype hx
    exact ⟨⟨x,⟨hTM hxSL.1.1,x.property⟩⟩,rfl⟩
  have hmodel := BinaryLinear.SylowFlagOvergroups.twoResidual_eq_cubic S g.range hS
  exact twoResidual_eq_primeToResidual_three_of_two_kernel g.rangeRestrict
    g.rangeRestrict_surjective
    (hgk.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict g)).symm) hmodel

/-- The literal original M intersection L lies in Mc in each binary-linear core row. -/
theorem PreparedChosenModule.raw_binaryLinear_intersection_le_partner
    (T : Sylow 2 G) {M Mc V Z1 L : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G))
    {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    M ⊓ L ≤ Mc := by
  let P := M ⊓ L
  let SL := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L
  have hR : (pResidual 2 P).map P.subtype ≤ centralizer (V : Set G) := by
    rw [raw_binaryLinear_residuals T hTM hs hn e]
    exact hcubic
  have hCMc : centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact localModule_centralizer_le_partner T M hu
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSLP : SL ≤ P := le_inf ((inf_le_left.trans inf_le_left).trans hTM) inf_le_right
  have hSyl : Chapter1.IsSylowIn 2 SL P := by
    obtain ⟨hp,hSL,hmax⟩ := Chapter1.isSylowIn_iff.mp hs
    exact Chapter1.isSylowIn_iff.mpr ⟨hp,hSLP,fun U hU hSU hUP => hmax U hU hSU (hUP.trans inf_le_right)⟩
  obtain ⟨Q,hQ⟩ := hSyl
  have he := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top Q)
  rw [Subgroup.map_sup,hQ,←MonoidHom.range_eq_map,range_subtype] at he
  change P ≤ Mc
  rw [←he]
  exact sup_le (hR.trans hCMc) ((inf_le_left.trans inf_le_left).trans hTMc)

end CFSG.Quasithin.Chapter15.Section01
