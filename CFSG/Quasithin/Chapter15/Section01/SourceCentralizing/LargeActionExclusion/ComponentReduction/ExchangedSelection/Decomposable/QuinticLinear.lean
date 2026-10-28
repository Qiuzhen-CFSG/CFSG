module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticSeven
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.CubicResidual

/-!
# Excluding binary linear quotients at the original prime-five component

The selected intersection M ∩ L contains a full Sylow two-subgroup of L.
In the literal binary linear quotient, its two-residual equals its
prime-to-three residual. This equality lifts through the original two-core
kernel. The prime-five module-centralizer quotient kills that cubic
residual, so O²(M ∩ L) centralizes V. Its Sylow supplement lies in Mc,
forcing M ∩ L into Mc. The retained generation by M ∩ L and M_L then
contradicts the original component's escape from M_Z.

Together with the preceding block exclusions, this removes every
constrained alternative at prime five on the same component with its
faithful sixteen-element moving support. The parent Decomposable module
applies it to the original eight-dimensional action. Constructing the
prime-five marker and proving catalogue exhaustion remain separate inputs.

Source: Aschbacher--Smith 15.1.22(3) and 15.1.23, printed pp.1099--1100.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The two original residuals of M ∩ L agree through its actual binary linear quotient. -/
theorem PreExclusionSource.selected_binaryLinear_residuals
    (s : d.PreExclusionSource h.normalized p) (hTM : (T : Subgroup G) ≤ M)
    {n : ℕ} (hn : 0 < n)
    (e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    pResidual 2 (M ⊓ d.L : Subgroup G) = primeToResidual 3 (M ⊓ d.L : Subgroup G) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let A := BinaryLinear.OuterCyclic.LinearGroup (m+1)
  let el := e.trans (BinaryLinear.OuterCyclic.slEquivLinear (m+1))
  let f := el.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  have hf : Function.Surjective f := el.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ el.injective,QuotientGroup.ker_mk']
  let P := M ⊓ d.L
  let j : P →* d.L := inclusion inf_le_right
  let g := f.comp j
  have hgk : IsPGroup 2 g.ker := by
    let a : g.ker →* pCore 2 d.L := {
      toFun := fun x => ⟨j x.val,hk ▸ x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective a
    intro x y he
    apply Subtype.ext
    exact (inclusion_injective inf_le_right) (congrArg Subtype.val he)
  obtain ⟨Q,hQ⟩ := s.component_sylow
  let S := Q.mapSurjective hf
  have hS : (S : Subgroup A) ≤ g.range := by
    rintro _ ⟨x,hx,rfl⟩
    have hxSL : (x : G) ∈ d.SL := hQ ▸ mem_map_of_mem d.L.subtype hx
    exact ⟨⟨x,⟨hTM (d.S_le_T (d.SL_le_S hxSL)),x.property⟩⟩,rfl⟩
  have hmodel := BinaryLinear.SylowFlagOvergroups.twoResidual_eq_cubic S g.range hS
  exact twoResidual_eq_primeToResidual_three_of_two_kernel g.rangeRestrict
    g.rangeRestrict_surjective
    (hgk.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict g)).symm) hmodel

/-- A binary linear quotient and the original parabolic generation exclude source prime five. -/
theorem PreExclusionSource.not_binaryLinear_quotient_of_prime_five
    (s : d.PreExclusionSource h.normalized 5) (hTM : (T : Subgroup G) ≤ M)
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {n : ℕ} (hn : 0 < n)
    (e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hgen : (M ⊓ d.L) ⊔ d.ML = d.L) : False := by
  let P := M ⊓ d.L
  have hR : (pResidual 2 P).map P.subtype ≤ centralizer (V : Set G) := by
    rw [s.selected_binaryLinear_residuals (h := h) hTM hn e]
    exact s.cubic_residual_centralizes_of_prime_five (h := h)
  have hCMc : centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact localModule_centralizer_le_partner T M hu
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSLP : d.SL ≤ P := le_inf (d.SL_le_S.trans (d.S_le_T.trans hTM)) inf_le_right
  have hSyl : Chapter1.IsSylowIn 2 d.SL P := by
    obtain ⟨hp,hSL,hmax⟩ := Chapter1.isSylowIn_iff.mp s.component_sylow
    exact Chapter1.isSylowIn_iff.mpr ⟨hp,hSLP,fun U hU hSU hUP => hmax U hU hSU (hUP.trans inf_le_right)⟩
  obtain ⟨Q,hQ⟩ := hSyl
  have hP : P ≤ Mc := by
    have he := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top Q)
    rw [Subgroup.map_sup,hQ,←MonoidHom.range_eq_map,range_subtype] at he
    rw [←he]
    exact sup_le (hR.trans hCMc) (d.SL_le_S.trans (d.S_le_T.trans hTMc))
  have hLMc : d.L ≤ Mc := by
    rw [←hgen]
    exact sup_le hP (inf_le_left.trans inf_le_right)
  exact d.L_not_le_MZ (le_inf d.L_component.1 hLMc)

/-- Every constrained row is impossible at prime five on the same faithful
sixteen-element moving support. The quotient and generation witnesses are
those of the original constrained catalogue. -/
theorem PreExclusionSource.not_constrained_of_prime_five_image_sixteen
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {B : Subgroup G} (hBV : B ≤ V) (hBL : B ≤ normalizer (d.L : Set G))
    (hcard : Nat.card (internalActionImage B d.L hBL) = 16) :
    ¬ d.ConstrainedAlternatives := by
  intro a
  rcases s.constrained_reduction_of_prime_five (h := h) hG hM hJ a with ha | ⟨n,e,hn,_,_,hg⟩
  · exact s.not_alternatingSeven_of_image_sixteen (h := h) hM.1.2 hBV hBL hcard ha
  · exact s.not_binaryLinear_quotient_of_prime_five (h := h) hM.1.2 hfull hu (by omega) e hg

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
