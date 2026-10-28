module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.FullSylow
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Escape
public import Theory.GroupTheory.PrimeResidualIntersection
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionMarkedFusion

/-!
# The literal marked intersection for the full partner

The prime residual and marked-centralizer escape identify the residual of
M intersect Mc intersect C_G(Z1). Its Sylow subgroup fixes E, so this whole
intersection fixes E. Pointwise Thompson correction transfers the conclusion
to Mc intersect C_G(Z1), giving exactly C_G(E) and its T-normalization.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- Prime-residual control on the original full-partner marked centralizer. -/
theorem PreparedChosenModule.decomposable_five_full_partner_marked_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      localModule T Mc = thompsonFixed T V →
      let E := thompsonFixed T V
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z₁ : Set G)
      let C := M ⊓ G1
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 →
      (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
        (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
          (M ⊓ centralizer (V : Set G)).subtype ∧
      G1 ⊓ Mc = centralizer (E : Set G) ∧
      (T : Subgroup G) ≤ normalizer (G1 ⊓ Mc : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq E Z₁ G1 C hcard
  let S := (T : Subgroup G) ⊓ G1
  let N := M ⊓ centralizer (V : Set G)
  let H := M ⊓ Mc ⊓ G1
  have hNE := h.decomposable_five_fixed_normalizer_eq_partner
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hMcE : Mc ≤ normalizer (E : Set G) := hNE.ge
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSC : S ≤ centralizer (E : Set G) := by
    have hh := (h.decomposable_five_full_partner_marked_sylow_normal
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive hUcEq).1
    exact hh.le.trans inf_le_right
  have hSylC : Chapter1.IsSylowIn 2 S C := s.local_sylow hM.1.2 h.normalized c d π hs
  have hescape : ¬ C ≤ Mc := h.decomposable_five_marked_centralizer_not_le
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hNMc : N ≤ Mc := inf_le_right.trans (h.centralizer_le_partner T hu)
  have hNC : N ≤ C := inf_le_inf_left M
    (centralizer_le (show Z₁ ≤ V from inf_le_right.trans inf_le_left))
  have hNH : N ≤ H := le_inf (le_inf inf_le_left hNMc) (hNC.trans inf_le_right)
  have hHC : H ≤ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hSH : S ≤ H := le_inf (le_inf (inf_le_left.trans hM.1.2)
    (inf_le_left.trans hTMc)) inf_le_right
  have hI : (pResidual 2 H).map H.subtype = (pResidual 2 N).map N.subtype := by
    let : (N.subgroupOf C).Normal := caseI_module_centralizer_normal h.normalized
    obtain ⟨P,hP⟩ := hSylC
    apply embedded_pResidual_intersection_of_prime_quotient_residual C N H hNC hNH hHC P
    · intro x hx
      exact hSH (hP ▸ hx)
    · intro hh
      exact hescape (hh ▸ (show H ≤ Mc from inf_le_left.trans inf_le_right))
    · rw [show Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 from hcard]
      decide
  have hHE : H ≤ centralizer (E : Set G) := by
    obtain ⟨P,hP⟩ := hSylC.restrict hSH hHC
    have hgen := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top P)
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hP] at hgen
    rw [←hgen,hI]
    exact sup_le ((map_subtype_le _).trans (inf_le_right.trans
      (centralizer_le (show E ≤ V from inf_le_left)))) hSC
  have hMZ : G1 ⊓ Mc = centralizer (E : Set G) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨n,hn,hnE,hnact⟩ := h.marked_normalizer_pointwise_correction hG T hM hJ
        (show E ≤ V from inf_le_left) (show Z₁ ≤ V from inf_le_right.trans inf_le_left)
        g hg.1 (hMcE hg.2)
      have hnC : n ∈ centralizer (E : Set G) := hHE ⟨⟨hn.1,hNE.le hnE⟩,hn.2⟩
      intro e he
      have hh : g*e*g⁻¹ = e := by
        rw [←hnact e he,←hnC e he,mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · exact le_inf (centralizer_le (show Z₁ ≤ E from inf_le_right))
        ((Subgroup.centralizer_le_normalizer (E : Set G)).trans hNE.le)
  refine ⟨hI,hMZ,?_⟩
  change (T : Subgroup G) ≤ normalizer ((G1 ⊓ Mc : Subgroup G) : Set G)
  rw [hMZ]
  exact (hTMc.trans hMcE).trans (normalizer_le_normalizer_centralizer _)

end CFSG.Quasithin.Chapter15.Section01
