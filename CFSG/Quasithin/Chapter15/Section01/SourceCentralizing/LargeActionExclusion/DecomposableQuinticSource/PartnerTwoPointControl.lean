module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoPoint
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMarkedControl

/-!
# Literal point control in the order-four second seed

The chosen support point a and the original diagonal Uc generate E₂.
Consequently its partner centralizer is exactly C_G(E₂). The point residual
is the original marked residual, so the original quotient order and prime
intersection argument apply with the same denominator.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual first support line gives Sylow, residual, and partner
centralizer control while retaining the original marked quotient premise. -/
theorem PreparedChosenModule.decomposable_five_partner_two_point_control
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
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) →
      let E₂ := thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc)
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      ∃ a ∈ Z₁, ∃ b ∈ Z₂, a ≠ 1 ∧ b ≠ 1 ∧
        localModule T Mc = zpowers (a*b) ∧ E₂ = zpowers a ⊔ zpowers b ∧
        let Z := zpowers a
        let Gₐ := centralizer (Z : Set G)
        let C := M ⊓ Gₐ
        let S := (T : Subgroup G) ⊓ Gₐ
        let N := M ⊓ centralizer (V : Set G)
        letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
        Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 ∧
        Chapter1.IsSylowIn 2 S C ∧ Chapter1.IsSylowIn 2 S Gₐ ∧
        (S.subgroupOf (T : Subgroup G)).Normal ∧
        Gₐ ⊓ Mc = centralizer (E₂ : Set G) ∧
        (T : Subgroup G) ≤ normalizer (Gₐ ⊓ Mc : Set G) ∧
        (pResidual 2 (M ⊓ Mc ⊓ Gₐ : Subgroup G)).map (M ⊓ Mc ⊓ Gₐ).subtype =
          (pResidual 2 N).map N.subtype := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard E₂ Z₁ Z₂
  obtain ⟨a, ha, b, hb, hane, hbne, hU, hE, hpoint, hwhole, hSn⟩ :=
    h.decomposable_five_partner_two_second_seed_lines
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive hcU hcard
  change E₂ = zpowers a ⊔ zpowers b at hE
  let Z := zpowers a
  let Gₐ := centralizer (Z : Set G)
  let C := M ⊓ Gₐ
  let S := (T : Subgroup G) ⊓ Gₐ
  let N := M ⊓ centralizer (V : Set G)
  let H := M ⊓ Mc ⊓ Gₐ
  have hGa : Gₐ = centralizer ({a} : Set G) := by
    simp only [Gₐ, Z, zpowers_eq_closure, centralizer_closure]
  have hZ : Z ≤ thompsonFixed T V := zpowers_le.mpr ha.2
  have hN₁ : normalizer (E₂ : Set G) = Mc :=
    (h.decomposable_five_partner_two_second_seed_normalizer
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU).2.1
  obtain ⟨hUZ, hMcZ, _, _, _⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU
  have hMcU : Mc = centralizer (localModule T Mc : Set G) := by rw [hUZ]; exact hMcZ
  have hgen : E₂ = Z ⊔ localModule T Mc := by
    rw [hE, hU]
    apply le_antisymm
    · refine sup_le le_sup_left (zpowers_le.mpr ?_)
      have hh := (Z ⊔ zpowers (a*b)).mul_mem
        ((Z ⊔ zpowers (a*b)).inv_mem
          ((show Z ≤ Z ⊔ zpowers (a*b) from le_sup_left) (mem_zpowers a)))
        ((show zpowers (a*b) ≤ Z ⊔ zpowers (a*b) from le_sup_right) (mem_zpowers (a*b)))
      simpa only [inv_mul_cancel_left] using hh
    · exact sup_le le_sup_left (zpowers_le.mpr
        (mul_mem_sup (mem_zpowers a) (mem_zpowers b)))
  have hMZ : Gₐ ⊓ Mc = centralizer (E₂ : Set G) := by
    rw [hMcU, hgen]
    apply le_antisymm
    · intro g hg
      exact le_centralizer_iff.mp (sup_le
        (le_centralizer_iff.mpr (show zpowers g ≤ centralizer (Z : Set G) from zpowers_le.mpr hg.1))
        (le_centralizer_iff.mpr (show zpowers g ≤ centralizer (localModule T Mc : Set G) from
          zpowers_le.mpr hg.2))) (mem_zpowers g)
    · exact le_inf (centralizer_le (show Z ≤ Z ⊔ localModule T Mc from le_sup_left))
        (centralizer_le (show localModule T Mc ≤ Z ⊔ localModule T Mc from le_sup_right))
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMcZ]
    exact le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)
  have hTn : (T : Subgroup G) ≤ normalizer (Gₐ ⊓ Mc : Set G) := by
    change (T : Subgroup G) ≤ normalizer ((Gₐ ⊓ Mc : Subgroup G) : Set G)
    rw [hMZ]
    exact (hTMc.trans hN₁.ge).trans (normalizer_le_normalizer_centralizer _)
  have hSylC : Chapter1.IsSylowIn 2 S C := by
    change Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ Gₐ) (M ⊓ Gₐ)
    rw [hGa]
    exact s.quintic_point_local_sylow hM.1.2 h.normalized c d π hs a ha.1 hane hpoint
  have hSylG : Chapter1.IsSylowIn 2 S Gₐ := h.caseI_centralizer_sylow hG T hM hJ hZ (by
    change Chapter1.IsSylowIn 2 S (Gₐ ⊓ M)
    rw [inf_comm Gₐ M]
    exact hSylC)
  let : (N.subgroupOf C).Normal := caseI_module_centralizer_normal h.normalized
  have hc : Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 :=
    (s.quintic_point_quotient_residual_card h.normalized c d π hp hs hfive a ha hane).trans hcard
  have hescape : ¬ C ≤ Mc := by
    intro hh
    apply h.decomposable_five_marked_centralizer_not_le
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive
    exact (inf_le_inf_left M (centralizer_le (zpowers_le.mpr ha))).trans hh
  have hNMc : N ≤ Mc := inf_le_right.trans (h.centralizer_le_partner T hu)
  have hNC : N ≤ C := inf_le_inf_left M (centralizer_le (hZ.trans inf_le_left))
  have hNH : N ≤ H := le_inf (le_inf inf_le_left hNMc) (hNC.trans inf_le_right)
  have hHC : H ≤ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hSH : S ≤ H := le_inf (le_inf (inf_le_left.trans hM.1.2)
    (inf_le_left.trans hTMc)) inf_le_right
  have hI : (pResidual 2 H).map H.subtype = (pResidual 2 N).map N.subtype := by
    obtain ⟨P, hP⟩ := hSylC
    apply embedded_pResidual_intersection_of_prime_quotient_residual C N H hNC hNH hHC P
    · exact hP.le.trans hSH
    · intro hh
      exact hescape (hh ▸ (show H ≤ Mc from inf_le_left.trans inf_le_right))
    · rw [hc]
      decide
  refine ⟨a, ha, b, hb, hane, hbne, hU, hE, hc, hSylC, hSylG, ?_, hMZ, hTn, hI⟩
  change (((T : Subgroup G) ⊓ Gₐ).subgroupOf (T : Subgroup G)).Normal
  rw [hGa]
  exact hSn

end CFSG.Quasithin.Chapter15.Section01
