module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSupportDisplacements
public import Theory.GroupTheory.CommutingCentralizerFactors

/-!
# The original module meets the partner core exactly in E

The original F-normalized direct product V1 V2 has fixed subgroup equal to
the product of its two fixed subgroups. Each support is genuinely moved, and
the original reflection geometry identifies its fixed group as Zi. Thus
C_V(F)=E. Since F is central in the partner core and E is in F, also V∩O2(Mc)=E.
The literal intersection M∩Mc therefore normalizes the original marked E.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_of_normalized_direct_product
    (A B H : Subgroup G) (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hnA : H ≤ normalizer (A : Set G)) (hnB : H ≤ normalizer (B : Set G)) :
    (A ⊔ B) ⊓ centralizer (H : Set G) =
      (A ⊓ centralizer (H : Set G)) ⊔ (B ⊓ centralizer (H : Set G)) := by
  apply le_antisymm
  · rintro x ⟨hx,hxH⟩
    have hx' : x ∈ (A : Set G)*(B : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right A B
        (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx'
    have hcoords (z : G) (hz : z ∈ H) : z*a*z⁻¹=a ∧ z*b*z⁻¹=b := by
      have he : (z*a*z⁻¹)*(z*b*z⁻¹)=a*b := by
        calc
          _ = z*(a*b)*z⁻¹ := by group
          _ = a*b := by rw [hxH z hz,mul_inv_cancel_right]
      have hp : ((⟨z*a*z⁻¹,(mem_normalizer_iff.mp (hnA hz) a).mp ha⟩ : A),
          (⟨z*b*z⁻¹,(mem_normalizer_iff.mp (hnB hz) b).mp hb⟩ : B)) =
          ((⟨a,ha⟩ : A),(⟨b,hb⟩ : B)) := mul_injective_of_disjoint hd he
      exact ⟨congrArg (fun p : A×B => (p.1 : G)) hp,
        congrArg (fun p : A×B => (p.2 : G)) hp⟩
    apply mul_mem_sup
    · refine ⟨ha,?_⟩
      intro z hz
      exact mul_inv_eq_iff_eq_mul.mp (hcoords z hz).1
    · refine ⟨hb,?_⟩
      intro z hz
      exact mul_inv_eq_iff_eq_mul.mp (hcoords z hz).2
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

/-- The unchanged E is the exact intersection of V with the partner core,
and is normalized by the actual M∩Mc. -/
theorem PreparedChosenModule.decomposable_five_partner_two_core_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      V ≤ Mc.pCoreIn 2 ∨
        (V ⊓ centralizer (F : Set G) = E ∧ V ⊓ Mc.pCoreIn 2 = E ∧
          M ⊓ Mc ≤ normalizer (E : Set G)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let Q := Mc.pCoreIn 2
  let F := conjugateSpanBy E C
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  by_cases hVQ : V ≤ Q
  · exact Or.inl hVQ
  right
  obtain ⟨_,hFQZ,hEF,_,_,_⟩ := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨_,hcore,hQT,_,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hFQ : F ≤ Q := hFQZ.trans inf_le_left
  have hFZ : F ≤ centralizer (Q : Set G) := hFQZ.trans inf_le_right
  have hQT' : Q ≤ (T : Subgroup G) := by
    change Mc.pCoreIn 2 ≤ (T : Subgroup G)
    rw [←hcore]
    exact hQT
  have hFT : F ≤ (T : Subgroup G) := hFQ.trans hQT'
  have hFE : F ≤ centralizer (E : Set G) := hFZ.trans (centralizer_le (hEF.trans hFQ))
  have hFN₁ : F ≤ normalizer (V₁ : Set G) := fun f hf =>
    s.centralizer_le_stabilizer ⟨hFT hf,
      (hFE.trans (centralizer_le (show Z₁ ≤ E from inf_le_right))) hf⟩
  have hFN₂ : F ≤ normalizer (V₂ : Set G) := fun f hf =>
    s.stabilizes_second ⟨hFT hf,hFN₁ hf⟩
  let : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  obtain ⟨hdisp,_⟩ := (h.decomposable_five_partner_two_support_displacements.{u,0}
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hfixed (i : d.Index) :
      plane V (c.ambientFactor d i).space ⊓ centralizer (F : Set G) =
        thompsonPlane T V (c.ambientFactor d i).space := by
    let Vi := plane V (c.ambientFactor d i).space
    let Zi := thompsonPlane T V (c.ambientFactor d i).space
    have hnon : ¬F ≤ centralizer (Vi : Set G) := by
      intro hh
      have he : ⁅Vi,F⁆ = ⊥ := by
        rw [commutator_comm]
        exact commutator_eq_bot_iff_le_centralizer.mpr hh
      have hz : Zi = ⊥ := (hdisp i).symm.trans he
      have hh := s.thompson_card i
      change Nat.card Zi = 4 at hh
      rw [hz,card_bot] at hh
      omega
    obtain ⟨f,hf,hfn⟩ := Set.not_subset.mp hnon
    have hfix := (s.involution_support_displacement_and_fixed hM.1.2 h.normalized c d
      π hp hs hfive f (hFT hf)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf) (hFN₁ hf) i).1.resolve_left hfn
    apply le_antisymm
    · intro v hv
      exact hfix ⟨hv.1,mem_centralizer_singleton_iff.mpr ((hv.2 f hf).symm)⟩
    · exact le_inf inf_le_left ((show Zi ≤ E from inf_le_right).trans
        (le_centralizer_iff.mp hFE))
  have hCV : V ⊓ centralizer (F : Set G) = E := by
    rw [←s.complement,centralizer_of_normalized_direct_product V₁ V₂ F
      (disjoint_iff.mpr s.disjoint)
      ((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _)))) hFN₁ hFN₂,
      hfixed s.first,hfixed s.second]
    exact s.thompson_split.symm
  have hVQeq : V ⊓ Q = E := by
    apply le_antisymm
    · exact (inf_le_inf_left V (le_centralizer_iff.mp hFZ)).trans_eq hCV
    · exact le_inf inf_le_left (hEF.trans hFQ)
  refine ⟨hCV,hVQeq,?_⟩
  have hnQ : Mc ≤ normalizer (Q : Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  intro g hg
  change g ∈ normalizer (E : Set G)
  rw [←hVQeq]
  apply mem_normalizer_iff.mpr
  intro x
  exact and_congr (mem_normalizer_iff.mp (h.normalized hg.1) x)
    (mem_normalizer_iff.mp (hnQ hg.2) x)

end CFSG.Quasithin.Chapter15.Section01
