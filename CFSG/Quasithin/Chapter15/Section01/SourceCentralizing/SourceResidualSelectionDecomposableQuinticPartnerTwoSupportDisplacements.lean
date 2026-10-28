module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoFullSupportActors
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelLines
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.InvariantImages
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineCosts

/-!
# Literal support displacements and surviving transvections

On the whole elementary span F the original support actors move exactly Zi.
Faithful conjugation coordinates identify this as the group equality [Vi,F]=Zi.
It therefore survives passage to the unchanged canonical F/D. The proved
line intersections make every original support image a nontrivial rank-one,
cost-one actor, with its literal marked line as its entire moved space.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem image_commutator_full
    {Mc F D : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ)
    (B : Subgroup G) (hB : B ≤ Mc) :
    dF.imageSpace ⁅B,F⁆ = subspaceCommutator
      (Representation.BinaryOffender.imageRepresentation ρ) ⊤
      (actionSubgroup ρ (B.subgroupOf Mc)) := by
  change _ = subspaceCommutator _ ⊤ ((B.subgroupOf Mc).map
    (Representation.BinaryOffender.actionHom ρ))
  rw [←subspaceCommutator_comp_map]
  change dF.imageSpace ⁅B,F⁆ = subspaceCommutator ρ ⊤ (B.subgroupOf Mc)
  simpa only [dF.imageSpace_self] using dF.imageSpace_commutator B F hB le_rfl

/-- Each original support moves exactly its original marked plane in F,
and induces a nontrivial transvection on the same canonical quotient. -/
theorem PreparedChosenModule.decomposable_five_partner_two_support_displacements
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
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ((∀ i : d.Index, ⁅plane V (c.ambientFactor d i).space,F⁆ =
          thompsonPlane T V (c.ambientFactor d i).space) ∧
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          ∀ i : d.Index,
            let Ai := actionSubgroup ρ ((plane V (c.ambientFactor d i).space).subgroupOf Mc)
            let Pi := dF.imageSpace (thompsonPlane T V (c.ambientFactor d i).space)
            let σ := Representation.BinaryOffender.imageRepresentation ρ
            Nat.card Ai = 2 ∧ rank Ai = 1 ∧ fixedCodim σ Ai = 1 ∧
              IsMinimalBestOffender σ Ai ∧ Module.finrank (ZMod 2) Pi = 1 ∧
              subspaceCommutator σ ⊤ Ai = Pi) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  obtain ⟨_,hFQZ,hEF,_,_,_⟩ := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨hCMc,_,_,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,_,hFel,_,hMcF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := hFel
  have hFMc : F ≤ Mc := (hFQZ.trans inf_le_left).trans (pCoreIn_le 2 Mc)
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hnBot : Mc ≤ normalizer (⊥ : Subgroup G) := by
    rw [(⊥ : Subgroup G).normalizer_eq_top]
    exact le_top
  obtain ⟨ρ₀,⟨d₀⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates
    Mc F ⊥ hFMc hMcF bot_le hnBot
  have hfullActors := ((h.decomposable_five_full_span_support_actors
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ)
      ρ₀ d₀
  have hdisp (i : d.Index) : ⁅plane V (c.ambientFactor d i).space,F⁆ =
      thompsonPlane T V (c.ambientFactor d i).space := by
    let Vi := plane V (c.ambientFactor d i).space
    let Zi := thompsonPlane T V (c.ambientFactor d i).space
    have hViMc : Vi ≤ Mc := (plane_le _).trans hVMc
    have hcommF : ⁅Vi,F⁆ ≤ F :=
      le_normalizer_iff_commutator_le_right.mp (hViMc.trans hMcF)
    have hZiF : Zi ≤ F := (show Zi ≤ E from inf_le_right).trans hEF
    have he : d₀.imageSpace ⁅Vi,F⁆ = d₀.imageSpace Zi :=
      (image_commutator_full ρ₀ d₀ Vi hViMc).trans (hfullActors i).2.2.2.2
    apply le_antisymm
    · intro x hx
      have hm := (d₀.coordinates_mem_imageSpace_iff_of_kernel_le ⁅Vi,F⁆ bot_le
        ⟨x,hcommF hx⟩).mpr hx
      rw [he] at hm
      exact (d₀.coordinates_mem_imageSpace_iff_of_kernel_le Zi bot_le _).mp hm
    · intro x hx
      have hm := (d₀.coordinates_mem_imageSpace_iff_of_kernel_le Zi bot_le
        ⟨x,hZiF hx⟩).mpr hx
      rw [←he] at hm
      exact (d₀.coordinates_mem_imageSpace_iff_of_kernel_le ⁅Vi,F⁆ bot_le _).mp hm
  refine ⟨hdisp,?_⟩
  intro W _ _ ρ dF i
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let Vi := plane V (c.ambientFactor d i).space
  let Zi := thompsonPlane T V (c.ambientFactor d i).space
  let Ai := actionSubgroup ρ (Vi.subgroupOf Mc)
  let Pi := dF.imageSpace Zi
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  obtain ⟨hline,_⟩ := (h.decomposable_five_partner_two_core_or_kernel_lines
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  obtain ⟨_,_,_,hd₁,hd₂,_,_,hc₁,hc₂,_,_⟩ :=
    ((h.decomposable_five_partner_two_line_actor_bounds
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hline
  have hdim : Module.finrank (ZMod 2) Pi = 1 := by
    change Module.finrank (ZMod 2)
      (dF.imageSpace (thompsonPlane T V (c.ambientFactor d i).space)) = 1
    rcases s.covers i with hi | hi
    · subst i
      exact hd₁
    · subst i
      exact hd₂
  have hc : Nat.card Ai ≤ 2 := by
    rcases s.covers i with hi | hi
    · simpa only [Ai,Vi,hi] using hc₁
    · simpa only [Ai,Vi,hi] using hc₂
  have hm : subspaceCommutator σ ⊤ Ai = Pi := by
    rw [←image_commutator_full ρ dF Vi ((plane_le _).trans hVMc)]
    exact congrArg dF.imageSpace (hdisp i)
  have hne : Ai ≠ ⊥ := by
    intro hz
    have hz' : subspaceCommutator σ ⊤ Ai = ⊥ := by
      rw [hz]
      exact (subspaceCommutator_eq_bot_iff σ ⊤ ⊥).mpr (by simp)
    rw [hz'] at hm
    have hzdim := congrArg (fun P : Submodule (ZMod 2) W => Module.finrank (ZMod 2) P) hm
    simp only [finrank_bot] at hzdim
    omega
  have hcard : Nat.card Ai = 2 := by
    have hl : 1 < Nat.card Ai := (one_lt_card_iff_ne_bot Ai).mpr hne
    omega
  let : IsElementaryAbelian 2 Vi := IsElementaryAbelian.of_le (plane_le _)
  let : IsElementaryAbelian 2 (Vi.subgroupOf Mc) :=
    IsElementaryAbelian.subgroupOf ((plane_le _).trans hVMc)
  have he : IsElementaryTwo Ai := ⟨hne,
    IsElementaryAbelian.map (Representation.BinaryOffender.actionHom ρ)⟩
  have hr : rank Ai = 1 := by
    have hh : 2^rank Ai = 2^1 := by rw [←he.card_eq_two_pow_rank,hcard]; rfl
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hh
  have hcost : fixedCodim σ Ai = 1 := by
    have hh := moved_dimension_eq_cost_of_card_two σ Ai hcard
    rw [hm,hdim] at hh
    exact hh.symm
  have hoff : IsOffender σ Ai := ⟨he,by rw [hr,hcost]⟩
  exact ⟨hcard,hr,hcost,minimal_best_of_card_two σ Ai hoff hcard,hdim,hm⟩

end CFSG.Quasithin.Chapter15.Section01
