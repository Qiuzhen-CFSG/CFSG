module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCoreIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineNaturalExclusion
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoRankOneFullAction

/-!
# The original rank-two quotient retains a rank-two full-action kernel

The two original support centralizers are distinct hyperplanes in full F.
Their intersection is the full original V-centralizer, of index four. The
literal C_V(F)=E computes the full original V-image as E16, and the explicit
quotient onto the same canonical rank-two image retains its E4 kernel.

This is an internal continuation of the frozen rank-one full-action proof;
its private full-action kernel and index calculations are intentionally
shared through `import all`, without changing the frozen predecessor.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u w
variable {G : Type u} [Group G] [Finite G]

/-- The full original V-image has rank four and cost two in the canonical
rank-two branch; its actual quotient onto the same canonical image has rank-two kernel. -/
theorem PreparedChosenModule.decomposable_five_partner_two_rank_two_full_action
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
      let V₁ := plane V (c.ambientFactor d s.first).space
      let V₂ := plane V (c.ambientFactor d s.second).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (_dF : BinaryConjugationSection Mc F D ρ),
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          rank A = 2 →
          fixedCodim (Representation.BinaryOffender.imageRepresentation ρ) A = 2 ∧
          F ⊓ centralizer (V : Set G) =
            (F ⊓ centralizer (V₁ : Set G)) ⊓ (F ⊓ centralizer (V₂ : Set G)) ∧
          F ⊓ centralizer (V₁ : Set G) ≠ F ⊓ centralizer (V₂ : Set G) ∧
          (centralizer (V : Set G)).relIndex F = 4 ∧
          ∀ {W₀ : Type w} [AddCommGroup W₀] [Module (ZMod 2) W₀]
            (ρ₀ : Representation (ZMod 2) Mc W₀) (_d₀ : BinaryConjugationSection Mc F ⊥ ρ₀),
            let A₀ := actionSubgroup ρ₀ (V.subgroupOf Mc)
            Nat.card A₀ = 16 ∧ rank A₀ = 4 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ₀) A₀ = 2 ∧
              ∃ f : A₀ →* A, Function.Surjective f ∧
                (∀ a : V.subgroupOf Mc,
                  f ((Representation.BinaryOffender.actionHom ρ₀).subgroupMap (V.subgroupOf Mc) a) =
                    (Representation.BinaryOffender.actionHom ρ).subgroupMap (V.subgroupOf Mc) a) ∧
                Nat.card f.ker = 4 ∧ rank f.ker = 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  change rank A = 2 → _
  intro hr
  obtain ⟨hCMc,_,_,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hV₁Mc : V₁ ≤ Mc := (plane_le _).trans hVMc
  have hV₂Mc : V₂ ≤ Mc := (plane_le _).trans hVMc
  let : IsElementaryAbelian 2 (V.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hVMc
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (Representation.BinaryOffender.actionHom ρ)
  have hAc : Nat.card A = 4 := by
    have hh := IsElementaryTwo.card_eq_two_pow_rank
      (show IsElementaryTwo A from ⟨by
        intro hz
        have hzero : rank A = 0 := hz ▸ rank_bot
        omega,inferInstance⟩)
    rw [hr] at hh
    exact hh
  have hcost : fixedCodim σ A = 2 :=
    (((h.decomposable_five_partner_two_core_or_equal_cost
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
        ρ dF).2.1.trans hr
  obtain ⟨_,hFQZ,_,_,_,_⟩ := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨_,_,_,hFel,_,hMcF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := hFel
  have hFMc : F ≤ Mc := (hFQZ.trans inf_le_left).trans (pCoreIn_le 2 Mc)
  have hnBot : Mc ≤ normalizer (⊥ : Subgroup G) := by
    rw [(⊥ : Subgroup G).normalizer_eq_top]; exact le_top
  obtain ⟨τ,⟨dτ⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates Mc F ⊥
    hFMc hMcF bot_le hnBot
  have hfullActors := ((h.decomposable_five_full_span_support_actors
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ) τ dτ
  have hidx (i : d.Index) :
      (centralizer (plane V (c.ambientFactor d i).space : Set G)).relIndex F = 2 := by
    rw [full_fixed_index τ dτ _ ((plane_le _).trans hVMc),(hfullActors i).2.1]
    rfl
  have hCV : centralizer (V : Set G) =
      centralizer (V₁ : Set G) ⊓ centralizer (V₂ : Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (plane_le _)) (centralizer_le (plane_le _))
    · apply le_centralizer_iff.mpr
      rw [←s.complement]
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  have hfixed : F ⊓ centralizer (V : Set G) =
      (F ⊓ centralizer (V₁ : Set G)) ⊓ (F ⊓ centralizer (V₂ : Set G)) := by
    rw [hCV]
    exact inf_inf_distrib_left _ _ _
  have hidxV : (centralizer (V : Set G)).relIndex F = 4 := by
    apply le_antisymm
    · rw [hCV]
      have hh := (relIndex_inf_le (H := centralizer (V₁ : Set G))
        (K := centralizer (V₂ : Set G)) (L := F))
      rw [hidx s.first,hidx s.second] at hh
      exact hh
    · have hh := dF.fixed_quotient_card_le_centralizer_index σ
        (Representation.BinaryOffender.actionHom ρ) V
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
      change 2 ^ fixedCodim σ A ≤ _ at hh
      rw [hcost] at hh
      exact hh
  have hdistinct : F ⊓ centralizer (V₁ : Set G) ≠ F ⊓ centralizer (V₂ : Set G) := by
    intro he
    rw [←he,inf_idem] at hfixed
    have hh := congrArg (fun B : Subgroup G => B.relIndex F) hfixed
    simp only [inf_relIndex_left] at hh
    rw [hidxV,hidx s.first] at hh
    norm_num at hh
  refine ⟨hcost,hfixed,hdistinct,hidxV,?_⟩
  intro W₀ _ _ ρ₀ d₀
  let : Finite W₀ := Finite.of_surjective (fun x : F => (d₀.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp d₀.onto)
  let σ₀ := Representation.BinaryOffender.imageRepresentation ρ₀
  let A₀ := actionSubgroup ρ₀ (V.subgroupOf Mc)
  let q₀ := Representation.BinaryOffender.actionHom ρ₀
  let q := Representation.BinaryOffender.actionHom ρ
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map q₀
  have hCV : V ⊓ centralizer (F : Set G) = E :=
    ((h.decomposable_five_partner_two_core_intersection
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ).1
  have hVcard : Nat.card V = 256 := by
    rw [←s.complement,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _)))).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr s.disjoint),s.support_card,s.support_card]
  have hA₀card : Nat.card A₀ = 16 := by
    have hc := BinaryConjugationSection.actor_image_card_eq_relIndex Mc
      (centralizer (F : Set G)) V q₀ (full_action_kernel ρ₀ d₀) hVMc
    have hh := relIndex_mul_card_of_le (show V ⊓ centralizer (F : Set G) ≤ V from inf_le_left)
    rw [inf_relIndex_left,hCV,s.fixed_card,hVcard] at hh
    change Nat.card A₀ = _ at hc
    omega
  have heA₀ : IsElementaryTwo A₀ := ⟨by intro hz; rw [hz,card_bot] at hA₀card; omega,inferInstance⟩
  have hr₀ : rank A₀ = 4 := by
    have hh : 2^rank A₀ = 2^4 := by rw [←heA₀.card_eq_two_pow_rank,hA₀card]; rfl
    exact Nat.pow_right_injective (by decide : 1 < 2) hh
  have hcost₀ : fixedCodim σ₀ A₀ = 2 := by
    have hh := full_fixed_index ρ₀ d₀ V hVMc
    rw [hidxV] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  let a₀ : V.subgroupOf Mc →* A₀ := q₀.subgroupMap (V.subgroupOf Mc)
  let a : V.subgroupOf Mc →* A := q.subgroupMap (V.subgroupOf Mc)
  have ha₀ : Function.Surjective a₀ := q₀.subgroupMap_surjective _
  have ha : Function.Surjective a := q.subgroupMap_surjective _
  have hker : a₀.ker ≤ a.ker := by
    intro x hx
    have hx₀ : (x : Mc) ∈ q₀.ker := congrArg Subtype.val hx
    rw [full_action_kernel ρ₀ d₀] at hx₀
    have hxρ : (x : Mc) ∈ ρ.ker := (dF.action_mem_ker_iff _).mpr (by
      intro y hy
      have he : ⁅((x : Mc) : G),y⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hx₀ y hy).symm
      rw [he]; exact D.one_mem)
    apply Subtype.ext
    apply (actionHom_eq_one_iff ρ (x : Mc)).mpr
    intro z
    exact LinearMap.congr_fun hxρ z
  let f : A₀ →* A := a₀.liftOfSurjective ha₀ ⟨a,hker⟩
  have hf (x : V.subgroupOf Mc) : f (a₀ x) = a x :=
    a₀.liftOfRightInverse_comp_apply _ _ _ x
  have honto : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := ha y
    exact ⟨a₀ x,hf x⟩
  have hkcard : Nat.card f.ker = 4 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr honto,card_top,hAc,hA₀card] at hh
    omega
  have hkne : f.ker ≠ ⊥ := by intro hz; rw [hz,card_bot] at hkcard; omega
  let : IsElementaryAbelian 2 f.ker := IsElementaryAbelian.of_injective f.ker.subtype f.ker.subtype_injective
  have hkrank : rank f.ker = 2 := by
    have he : IsElementaryTwo f.ker := ⟨hkne,inferInstance⟩
    have hh : 2^rank f.ker = 2^2 := by rw [←he.card_eq_two_pow_rank,hkcard]; rfl
    exact Nat.pow_right_injective (by decide : 1 < 2) hh
  exact ⟨hA₀card,hr₀,hcost₀,f,honto,hf,hkcard,hkrank⟩

end CFSG.Quasithin.Chapter15.Section01
