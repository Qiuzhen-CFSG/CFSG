module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCoreIntersection
public import Theory.Representation.BinaryConjugationSection.SharpFixedIndex
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# The original rank-one quotient retains a rank-three full-action kernel

The unchanged support images on F/D coincide when the original V-image has
rank one. Sharpness of both actual centralizer indices lifts this equality
to a common fixed hyperplane in full F. The literal C_V(F)=E computes the
full original V-image as E16, and the quotient map to its canonical image
retains its E8 kernel. No faithful-FF quotient inheritance or model callback
is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v w
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem full_action_kernel
    {Mc F : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F ⊥ ρ) :
    (Representation.BinaryOffender.actionHom ρ).ker = (centralizer (F : Set G)).subgroupOf Mc := by
  ext a
  have hk : a ∈ (Representation.BinaryOffender.actionHom ρ).ker ↔ a ∈ ρ.ker := by
    change Representation.BinaryOffender.actionHom ρ a = 1 ↔ ρ a = 1
    rw [actionHom_eq_one_iff]
    exact ⟨fun he => LinearMap.ext he,fun he v => LinearMap.congr_fun he v⟩
  rw [hk,dF.action_mem_ker_iff]
  constructor
  · intro hh f hf
    exact (commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hh f hf))).symm
  · intro hh f hf
    exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hh f hf).symm)

omit [Finite G] in
private theorem bot_commutatorPreimage (F B : Subgroup G) :
    commutatorPreimage F B ⊥ = F ⊓ centralizer (B : Set G) := by
  have hn : F ≤ normalizer (⊥ : Subgroup G) := by rw [(⊥ : Subgroup G).normalizer_eq_top]; exact le_top
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
        (commutator_commutatorPreimage_le F B ⊥ hn)))
  · exact le_commutatorPreimage inf_le_left
      (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le

private theorem full_fixed_index
    {Mc F : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F ⊥ ρ)
    (B : Subgroup G) (hB : B ≤ Mc) :
    (centralizer (B : Set G)).relIndex F =
      2 ^ fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
        (actionSubgroup ρ (B.subgroupOf Mc)) := by
  have hh := dF.fixed_index B hB
  rw [bot_commutatorPreimage,inf_relIndex_left] at hh
  simpa only [fixedCodim_actionSubgroup] using hh

/-- The full original V-image has rank four and cost one in the canonical
rank-one branch; its actual quotient onto the canonical image has rank-three kernel. -/
theorem PreparedChosenModule.decomposable_five_partner_two_rank_one_full_action
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
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (_dF : BinaryConjugationSection Mc F D ρ),
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          rank A = 1 →
          F ⊓ centralizer (V₁ : Set G) = F ⊓ centralizer (V₂ : Set G) ∧
          F ⊓ centralizer (V : Set G) = F ⊓ centralizer (V₁ : Set G) ∧
          (centralizer (V : Set G)).relIndex F = 2 ∧
          ∀ {W₀ : Type w} [AddCommGroup W₀] [Module (ZMod 2) W₀]
            (ρ₀ : Representation (ZMod 2) Mc W₀) (_d₀ : BinaryConjugationSection Mc F ⊥ ρ₀),
            let A₀ := actionSubgroup ρ₀ (V.subgroupOf Mc)
            Nat.card A₀ = 16 ∧ rank A₀ = 4 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ₀) A₀ = 1 ∧
              ∃ f : A₀ →* A, Function.Surjective f ∧
                (∀ a : V.subgroupOf Mc,
                  f ((Representation.BinaryOffender.actionHom ρ₀).subgroupMap (V.subgroupOf Mc) a) =
                    (Representation.BinaryOffender.actionHom ρ).subgroupMap (V.subgroupOf Mc) a) ∧
                Nat.card f.ker = 8 ∧ rank f.ker = 3 := by
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
  let A₁ := actionSubgroup ρ (V₁.subgroupOf Mc)
  let A₂ := actionSubgroup ρ (V₂.subgroupOf Mc)
  change rank A = 1 → _
  intro hr
  obtain ⟨hCMc,_,_,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hV₁Mc : V₁ ≤ Mc := (plane_le _).trans hVMc
  have hV₂Mc : V₂ ≤ Mc := (plane_le _).trans hVMc
  let : IsElementaryAbelian 2 (V.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hVMc
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (Representation.BinaryOffender.actionHom ρ)
  have hAc : Nat.card A = 2 := by
    have hh := IsElementaryTwo.card_eq_two_pow_rank
      (show IsElementaryTwo A from ⟨by
        intro hz
        have hzero : rank A = 0 := hz ▸ rank_bot
        omega,inferInstance⟩)
    rw [hr] at hh
    exact hh
  have hsupport := ((h.decomposable_five_partner_two_support_displacements
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ).2 ρ dF
  have hAe₁ : A₁ = A := eq_of_le_of_card_ge
    (map_mono (subgroupOf_mono Mc (plane_le _))) (by rw [(hsupport s.first).1,hAc])
  have hAe₂ : A₂ = A := eq_of_le_of_card_ge
    (map_mono (subgroupOf_mono Mc (plane_le _))) (by rw [(hsupport s.second).1,hAc])
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
  have hsharp (i : d.Index) :
      Nat.card (W ⧸ fixedSpace σ (actionSubgroup ρ
        ((plane V (c.ambientFactor d i).space).subgroupOf Mc))) =
        (centralizer (plane V (c.ambientFactor d i).space : Set G)).relIndex F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 ^ fixedCodim σ _ = _
    rw [(hsupport i).2.2.1,hidx]
    rfl
  have hcommon : F ⊓ centralizer (V₁ : Set G) = F ⊓ centralizer (V₂ : Set G) := by
    ext x
    constructor
    · intro hx
      have hm := (dF.fixed_coordinates_iff_of_sharp_index σ
        (Representation.BinaryOffender.actionHom ρ) V₁ (hsharp s.first) ⟨x,hx.1⟩).mpr hx.2
      change (dF.coordinates ⟨x,hx.1⟩).toAdd ∈ fixedSpace σ A₁ at hm
      rw [hAe₁,←hAe₂] at hm
      exact ⟨hx.1,(dF.fixed_coordinates_iff_of_sharp_index σ
        (Representation.BinaryOffender.actionHom ρ) V₂ (hsharp s.second) ⟨x,hx.1⟩).mp hm⟩
    · intro hx
      have hm := (dF.fixed_coordinates_iff_of_sharp_index σ
        (Representation.BinaryOffender.actionHom ρ) V₂ (hsharp s.second) ⟨x,hx.1⟩).mpr hx.2
      change (dF.coordinates ⟨x,hx.1⟩).toAdd ∈ fixedSpace σ A₂ at hm
      rw [hAe₂,←hAe₁] at hm
      exact ⟨hx.1,(dF.fixed_coordinates_iff_of_sharp_index σ
        (Representation.BinaryOffender.actionHom ρ) V₁ (hsharp s.first) ⟨x,hx.1⟩).mp hm⟩
  have hfixed : F ⊓ centralizer (V : Set G) = F ⊓ centralizer (V₁ : Set G) := by
    apply le_antisymm (inf_le_inf_left F (centralizer_le (plane_le _)))
    intro x hx
    refine ⟨hx.1,?_⟩
    have hx₂ : x ∈ F ⊓ centralizer (V₂ : Set G) := hcommon ▸ hx
    have hVX : V ≤ centralizer ({x} : Set G) := by
      rw [←s.complement]
      exact sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hx.2 v hv))
        (fun v hv => mem_centralizer_singleton_iff.mpr (hx₂.2 v hv))
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hVX hv)
  have hidxV : (centralizer (V : Set G)).relIndex F = 2 := by
    have hh := congrArg (fun B : Subgroup G => B.relIndex F) hfixed
    simp only [inf_relIndex_left] at hh
    exact hh.trans (hidx s.first)
  refine ⟨hcommon,hfixed,hidxV,?_⟩
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
  have hcost₀ : fixedCodim σ₀ A₀ = 1 := by
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
  have hkcard : Nat.card f.ker = 8 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr honto,card_top,hAc,hA₀card] at hh
    omega
  have hkne : f.ker ≠ ⊥ := by intro hz; rw [hz,card_bot] at hkcard; omega
  let : IsElementaryAbelian 2 f.ker := IsElementaryAbelian.of_injective f.ker.subtype f.ker.subtype_injective
  have hkrank : rank f.ker = 3 := by
    have he : IsElementaryTwo f.ker := ⟨hkne,inferInstance⟩
    have hh : 2^rank f.ker = 2^3 := by rw [←he.card_eq_two_pow_rank,hkcard]; rfl
    exact Nat.pow_right_injective (by decide : 1 < 2) hh
  exact ⟨hA₀card,hr₀,hcost₀,f,honto,hf,hkcard,hkrank⟩

end CFSG.Quasithin.Chapter15.Section01
