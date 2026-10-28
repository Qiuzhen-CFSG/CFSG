module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.CubicImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionCore
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFifteen

/-!
# The original partner point centralizer has the same two-core

The point centralizer's two-core lies in the original Sylow centralizer,
so it preserves both Thompson planes. The canonical cubic actor normalizes
that core and acts faithfully on the opposite four-group. The resulting
four-group action has trivial two-core, forcing the point core to fix both
planes. It therefore lies in the full partner kernel, whose two-core is
already the partner's two-core.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem four_action_three_divisor_core_free
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hW : Nat.card W=4) (L : Subgroup (MulAut W)) (hthree : 3∣Nat.card L) :
    pCore 2 L=⊥ := by
  let : Nontrivial W := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hW]; decide)
  let : IsKleinFour W := ⟨hW,IsElementaryAbelian.exponent_eq_prime⟩
  have hd : Nat.card L∣6 := IsKleinFour.card_mulAut W ▸ L.card_subgroup_dvd_card
  have hlo : 3≤Nat.card L := Nat.le_of_dvd Nat.card_pos hthree
  have hhi : Nat.card L≤6 := Nat.le_of_dvd (by decide) hd
  have hc : Nat.card L=3 ∨ Nat.card L=6 := by
    interval_cases hh : Nat.card L <;> norm_num at hd <;> omega
  rcases hc with hc|hc
  · have hdiv : Nat.card (pCore 2 L)∣3 := hc ▸ (pCore 2 L).card_subgroup_dvd_card
    have hcop : Nat.Coprime (Nat.card (pCore 2 L)) 3 := by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=L)).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    exact card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv)
  · have hsurj : Function.Surjective L.subtype := by
      apply (Nat.bijective_iff_injective_and_card L.subtype).mpr
        ⟨L.subtype_injective,hc.trans (IsKleinFour.card_mulAut W).symm⟩ |>.surjective
    exact bot_unique ((IsKleinFour.twoCore_le_ker_of_surjective W L.subtype hsurj).trans_eq
      (L.subtype.ker_eq_bot L.subtype_injective))

variable {G : Type*} [Group G] [Finite G]

/-- The actual marked point centralizer and partner have the same embedded two-core. -/
theorem PreparedChosenModule.decomposable_fifteen_partner_point_core
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
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z₁ : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 15 →
      (Mc ⊓ centralizer (Z₁ : Set G)).pCoreIn 2 = Mc.pCoreIn 2 := by
  classical
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z₁ C h15
  let V := localModule T M
  let E := thompsonFixed T V
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let A := (primeToResidual 3 C).map C.subtype
  have hpartner := h.decomposable_fifteen_partner_and_normalization
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive h15
  have hMcE : Mc ≤ normalizer (E : Set G) := by
    change Mc ≤ normalizer (thompsonFixed T V : Set G)
    rw [←hpartner.1]
    exact le_normalizer_conjugateSpanBy _ _
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun F hF => hF.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  obtain ⟨hAMc,hAR,himage,_,hmove⟩ := cubic_actor_of_fixed_normalizer T hM h c d s π hp hs
    hJi hfive hpartner.2.2.2.2.1 h15
  have hAM : A ≤ M := hAMc.trans inf_le_left
  have hAMc' : A ≤ Mc := hAMc.trans inf_le_right
  have hAV : A ≤ normalizer (V : Set G) := hAM.trans h.normalized
  have hAE : A ≤ normalizer (E : Set G) := hAMc'.trans hMcE
  have hV₁ : V₁ ≤ V := map_subtype_le _
  have hV₂ : V₂ ≤ V := map_subtype_le _
  have hgeo := s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi
  have hfix : V₁ ≤ centralizer (A : Set G) :=
    hgeo.1.symm.le.trans (inf_le_right.trans (centralizer_le hAR))
  obtain ⟨_,hV₂fixed⟩ := coprime_cubic_fixed_support M V A V₁ V₂ h.normalized hAM
    himage hV₁ hV₂ s.complement s.disjoint (s.support_card s.first)
    (s.support_card s.second) hfix hmove
  have hZ₂fixed : Z₂ ⊓ centralizer (A : Set G) = ⊥ :=
    bot_unique ((inf_le_inf inf_le_left le_rfl).trans hV₂fixed.le)
  have hAZ₂ : A ≤ normalizer (Z₂ : Set G) := by
    apply le_normalizer_inf ?_ hAE
    rw [←hmove]
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hAV ha),
      mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer ha)]
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let G₁ := centralizer (Z₁ : Set G)
  let MZ := Mc ⊓ G₁
  let Q₁ := MZ.pCoreIn 2
  let S := (T : Subgroup G) ⊓ G₁
  have hZ₁E : Z₁≤E := inf_le_right
  have hSylC : Chapter1.IsSylowIn 2 S C := s.local_sylow hM.1.2 h.normalized c d π hs
  have hSylG : Chapter1.IsSylowIn 2 S G₁ := h.caseI_centralizer_sylow hG T hM hJ hZ₁E (by
    change Chapter1.IsSylowIn 2 S (G₁⊓M)
    rw [inf_comm G₁ M]
    exact hSylC)
  have hSMZ : S≤MZ := le_inf (inf_le_left.trans hTMc) inf_le_right
  obtain ⟨P,hP⟩ := hSylG.restrict hSMZ inf_le_right
  have hQ₁S : Q₁≤S := (pCoreIn_le_sylow MZ P).trans_eq hP
  have hQ₁T : Q₁≤(T : Subgroup G) := hQ₁S.trans inf_le_left
  have hQ₁Z₁ : Q₁≤centralizer (Z₁ : Set G) := (pCoreIn_le 2 MZ).trans inf_le_right
  have hQ₁Z₂ : Q₁≤normalizer (Z₂ : Set G) :=
    ((le_inf hQ₁T (hQ₁S.trans s.centralizer_le_stabilizer)).trans
      s.thompson_normalized).trans inf_le_right
  have hAMZ : A≤MZ := le_inf hAMc' ((map_subtype_le _).trans inf_le_right)
  have hMZQ : MZ≤normalizer (Q₁ : Set G) := MZ.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image MZ (pCore 2 MZ))
  let N := A⊔Q₁
  have hNZ₂ : N≤normalizer (Z₂ : Set G) := sup_le hAZ₂ hQ₁Z₂
  have hNQ : N≤normalizer (Q₁ : Set G) := sup_le (hAMZ.trans hMZQ) Q₁.le_normalizer
  let : IsElementaryAbelian 2 Z₂ := IsElementaryAbelian.of_le
    (show Z₂≤V from inf_le_left.trans hV₂)
  let f := actionHom N Z₂ hNZ₂
  let L := f.range
  have hAc : Nat.card ((A.subgroupOf N).map f.rangeRestrict)=3 := by
    have hdiv : Nat.card ((A.subgroupOf N).map f.rangeRestrict)∣3 := by
      have he : Nat.card ((A.subgroupOf N).map f.rangeRestrict)=
          (centralizer (Z₂ : Set G)).relIndex A := image_card N Z₂ A hNZ₂ le_sup_left
      rw [he]
      have hidx : (centralizer (V : Set G)).relIndex A=3 :=
        (image_card M V A h.normalized hAM).symm.trans himage
      exact hidx ▸ relIndex_dvd_of_le_left A
        (centralizer_le (show Z₂≤V from inf_le_left.trans hV₂))
    apply (Nat.dvd_prime Nat.prime_three).mp hdiv |>.resolve_left
    intro hone
    have hh : (centralizer (Z₂ : Set G)).relIndex A=1 :=
      (image_card N Z₂ A hNZ₂ le_sup_left).symm.trans hone
    have hAC : A≤centralizer (Z₂ : Set G) := relIndex_eq_one.mp hh
    have hzero : Z₂=⊥ := bot_unique (by
      intro z hz
      exact hZ₂fixed.le ⟨hz,le_centralizer_iff.mp hAC hz⟩)
    have hh := s.thompson_card s.second
    change Nat.card Z₂=4 at hh
    rw [hzero,card_bot] at hh
    omega
  have hcoreL : pCore 2 L=⊥ := four_action_three_divisor_core_free
    (s.thompson_card s.second) L (hAc ▸ ((A.subgroupOf N).map f.rangeRestrict).card_subgroup_dvd_card)
  let Qn := Q₁.subgroupOf N
  let : Qn.Normal := normal_subgroupOf_of_le_normalizer hNQ
  have hQn : Qn≤pCore 2 N := le_sSup
    ⟨inferInstance,(isPGroup_pCoreIn 2 MZ).comap_subtype⟩
  have hmap : (pCore 2 N).map f.rangeRestrict≤pCore 2 L := le_sSup
    ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
      pCore_isPGroup.map f.rangeRestrict⟩
  have hQ₁C₂ : Q₁≤centralizer (Z₂ : Set G) := by
    intro x hx
    let xN : N := ⟨x,(show Q₁≤N from le_sup_right) hx⟩
    have hh := hmap (mem_map_of_mem f.rangeRestrict (hQn (show xN∈Qn from hx)))
    rw [hcoreL] at hh
    have he := congrArg Subtype.val (mem_bot.mp hh)
    change xN∈f.ker at he
    rw [actionHom_ker] at he
    exact he
  have hQ₁CE : Q₁≤centralizer (E : Set G) := by
    apply le_centralizer_iff.mpr
    change thompsonFixed T V≤centralizer (Q₁ : Set G)
    rw [s.thompson_split]
    exact sup_le (le_centralizer_iff.mp hQ₁Z₁) (le_centralizer_iff.mp hQ₁C₂)
  have hkernel := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  dsimp only at hkernel
  rw [hpartner.1] at hkernel
  have hCEMZ : centralizer (E : Set G)≤MZ := le_inf hkernel.1 (centralizer_le hZ₁E)
  have hQ₁Q : Q₁≤Mc.pCoreIn 2 := by
    rw [←hkernel.2.1]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 MZ) hQ₁CE (hCEMZ.trans hMZQ)
  have hQCE : Mc.pCoreIn 2≤centralizer (E : Set G) :=
    hkernel.2.1 ▸ pCoreIn_le 2 (centralizer (E : Set G))
  have hQQ₁ : Mc.pCoreIn 2≤Q₁ := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Mc)
    (le_inf (pCoreIn_le 2 Mc) (hQCE.trans (centralizer_le hZ₁E)))
    (inf_le_left.trans (Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))))
  exact le_antisymm hQ₁Q hQQ₁

end CFSG.Quasithin.Chapter15.Section01
