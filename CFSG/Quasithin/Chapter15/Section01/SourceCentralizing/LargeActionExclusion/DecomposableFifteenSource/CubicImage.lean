module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFifteen
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SharpExtension
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFifteen

/-!
# Two independent cubic images on the original partner module

The canonical cubic part of the marked order-fifteen residual acts on one
Thompson four-group and fixes the other. Its conjugate by the original
Sylow exchange has the opposite support. Their literal images on the
partner module commute, intersect trivially, and generate an elementary
abelian group of order nine.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem independent_automorphism_supports
    {D W : Type*} [Group D] [Group W]
    (ρ : D →* MulAut W) (hf : Function.Injective ρ)
    (X Y : Subgroup D) (P Q : Subgroup W) (hgen : P ⊔ Q = ⊤)
    (hXP : ∀ x ∈ X, ∀ w ∈ P, ρ x w = w)
    (hYQ : ∀ y ∈ Y, ∀ w ∈ Q, ρ y w = w)
    (hXQ : ∀ x ∈ X, ∀ w ∈ Q, ρ x w ∈ Q)
    (hYP : ∀ y ∈ Y, ∀ w ∈ P, ρ y w ∈ P) :
    X ≤ centralizer (Y : Set D) ∧ Disjoint X Y := by
  have hext (a b : MulAut W) (hP : ∀ w ∈ P,a w=b w)
      (hQ : ∀ w ∈ Q,a w=b w) : a=b := by
    have he : (⊤ : Subgroup W) ≤ a.toMonoidHom.eqLocus b.toMonoidHom := by
      rw [←hgen]
      exact sup_le hP hQ
    ext w
    exact he (mem_top w)
  constructor
  · intro x hx y hy
    apply hf
    rw [map_mul,map_mul]
    apply hext
    · intro w hw
      change ρ y (ρ x w)=ρ x (ρ y w)
      rw [hXP x hx w hw,hXP x hx _ (hYP y hy w hw)]
    · intro w hw
      change ρ y (ρ x w)=ρ x (ρ y w)
      rw [hYQ y hy w hw,hYQ y hy _ (hXQ x hx w hw)]
  · apply disjoint_iff.mpr
    apply bot_unique
    rintro x ⟨hx,hy⟩
    apply mem_bot.mpr
    apply hf
    rw [map_one]
    exact hext _ _ (hXP x hx) (hYQ x hy)

private theorem cubic_elementary {D : Type*} [Group D] [Finite D]
    (X : Subgroup D) (hc : Nat.card X=3) : IsElementaryAbelian 3 X := by
  let : IsCyclic X := isCyclic_of_prime_card hc
  exact { toIsMulCommutative := inferInstance
          exponent_dvd_p := hc ▸ Group.exponent_dvd_nat_card }

variable {G : Type*} [Group G] [Finite G]

/-- The actual partner action contains an elementary abelian group of order nine. -/
theorem PreparedChosenModule.decomposable_fifteen_partner_cubic_nine
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
      let E := thompsonFixed T V
      ∃ hn : Mc ≤ normalizer (E : Set G),
        ∃ R : Subgroup (internalActionImage Mc E hn),
          IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
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
  obtain ⟨t,ht,hout⟩ : ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V₁ : Set G) := by
    by_contra! hall
    have he := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at he
    contradiction
  let D := internalActionImage Mc E hMcE
  let f : Mc →* D := (actionHom Mc E hMcE).rangeRestrict
  let B := (A.subgroupOf Mc).map f
  let u : D := f ⟨t,hTMc ht⟩
  let B' := B.map (MulAut.conj u).toMonoidHom
  have hBcard : Nat.card B=3 := by
    have hdvd : Nat.card B ∣ 3 := by
      rw [image_card Mc E A hMcE hAMc']
      have hidx : (centralizer (V : Set G)).relIndex A=3 :=
        (image_card M V A h.normalized hAM).symm.trans himage
      exact hidx ▸ relIndex_dvd_of_le_left A (centralizer_le (show E ≤ V from inf_le_left))
    apply (Nat.dvd_prime Nat.prime_three).mp hdvd |>.resolve_left
    intro hbone
    have hBbot : B=⊥ := card_eq_one.mp hbone
    have hAC : A ≤ centralizer (E : Set G) := by
      intro a ha
      have hh := mem_map_of_mem f (show (⟨a,hAMc' ha⟩ : Mc) ∈ A.subgroupOf Mc from ha)
      change f ⟨a,hAMc' ha⟩ ∈ B at hh
      rw [hBbot] at hh
      have he := congrArg Subtype.val (mem_bot.mp hh)
      change (⟨a,hAMc' ha⟩ : Mc) ∈ (actionHom Mc E hMcE).ker at he
      rw [actionHom_ker] at he
      exact he
    have hzero : Z₂=⊥ := bot_unique (by
      intro z hz
      exact hZ₂fixed.le ⟨hz,le_centralizer_iff.mp hAC (show z∈E from hz.2)⟩)
    have hh := s.thompson_card s.second
    change Nat.card Z₂=4 at hh
    rw [hzero,card_bot] at hh
    omega
  have hB'card : Nat.card B'=3 := by
    rw [card_map_of_injective (MulAut.conj u).injective,hBcard]
  let P := Z₁.subgroupOf E
  let Q := Z₂.subgroupOf E
  have hZ₁E : Z₁ ≤ E := inf_le_right
  have hZ₂E : Z₂ ≤ E := inf_le_right
  have hPQ : P ⊔ Q=⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hZ₁E,map_subgroupOf_eq_of_le hZ₂E,
      ←MonoidHom.range_eq_map,range_subtype]
    exact s.thompson_split.symm
  have hBP : ∀ b∈B, ∀ w∈P, (b:MulAut E) w=w := by
    rintro b ⟨a,ha,rfl⟩ w hw
    apply Subtype.ext
    change (a:G)*(w:G)*(a:G)⁻¹=(w:G)
    rw [hfix (show (w:G)∈V₁ from hw.1) a ha,mul_inv_cancel_right]
  have hBQ : ∀ b∈B, ∀ w∈Q, (b:MulAut E) w∈Q := by
    rintro b ⟨a,ha,rfl⟩ w hw
    exact le_normalizer_iff.mp hAZ₂ a ha w hw
  have huQ : ∀ w∈Q,(u:MulAut E) w∈P := by
    intro w hw
    change (w:G)∈Z₂ at hw
    have hh := mem_map_of_mem (MulAut.conj t).toMonoidHom hw
    rw [(s.thompson_exchanges t ht hout).2] at hh
    exact hh
  have huiP : ∀ w∈P,(u⁻¹: D).val w∈Q := by
    intro w hw
    have he := (s.thompson_exchanges t ht hout).2
    change (w:G)∈thompsonPlane T V (c.ambientFactor d s.first).space at hw
    rw [←he] at hw
    obtain ⟨z,hz,hzv⟩ := hw
    rw [show u⁻¹=f ⟨t⁻¹,Mc.inv_mem (hTMc ht)⟩ from (map_inv f ⟨t,hTMc ht⟩).symm]
    change (t⁻¹*(w:G)*(t⁻¹)⁻¹)∈Z₂
    rw [inv_inv]
    rw [←hzv]
    change t⁻¹*(t*z*t⁻¹)*t∈Z₂
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using
      (show z∈Z₂ from hz)
  have huiQ : ∀ w∈Q,(u⁻¹: D).val w∈P := by
    intro w hw
    have he := (s.thompson_exchanges t ht hout).1
    change (w:G)∈thompsonPlane T V (c.ambientFactor d s.second).space at hw
    rw [←he] at hw
    obtain ⟨z,hz,hzv⟩ := hw
    rw [show u⁻¹=f ⟨t⁻¹,Mc.inv_mem (hTMc ht)⟩ from (map_inv f ⟨t,hTMc ht⟩).symm]
    change (t⁻¹*(w:G)*(t⁻¹)⁻¹)∈Z₁
    rw [inv_inv]
    rw [←hzv]
    change t⁻¹*(t*z*t⁻¹)*t∈Z₁
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using
      (show z∈Z₁ from hz)
  have hB'Q : ∀ b∈B', ∀ w∈Q,(b:MulAut E) w=w := by
    rintro b ⟨a,ha,rfl⟩ w hw
    change (u:MulAut E) ((a:MulAut E) ((u⁻¹:D).val w))=w
    rw [hBP a ha _ (huiQ w hw)]
    exact (u:MulAut E).apply_symm_apply w
  have hB'P : ∀ b∈B', ∀ w∈P,(b:MulAut E) w∈P := by
    rintro b ⟨a,ha,rfl⟩ w hw
    exact huQ _ (hBQ a ha _ (huiP w hw))
  obtain ⟨hcomm,hdis⟩ := independent_automorphism_supports D.subtype D.subtype_injective
    B B' P Q hPQ hBP hB'Q hBQ hB'P
  let : IsElementaryAbelian 3 B := cubic_elementary B hBcard
  let : IsElementaryAbelian 3 B' := cubic_elementary B' hB'card
  refine ⟨hMcE,B⊔B',IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp hcomm),?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint B B'
    ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _)) hdis,
    hBcard,hB'card]

end CFSG.Quasithin.Chapter15.Section01
