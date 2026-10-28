module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic.OmegaEndgame

/-!
# Source assembly of the final normal-closure argument in 15.4.8

A normal cubic in the actual action centralizer quotient lies in the central
first omega subgroup of its three-core. That subgroup is characteristic and
elementary abelian, so it contains the whole first normal-closure image.
The source three-rank bound and nonnormality force that image to have order
nine. The checked omega endgame then gives the contradiction.

A common normalizer of the nontrivial two-core also proves that the source
member cannot be normal in both chosen maximal two-local overgroups.
The final consumer retains exactly the genuine earlier 15.4.5 cubic-quotient
output, 15.4.9 existence output and universal 15.4.10 action control, with
qt-15-04-prime-reduction / qt-15-04-centralizer-witness as their source owners.
No elementary-image model or normality conclusion is an input.

Source: Aschbacher--Smith, 15.4.8, printed pp.1159--1160.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.SourceAssembly
open FamilySource OmegaEndgame
variable {G : Type*} [Group G]

private def centralThreeOmega (J : Subgroup G) : Subgroup G :=
  (((omega₁ (center (pCore 3 J)) (p := 3)).map (center (pCore 3 J)).subtype).map
    (pCore 3 J).subtype).map J.subtype

private theorem centralThreeOmega_normal (J : Subgroup G) [J.Normal] :
    (centralThreeOmega J).Normal := by
  let : (omega₁ (center (pCore 3 J)) (p := 3)).Characteristic := omega₁_characteristic _
  unfold centralThreeOmega
  infer_instance

private theorem centralThreeOmega_elementary (J : Subgroup G) :
    IsElementaryAbelian 3 (centralThreeOmega J) := by
  let : IsElementaryAbelian 3 (omega₁ (center (pCore 3 J)) (p := 3)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 3 ((omega₁ (center (pCore 3 J)) (p := 3)).map
      (center (pCore 3 J)).subtype) := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 3 (((omega₁ (center (pCore 3 J)) (p := 3)).map
      (center (pCore 3 J)).subtype).map (pCore 3 J).subtype) := IsElementaryAbelian.map_subtype
  exact IsElementaryAbelian.map_subtype

private theorem image_normalized (M U V : Subgroup G)
    (hn : U ≤ normalizer (V : Set G)) :
    image M U ≤ normalizer (image M V : Set (CoreQuotient M)) := by
  have hh : U.subgroupOf M ≤ normalizer (V.subgroupOf M : Set M) := by
    intro u hu
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (hn hu) (v : G)
  exact (map_mono hh).trans ((V.subgroupOf M).le_normalizer_map (quotientMap M))

private theorem image_closure_normal (M X : Subgroup G) : (image M (sourceClosure M X)).Normal := by
  have hYM : sourceClosure M X ≤ M := map_subtype_le _
  have hn := (normal_subgroupOf_iff_le_normalizer hYM).mpr (sourceClosure_normalized M X)
  exact Subgroup.Normal.map hn (quotientMap M) (QuotientGroup.mk'_surjective _)

/-- A source member cannot be normal in two distinct maximal two-local
overgroups of C_G(Z): they would normalize its same nontrivial two-core. -/
theorem not_normal_in_both {T Z X M₁ M₂ : Subgroup G}
    (hX : X ∈ NormalCentralizerXi T Z)
    (hCM₁ : centralizer (Z : Set G) ≤ M₁)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hEC : HasCharacteristicTwo M₁) (hne : M₁ ≠ M₂) :
    ¬ (M₁ ≤ normalizer (X : Set G) ∧ M₂ ≤ normalizer (X : Set G)) := by
  rintro ⟨hn₁, hn₂⟩
  have hXne : X ≠ ⊥ := by
    intro he
    have hs : Subsingleton X := by rw [he]; infer_instance
    exact Xi.core_ne_top hX.1 (Subsingleton.elim _ _)
  have hXM₁ := hX.2.1.trans hCM₁
  have hcore : X.pCoreIn 2 ≠ ⊥ := coreIn_ne_bot_of_normal hEC hXne hXM₁
    ((normal_subgroupOf_iff_le_normalizer hXM₁).mpr hn₁)
  have hn := normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hlocal : IsTwoLocal (normalizer (X.pCoreIn 2 : Set G)) :=
    ⟨X.pCoreIn 2, hcore, isPGroup_pCoreIn 2 X, rfl⟩
  have hle : M₂ ≤ M₁ := (hn₂.trans hn).trans (hM₁.2 hlocal (hn₁.trans hn))
  exact hne (hM₂.eq_of_le hM₁.1 hle).symm

variable [Finite G]

private theorem normal_cubic_le_centralOmega (J : Subgroup G) (A : Subgroup J)
    [A.Normal] (hA : Nat.card A = 3) : A.map J.subtype ≤ centralThreeOmega J := by
  let P := pCore 3 J
  have hAP : A ≤ P := le_sSup ⟨inferInstance, IsPGroup.of_card (p := 3) (n := 1)
    (by simpa using hA)⟩
  have hPC : P ≤ centralizer (A : Set J) := by
    have hc := twoPerfect_centralizes_small_normal (pResidual 2 J) A
      (isPPerfect_pResidual 2) (Or.inr hA)
    apply le_trans ?_ hc
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := J)).exists_card_eq
    have hcop : Nat.Coprime 2 (Nat.card P) := by
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_right n
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    have ho : orderOf (⟨x, hx⟩ : P) = orderOf x :=
      (orderOf_injective P.subtype P.subtype_injective _).symm
    exact hcop.of_dvd_right (ho ▸ orderOf_dvd_natCard (⟨x, hx⟩ : P))
  rintro x ⟨a, ha, rfl⟩
  let ap : P := ⟨a, hAP ha⟩
  have haz : ap ∈ center P := by
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext ((hPC p.property) a ha).symm
  let az : center P := ⟨ap, haz⟩
  have hp : az ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change a ^ 3 = (1 : J)
    have h := pow_card_eq_one' (x := (⟨a, ha⟩ : A))
    rw [hA] at h
    exact congrArg (fun b : A => (b : J)) h
  have hw : az ∈ omega₁ (center P) (p := 3) := subset_closure (by simpa using hp)
  exact ⟨a, ⟨ap, ⟨az, hw, rfl⟩, rfl⟩, rfl⟩

/-- The first literal normal-closure image is elementary of order nine.
Its cubic generator comes from the intrinsic 15.4.5 quotient through the
actual two-core map; elementarity and the order nine are proved here. -/
theorem first_image_elementary_and_card (T : Sylow 2 G) (Z M X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hc : X ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G))
    (h3 : Nat.card (X ⧸ pCore 2 X) = 3) (hr : primeRank 3 M ≤ 2)
    (hnon : ¬ M ≤ normalizer (X : Set G)) :
    IsElementaryAbelian 3 (image M (sourceClosure M X)) ∧
      Nat.card (image M (sourceClosure M X)) = 9 ∧ Nat.card (image M X) = 3 := by
  let H := M ⊓ centralizer (localV (T : Subgroup G) M : Set G)
  let J := image M H
  let Y := sourceClosure M X
  have hXM : X ≤ M := hc.trans inf_le_left
  have hcore := core_le_of_action_control T Z M X hZT hTM hZ hX hc
  obtain ⟨e, _⟩ := coreQuotientEquivImage M X hXM hcore
  have hB : Nat.card (image M X) = 3 := (Nat.card_congr e.symm.toEquiv).trans h3
  have hMH : M ≤ normalizer (H : Set G) := actionCentralizer_normalizes (T : Subgroup G) M
  have hHn : (H.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hMH
  let : J.Normal := Subgroup.Normal.map hHn (quotientMap M) (QuotientGroup.mk'_surjective _)
  have hHC : H ≤ centralizer (Z : Set G) :=
    inf_le_right.trans (action_centralizer_le T Z M hZT hTM hZ)
  have hHX : H ≤ normalizer (X : Set G) := hHC.trans hX.2.2
  have hBJ : image M X ≤ J := map_mono (comap_mono hc)
  let B := (image M X).subgroupOf J
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hBJ).mpr (image_normalized M H X hHX)
  have hBc : Nat.card B = 3 := (Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv).trans hB
  let E := centralThreeOmega J
  let : E.Normal := centralThreeOmega_normal J
  let : IsElementaryAbelian 3 E := centralThreeOmega_elementary J
  have hBE : image M X ≤ E := by
    have hh := normal_cubic_le_centralOmega J B hBc
    rwa [map_subgroupOf_eq_of_le hBJ] at hh
  have hYE : image M Y ≤ E := by
    have hn : normalClosure (X.subgroupOf M : Set M) ≤ E.comap (quotientMap M) :=
      normalClosure_le_normal (map_le_iff_le_comap.mp hBE)
    change (((normalClosure (X.subgroupOf M : Set M)).map M.subtype).subgroupOf M).map
      (quotientMap M) ≤ E
    rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
    exact map_le_iff_le_comap.mpr hn
  let hEl : IsElementaryAbelian 3 (image M Y) := IsElementaryAbelian.of_le hYE
  let := hEl
  have hmax : Nat.card (image M Y) ≤ 9 :=
    (primeRank_le_iff_elementary_card_le (CoreQuotient M)).mp
      (three_rank_quotient_le M hr) (image M Y) hEl
  have hXY : X ≤ Y := by
    intro x hx
    exact ⟨⟨x, hXM hx⟩, le_normalClosure hx, rfl⟩
  have hBY : image M X ≤ image M Y := map_mono (comap_mono hXY)
  have hmin : 3 ≤ Nat.card (image M Y) := hB ▸ card_le_of_le hBY
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 (image M Y)).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp (by
    simpa only [hn] using hmax)
  have hnpos : 0 < n := by
    by_contra hn0
    have he : n = 0 := by omega
    rw [hn, he, pow_zero] at hmin
    omega
  have hnne : n ≠ 1 := by
    intro hn1
    have he : image M X = image M Y := eq_of_le_of_card_ge hBY (by rw [hn, hn1, pow_one, hB])
    have hBn : (image M X).Normal := he.symm ▸ image_closure_normal M X
    have hMn : M ≤ normalizer (lift M (image M X) : Set G) :=
      lift_normalized M M le_rfl (image M X) (by rw [normalizer_eq_top_iff.mpr hBn]; exact le_top)
    rw [perfect_eq_lift_image T hTM hXM hX.1.2.1 hX.1.1] at hMn
    exact hnon hMn
  have hn2 : n = 2 := by omega
  refine ⟨hEl, ?_, hB⟩
  rw [hn, hn2]
  norm_num

/-- The complete final-paragraph implication of 15.4.8 from its genuine
preceding source outputs. No first-image or nonnormal-choice premise remains. -/
theorem contradiction_from_earlier_source
    (T : Sylow 2 G) (Z M₁ M₂ : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM₁ : centralizer (Z : Set G) ≤ M₁) (hCM₂ : centralizer (Z : Set G) ≤ M₂)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂) (hneM : M₁ ≠ M₂)
    (hEC₁ : HasCharacteristicTwo M₁) (hEC₂ : HasCharacteristicTwo M₂)
    (hr₁ : primeRank 3 M₁ ≤ 2) (hr₂ : primeRank 3 M₂ ≤ 2)
    (h9 : (NormalCentralizerXi (T : Subgroup G) Z).Nonempty)
    (h5 : ∀ X ∈ NormalCentralizerXi (T : Subgroup G) Z, Nat.card (X ⧸ pCore 2 X) = 3)
    (h10 : ∀ X ∈ NormalCentralizerXi (T : Subgroup G) Z, ∀ M : Subgroup G,
      IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M →
      X ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G)) : False := by
  obtain ⟨X, hX⟩ := h9
  have hkill (M N : Subgroup G) (hM : IsMaximalTwoLocal M) (hN : IsMaximalTwoLocal N)
      (hCM : centralizer (Z : Set G) ≤ M) (hCN : centralizer (Z : Set G) ≤ N)
      (hne : M ≠ N) (hEC : HasCharacteristicTwo M)
      (hrM : primeRank 3 M ≤ 2) (hrN : primeRank 3 N ≤ 2)
      (hnon : ¬ M ≤ normalizer (X : Set G)) : False := by
    have hc := h10 X hX M hM (sup_le (hX.2.1.trans hCM) (hTC.trans hCM))
    obtain ⟨hE, hY, hB⟩ := first_image_elementary_and_card T Z M X hZT (hTC.trans hCM)
      hZ hX hc (h5 X hX) hrM hnon
    let := hE
    exact OmegaEndgame.source_contradiction T Z M N X hZT hTC hZne hZ hCM hCN
      hM hN hne hEC hX hnon hY hB hrN h10
  by_cases hn₁ : M₁ ≤ normalizer (X : Set G)
  · have hn₂ : ¬ M₂ ≤ normalizer (X : Set G) := fun hn₂ =>
      not_normal_in_both hX hCM₁ hM₁ hM₂ hEC₁ hneM ⟨hn₁, hn₂⟩
    exact hkill M₂ M₁ hM₂ hM₁ hCM₂ hCM₁ hneM.symm hEC₂ hr₂ hr₁ hn₂
  · exact hkill M₁ M₂ hM₁ hM₂ hCM₁ hCM₂ hneM hEC₁ hr₁ hr₂ hn₁

/-- The actual 15.4.8 centralizer equality, once the original 15.4.5, 15.4.9
and 15.4.10 outputs have been supplied by their existing source owners. -/
theorem centralizer_eq_of_earlier_source
    (T : Sylow 2 G) (Z M₁ M₂ : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM₁ : centralizer (Z : Set G) ≤ M₁) (hCM₂ : centralizer (Z : Set G) ≤ M₂)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂) (hneM : M₁ ≠ M₂)
    (hEC₁ : HasCharacteristicTwo M₁) (hEC₂ : HasCharacteristicTwo M₂)
    (hr₁ : primeRank 3 M₁ ≤ 2) (hr₂ : primeRank 3 M₂ ≤ 2)
    (h9 : centralizer (Z : Set G) ≠ (T : Subgroup G) →
      (NormalCentralizerXi (T : Subgroup G) Z).Nonempty)
    (h5 : ∀ X ∈ NormalCentralizerXi (T : Subgroup G) Z, Nat.card (X ⧸ pCore 2 X) = 3)
    (h10 : ∀ X ∈ NormalCentralizerXi (T : Subgroup G) Z, ∀ M : Subgroup G,
      IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M →
      X ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G)) :
    centralizer (Z : Set G) = (T : Subgroup G) := by
  by_contra hne
  exact contradiction_from_earlier_source T Z M₁ M₂ hZT hTC hZne hZ hCM₁ hCM₂
    hM₁ hM₂ hneM hEC₁ hEC₂ hr₁ hr₂ (h9 hne) h5 h10

end CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.SourceAssembly
