module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ThompsonOffender
public import Theory.GroupTheory.CComponent.QuasisimpleImage
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# Initial MS orbit actions with a central covering kernel

For a normal C-component K with quasisimple K/O₂(K), the centralizer of
W = ⟨Ω₁(Z(R))ᴳ⟩ need not have been identified with O₂(G). Its image modulo
the two-core lies in the Fitting subgroup: component dichotomy places that
image in the center of the unique component. Since O₂ of the quotient is
trivial, this image has odd order. It therefore meets the actual two-group
R trivially modulo O₂(G).

This proves C_R(W) = O₂(G), the exact edge-centralizer condition in MS93
(2.2). It also supplies genuine FF actions on every normal elementary layer
between W and R, through each layer's actual centralizer quotient. No
simplicity or triviality of an odd covering center is assumed.

Source: Meierfrankenfeld--Stellmacher, “Pushing up weak BN-pairs of rank two”
(1993), (2.2) and the opening of (3.2), pp.856--857 and863; Aschbacher--Smith
C.1.31--32, printed pp.135--136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The possible covering kernel on the initial orbit has nilpotent image. -/
theorem centralizer_image_le_fitting (K R : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 G ≤ R)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ r ∈ R, k*r=g)
    (hms : MSCharacteristicCondition R) :
    (centralizer (omegaOrbit R : Set G)).map (QuotientGroup.mk' (pCore 2 G)) ≤
      fittingSubgroup (G ⧸ pCore 2 G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let C := centralizer (omegaOrbit R : Set G)
  let D := C.map q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let : D.Normal := (inferInstance : C.Normal).map q hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hsup : B ⊔ R.map q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g,rfl⟩ := hq x
    obtain ⟨k,hk,r,hr,rfl⟩ := hprod g
    rw [map_mul]
    exact mul_mem ((show B ≤ B ⊔ R.map q from le_sup_left) (mem_map_of_mem q hk))
      ((show R.map q ≤ B ⊔ R.map q from le_sup_right) (mem_map_of_mem q hr))
  have hF : generalizedFitting (G ⧸ pCore 2 G) = B :=
    generalizedFitting_eq_of_quasisimple_two_quotient B
      (isPGroup_quotient_of_sup_eq_top B (R.map q) (hp.map q) hsup)
      (pCore_quotient_pCore_eq_bot 2)
  have hQC : pCore 2 G ≤ C := by
    intro z hz w hw
    exact (((mem_omegaCenterIn_iff _ _).mp
      (omegaOrbit_le_centralOmega R hQR hself hw)).2.1 z hz).symm
  have hBD : ¬ B ≤ D := by
    intro h
    apply component_not_centralizes_omegaOrbit K R hp hne hprod hms
    intro k hk
    obtain ⟨c,hc,he⟩ := h (mem_map_of_mem q hk)
    have hm : k*c⁻¹ ∈ pCore 2 G := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (k*c⁻¹) = 1
      rw [map_mul,map_inv,he]
      exact mul_inv_cancel _
    have hh := C.mul_mem (hQC hm) hc
    simpa only [inv_mul_cancel_right] using hh
  have hcomm : ⁅B,D⁆ = ⊥ :=
    (IsComponent.normal_dichotomy
      (⟨(inferInstance : B.Normal).isSubnormal,inferInstance⟩ : IsComponent _ B) D).resolve_left hBD
  have hDC : D ≤ centralizer (B : Set (G ⧸ pCore 2 G)) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hDB : D ≤ B := by
    rw [←hF]
    exact hDC.trans (hF ▸ centralizer_generalizedFitting_le _)
  let : IsMulCommutative D := ⟨⟨fun a b => Subtype.ext (hDC a.property b (hDB b.property)).symm⟩⟩
  exact le_sSup ⟨inferInstance,inferInstance⟩

/-- The actual MS radical detects every nontrivial two-element of the action. -/
theorem omegaOrbit_radical_centralizer (K R : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 G ≤ R)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ r ∈ R, k*r=g)
    (hms : MSCharacteristicCondition R) :
    R ⊓ centralizer (omegaOrbit R : Set G) = pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := (R ⊓ centralizer (omegaOrbit R : Set G)).map q
  have hA : IsPGroup 2 A := (hp.to_le inf_le_left).map q
  have hAF : A ≤ fittingSubgroup (G ⧸ pCore 2 G) :=
    (map_mono inf_le_right).trans
      (centralizer_image_le_fitting K R hK hp hne hQR hself hprod hms)
  have hAO : A ≤ pPrimeCore 2 (G ⧸ pCore 2 G) :=
    hAF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 (pCore_quotient_pCore_eq_bot 2))
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pPrimeCore 2 (G ⧸ pCore 2 G))) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G ⧸ pCore 2 G)).pow_left n
  have hz : A = ⊥ := le_bot_iff.mp
    ((le_inf le_rfl hAO).trans (disjoint_of_coprime_natCard hcop).le_bot)
  apply le_antisymm
  · simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  · refine le_inf hQR ?_
    intro z hz w hw
    exact (((mem_omegaCenterIn_iff _ _).mp
      (omegaOrbit_le_centralOmega R hQR hself hw)).2.1 z hz).symm

/-- Every normal elementary layer between the original orbit and the core
has an FF action on its literal centralizer quotient. -/
theorem layer_isFFModule (K R X : Subgroup G) [K.Normal] [X.Normal]
    [IsElementaryAbelian 2 X]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 G ≤ R)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ r ∈ R, k*r=g)
    (hms : MSCharacteristicCondition R)
    (hWX : omegaOrbit R ≤ X) (hXR : X ≤ R) :
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation X
        (QuotientGroup.mk' (centralizer (X : Set G)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  apply Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    X (QuotientGroup.mk' (centralizer (X : Set G)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) R hXR
  intro h
  apply hms.thompson_not_le_core hp hne hQR
  rw [←omegaOrbit_radical_centralizer K R hK hp hne hQR hself hprod hms]
  apply le_inf
  · exact sSup_le fun A hA => hA.1
  · rw [QuotientGroup.ker_mk'] at h
    exact h.trans (centralizer_le hWX)

end CFSG.Quasithin.ChapterC.MSCentralOrbit
