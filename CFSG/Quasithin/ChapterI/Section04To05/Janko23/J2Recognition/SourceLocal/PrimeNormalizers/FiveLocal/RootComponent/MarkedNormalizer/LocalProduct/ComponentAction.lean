module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Component
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.Inverter
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.Assembly
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension

/-!
# Trivial component action in the selected five-normalizer

Write K for the selected root component and L for the intrinsic layer of
C_G(E). The marked A₄ factor B centralizes K, and E lies in K. Quotient
recognition identifies C_G(E) with E × L. Projection of B to E is trivial
by coprimality of twelve and five, so B lies in L. Every element of
K ∩ N_G(E) normalizes L and fixes B pointwise. Faithfulness of restriction
to an order-twelve subgroup of A₅ then makes its action on L trivial.

The selected inverter consequently gives the actual marked ProductData,
with the independent upper bound on the full normalizer still explicit.
The selected geometry and quotient recognition are the authorized inputs;
no ambient simplicity or order hypothesis is needed for this implication.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
variable {G : Type*} [Group G] [Finite G]

private theorem normalizerFourFactor_card {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) :
    Nat.card S.normalizerFourFactor = 12 := by
  let f := (normalizer (InvolutionGeometry.rootCore S.t : Set G)).subtype.comp
    S.normalizerEquiv.symm.toMonoidHom
  have hf : Function.Injective f := by
    intro x y h
    exact S.normalizerEquiv.symm.injective
      ((normalizer (InvolutionGeometry.rootCore S.t : Set G)).subtype_injective h)
  change Nat.card (((⊤ : Subgroup InvolutionGeometry.A4).prod
    (⊥ : Subgroup InvolutionGeometry.A5)).map f) = 12
  rw [card_map_of_injective hf,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_top, card_bot, mul_one, nat_card_alternatingGroup]
  norm_num

/-- The marked A₄ lies in the intrinsic component of the five-centralizer. -/
theorem normalizerFourFactor_le_fiveComponent {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    S.normalizerFourFactor ≤ fiveComponent E := by
  let B := S.normalizerFourFactor
  let L := fiveComponent E
  let C := centralizer (E : Set G)
  have hEK : E ≤ InvolutionGeometry.rootComponent S.t := by
    rw [S.component_eq]
    exact five_le_fiveFactor S.model E hE hEt
  have hBC : B ≤ C := S.normalizerFourFactor_centralizes.trans (centralizer_le hEK)
  have hLC : L ≤ C := map_subtype_le _
  obtain ⟨d, _, hdL⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    C E L (centralizer_sup E hE e) (centralizer_disjoint E hE e)
    (le_centralizer_iff.mpr hLC)
  let f : B →* E := (MonoidHom.fst E L).comp
    (d.toMonoidHom.comp (Subgroup.inclusion hBC))
  have hf (b : B) : f b = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 12 5 by decide)
    · have hb : orderOf b ∣ 12 := by
        simpa only [B, normalizerFourFactor_card S] using orderOf_dvd_natCard b
      exact (orderOf_map_dvd f b).trans hb
    · simpa only [hE] using orderOf_dvd_natCard (f b)
  intro b hb
  have hmem : d ⟨b, hBC hb⟩ ∈ (⊥ : Subgroup E).prod (⊤ : Subgroup L) :=
    ⟨hf ⟨b, hb⟩, mem_top _⟩
  rw [← hdL] at hmem
  obtain ⟨c, hc, he⟩ := hmem
  have he' := d.injective he
  have hbL : (⟨b, hBC hb⟩ : C) ∈ L.subgroupOf C := he' ▸ hc
  exact hbL

/-- The root-component normalizer acts trivially on the intrinsic five-component. -/
theorem root_component_normalizer_centralizes {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    InvolutionGeometry.rootComponent S.t ⊓ normalizer (E : Set G) ≤
      centralizer (fiveComponent E : Set G) := by
  let B := S.normalizerFourFactor
  let L := fiveComponent E
  have hBL : B ≤ L := normalizerFourFactor_le_fiveComponent S E hE hEt e
  have hB : Nat.card (B.subgroupOf L) = 12 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv).trans
      (normalizerFourFactor_card S)
  obtain ⟨eL⟩ := fiveComponent_equiv E hE e
  rintro j ⟨hjK, hjN⟩
  have hmap : L.map (MulAut.conj j).toMonoidHom = L := by
    have hEconj : E.map (MulAut.conj j).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp hjN
    exact (fiveComponent_map (MulAut.conj j) E).trans (congrArg fiveComponent hEconj)
  let a : MulAut L := ((MulAut.conj j).subgroupMap L).trans
    (MulEquiv.subgroupCongr hmap)
  have ha : a = 1 := AlternatingFiveSubgroupExtension.aut_eq_of_agree
    AlternatingFiveSubgroupExtension.restrictionFaithful eL
    (B.subgroupOf L) hB a 1 (by
      intro b
      apply Subtype.ext
      change j * (b.val : G) * j⁻¹ = (b.val : G)
      have hcomm : j * (b.val : G) = (b.val : G) * j :=
        S.normalizerFourFactor_centralizes b.property j hjK
      rw [hcomm, mul_inv_cancel_right])
  intro x hx
  have hfix := congrArg (fun f : MulAut L => (f ⟨x, hx⟩ : G)) ha
  change j * x * j⁻¹ = x at hfix
  exact (mul_inv_eq_iff_eq_mul.mp hfix).symm

/-- The selected inverter and the proved component action construct the marked
product; only the independent bound on the full normalizer remains explicit. -/
theorem selected_product_of_normalizer_bound {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5))
    (hN : Nat.card (normalizer (E : Set G)) ≤ 600) : Nonempty (ProductData D E) := by
  obtain ⟨j, hjK, hjconj, hj, hinv⟩ := selected_inverter S E hE hEt
  exact productData_of_inverter_and_bound D E hE e hN j hj hjconj hinv
    (root_component_normalizer_centralizes S E hE hEt e
      ⟨hjK, mem_normalizer_of_inverts E j hinv⟩)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
