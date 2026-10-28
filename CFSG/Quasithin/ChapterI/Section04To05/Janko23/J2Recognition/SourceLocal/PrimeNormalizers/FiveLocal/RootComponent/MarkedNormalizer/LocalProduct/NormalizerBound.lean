module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Component
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.Inverter
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.Assembly
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.PentagonNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Bounding the full five-normalizer through the marked root normalizer

Write U = U(t), C = C_G(E), and N = N_G(E). The recognized quotient
C/E has order sixty, so C has order 300 and U is a Sylow two-subgroup of C.
Frattini's argument inside N, where C is normal, gives
C ∨ (N ∩ N_G(U)) = N.

The marked A₄ × A₅ coordinates of N_G(U) put E in its second factor.
The checked order-ten normalizer of a five-subgroup of A₅ therefore gives
|N ∩ N_G(U)| = 120. The actual A₄ × E subgroup lies in C ∩ N_G(U),
so that intersection has order at least sixty. The subgroup product formula
now gives |N| ≤ 300 · 120 / 60 = 600.

The final application combines this bound with the selected inverter and
marked-product assembly. The independent component-action containment remains
explicit; neither it nor ProductData is a premise of the order bound.
Ambient simplicity and the ambient order 604800 are unnecessary here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
open InvolutionGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_right_factor (P : Subgroup A5) :
    normalizer (((⊥ : Subgroup A4).prod P) : Set (A4 × A5)) =
      (⊤ : Subgroup A4).prod (normalizer (P : Set A5)) := by
  ext a
  simp only [mem_normalizer_iff, mem_prod, mem_bot, mem_top, true_and,
    Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, conj_eq_one_iff]
  constructor
  · intro h b
    simpa using h (1, b)
  · intro h b
    exact and_congr Iff.rfl (h b.2)

private theorem marked_intersection_bounds {D : Seed G}
    (S : SelectedGeometry D) (E : Subgroup G) (hE : Nat.card E = 5)
    (hEt : E ≤ involutionCentralizer S.t) :
    Nat.card (normalizer (E : Set G) ⊓ normalizer (rootCore S.t : Set G) : Subgroup G) ≤ 120 ∧
    60 ≤ Nat.card (centralizer (E : Set G) ⊓ normalizer (rootCore S.t : Set G) : Subgroup G) := by
  let H := normalizer (rootCore S.t : Set G)
  let f : A4 × A5 →* G := H.subtype.comp S.normalizerEquiv.symm.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp S.normalizerEquiv.symm.injective
  have hfr : f.range = H := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (S.normalizerEquiv.symm a).property
    · intro hx
      exact ⟨S.normalizerEquiv ⟨x, hx⟩,
        congrArg Subtype.val (S.normalizerEquiv.symm_apply_apply _)⟩
  have hEf : E ≤ ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map f := by
    change E ≤ ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map
      (H.subtype.comp S.normalizerEquiv.symm.toMonoidHom)
    rw [S.normalizer_component, S.component_eq]
    exact five_le_fiveFactor S.model E hE hEt
  let P : Subgroup A5 := E.comap (f.comp (MonoidHom.inr A4 A5))
  have hEP : E = ((⊥ : Subgroup A4).prod P).map f := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hax⟩ := hEf hx
      refine ⟨a, ⟨ha.1, ?_⟩, hax⟩
      change f (1, a.2) ∈ E
      have ha1 : a.1 = 1 := ha.1
      simpa only [← ha1, Prod.mk.eta, hax] using hx
    · rintro ⟨a, ha, rfl⟩
      have ha2 : f (1, a.2) ∈ E := ha.2
      have ha1 : a.1 = 1 := ha.1
      simpa only [← ha1, Prod.mk.eta] using ha2
  have hP : Nat.card P = 5 := by
    have hh := congrArg (fun K : Subgroup G => Nat.card K) hEP
    rw [card_map_of_injective hf,
      Nat.card_congr (prodEquiv (⊥ : Subgroup A4) P).toEquiv,
      Nat.card_prod, card_bot, one_mul] at hh
    exact hh.symm.trans hE
  have hEr : E ≤ f.range := hEf.trans (map_le_range _ _)
  have hpre : (normalizer (E : Set G)).comap f =
      (⊤ : Subgroup A4).prod (normalizer (P : Set A5)) := by
    rw [comap_normalizer_eq_of_le_range hEr, hEP,
      comap_map_eq_self_of_injective hf, normalizer_right_factor]
  have hN : Nat.card (normalizer (E : Set G) ⊓ H : Subgroup G) = 120 := by
    have hm : ((normalizer (E : Set G)).comap f).map f = normalizer (E : Set G) ⊓ H := by
      rw [map_comap_eq, hfr, inf_comm]
    rw [← hm, card_map_of_injective hf, hpre,
      Nat.card_congr (prodEquiv (⊤ : Subgroup A4) (normalizer (P : Set A5))).toEquiv,
      Nat.card_prod, card_top, alternatingGroup.FiveLocalGeometry.five_normalizer_card P hP,
      nat_card_alternatingGroup]
    norm_num
  have hPc : P ≤ centralizer (P : Set A5) := five_le_centralizer P hP
  have hC : ((⊤ : Subgroup A4).prod P).map f ≤ centralizer (E : Set G) ⊓ H := by
    rintro x ⟨a, ha, rfl⟩
    refine ⟨?_, (S.normalizerEquiv.symm a).property⟩
    intro y hy
    rw [hEP] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    apply congrArg f
    have hb1 : b.1 = 1 := hb.1
    exact Prod.ext (by simp [hb1]) (hPc ha.2 b.2 hb.2)
  have hcard : Nat.card (((⊤ : Subgroup A4).prod P).map f) = 60 := by
    rw [card_map_of_injective hf, Nat.card_congr (prodEquiv (⊤ : Subgroup A4) P).toEquiv,
      Nat.card_prod, card_top, hP, nat_card_alternatingGroup]
    norm_num
  exact ⟨hN.le, hcard ▸ card_le_of_le hC⟩

private theorem frattini_join {D : Seed G} (S : SelectedGeometry D)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* A5) :
    centralizer (E : Set G) ⊔
      (normalizer (E : Set G) ⊓ normalizer (rootCore S.t : Set G)) =
        normalizer (E : Set G) := by
  let N := normalizer (E : Set G)
  let C := centralizer (E : Set G)
  let U := rootCore S.t
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hUC : U ≤ C := rootCore_le_centralizer S.model E hEt
  have hUN : U ≤ N := hUC.trans hCN
  let C₀ := C.subgroupOf N
  let U₀ := U.subgroupOf N
  have hU₀C₀ : U₀ ≤ C₀ := fun _ hx => hUC hx
  have hC₀ : Nat.card C₀ = 300 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).trans (centralizer_card E hE e)
  have hU₀ : Nat.card U₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv).trans S.model.rootCore_card
  have hU₁ : Nat.card (U₀.subgroupOf C₀) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hU₀C₀).toEquiv).trans hU₀
  let P : Sylow 2 C₀ := Sylow.ofCard (U₀.subgroupOf C₀) (by rw [hU₁, hC₀]; decide +kernel)
  have hm : (P : Subgroup C₀).map C₀.subtype = U₀ := map_subgroupOf_eq_of_le hU₀C₀
  have hj := P.normalizer_sup_eq_top
  change normalizer ((P : Subgroup C₀).map C₀.subtype : Set N) ⊔ C₀ = ⊤ at hj
  rw [hm, ← subgroupOf_normalizer_eq hUN] at hj
  have hj' := congrArg (Subgroup.map N.subtype) hj
  rw [Subgroup.map_sup, subgroupOf_map_subtype, map_subgroupOf_eq_of_le hCN,
    ← MonoidHom.range_eq_map, range_subtype] at hj'
  simpa only [inf_comm, sup_comm] using hj'

/-- The marked root normalizer bounds the full five-normalizer, independently of
its action on the intrinsic five-centralizer component. -/
theorem normalizer_card_le {D : Seed G} (S : SelectedGeometry D)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    Nat.card (normalizer (E : Set G)) ≤ 600 := by
  obtain ⟨hN, hC⟩ := marked_intersection_bounds S E hE hEt
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (centralizer (E : Set G))
    (normalizer (E : Set G) ⊓ normalizer (rootCore S.t : Set G))
    (inf_le_left.trans (normalizer_le_normalizer_centralizer E))
  rw [centralizer_card E hE e, frattini_join S E hE hEt e,
    ← inf_assoc, inf_eq_left.mpr (Subgroup.centralizer_le_normalizer (E : Set G))] at hm
  have hbound := Nat.mul_le_mul_right (Nat.card (normalizer (E : Set G))) hC
  nlinarith

/-- The selected inverter and the proved order bound construct the marked
product once the independent component-action containment is supplied. -/
theorem productData_of_selected_action {D : Seed G} (S : SelectedGeometry D)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5))
    (ha : rootComponent S.t ⊓ normalizer (E : Set G) ≤
      centralizer (fiveComponent E : Set G)) : Nonempty (ProductData D E) := by
  obtain ⟨j, hjc, hconj, hj, hinv⟩ := selected_inverter S E hE hEt
  exact productData_of_inverter_and_bound D E hE e (normalizer_card_le S E hE hEt e)
    j hj hconj hinv (ha ⟨hjc, mem_normalizer_of_inverts E j hinv⟩)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
