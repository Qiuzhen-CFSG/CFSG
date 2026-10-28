module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The intrinsic component after recognizing the five-centralizer quotient

The central order-five kernel has an A₅ complement by the central splitting
argument. A central supplement makes this complement normal and contains every
perfect subgroup in it. It is itself quasisimple, so it is exactly the intrinsic
layer. Thus the recognized quotient identifies the actual ambient component,
independently of any choices of section or coordinates.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer

variable {G : Type*} [Group G] [Finite G]

private theorem layer_eq_of_central_complement {H : Type*} [Group H]
    (K L : Subgroup H) (hK : K ≤ center H) (hKL : K.IsComplement' L)
    (e : L ≃* alternatingGroup (Fin 5)) : componentLayer H = L := by
  have hn : (⊤ : Subgroup H) ≤ normalizer (L : Set H) := by
    rw [← hKL.sup_eq_top]
    exact sup_le (hK.trans (center_le_normalizer _)) L.le_normalizer
  let : L.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 5)) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  have hcomm : _root_.commutator H ≤ L := by
    have hgen : L ⊔ center H = ⊤ := top_unique (by
      rw [← hKL.symm.sup_eq_top]
      exact sup_le_sup_left hK _)
    exact Normal.commutator_le_of_self_sup_commutative_eq_top hgen inferInstance
  apply le_antisymm
  · apply sSup_le
    intro J hJ
    let : Group.IsPerfect J := hJ.2.toIsPerfect
    exact (by
      rw [← commutator_eq_self (H := J)]
      exact commutator_mono le_top le_top : J ≤ _root_.commutator H).trans hcomm
  · exact le_sSup ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩

/-- The section of the recognized quotient lands exactly in the intrinsic layer. -/
theorem exists_layer_complement (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
      (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ ∧
      s.range = componentLayer (centralizer (E : Set G)) ∧
      (kernel E).IsComplement' (componentLayer (centralizer (E : Set G))) := by
  obtain ⟨s, hs, hc⟩ := exists_complement_of_quotient_equiv E hE e
  have hi : Function.Injective s := by
    intro a b hab
    have hh := congrArg (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))) hab
    exact (DFunLike.congr_fun hs a).symm.trans (hh.trans (DFunLike.congr_fun hs b))
  have hl := layer_eq_of_central_complement (kernel E) s.range (kernel_le_center E)
    hc (MonoidHom.ofInjective hi).symm
  exact ⟨s, hs, hl.symm, hl ▸ hc⟩

/-- The recognized A₅ is the literal component in the ambient group. -/
theorem fiveComponent_equiv (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    Nonempty (fiveComponent E ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨s, hs, hr, _⟩ := exists_layer_complement E hE e
  have hi : Function.Injective s := by
    intro a b hab
    have hh := congrArg (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))) hab
    exact (DFunLike.congr_fun hs a).symm.trans (hh.trans (DFunLike.congr_fun hs b))
  exact ⟨((componentLayer (centralizer (E : Set G))).equivMapOfInjective
    (centralizer (E : Set G)).subtype (centralizer (E : Set G)).subtype_injective).symm.trans
      ((MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hi).symm)⟩

/-- The central order-five subgroup and the intrinsic component generate C_G(E). -/
theorem centralizer_sup (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    E ⊔ fiveComponent E = centralizer (E : Set G) := by
  obtain ⟨_, _, _, hc⟩ := exists_layer_complement E hE e
  have hm := congrArg (Subgroup.map (centralizer (E : Set G)).subtype) hc.sup_eq_top
  simpa only [Subgroup.map_sup, kernel, map_subgroupOf_eq_of_le (five_le_centralizer E hE),
    ← MonoidHom.range_eq_map, range_subtype, fiveComponent] using hm

/-- The same two actual factors have trivial intersection. -/
theorem centralizer_disjoint (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) : Disjoint E (fiveComponent E) := by
  obtain ⟨_, _, _, hc⟩ := exists_layer_complement E hE e
  have hd := hc.disjoint
  rw [disjoint_def] at hd ⊢
  intro x hx hxL
  obtain ⟨y, hy, rfl⟩ := hxL
  exact congrArg Subtype.val (hd hx hy)

/-- The order of the actual component, after quotient recognition. -/
theorem fiveComponent_card (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) : Nat.card (fiveComponent E) = 60 :=
  (Nat.card_congr (fiveComponent_equiv E hE e).some.toEquiv).trans InvolutionGeometry.card_A5

omit [Finite G] in
/-- The recognized quotient has the centralizer order used by the normalizer argument. -/
theorem centralizer_card (E : Subgroup G) (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    Nat.card (centralizer (E : Set G)) = 300 := by
  rw [card_eq_card_quotient_mul_card_subgroup (kernel E),
    Nat.card_congr e.toEquiv, InvolutionGeometry.card_A5, kernel_card E hE]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
