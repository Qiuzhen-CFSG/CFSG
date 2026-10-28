module
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.InnerImageGeometry

/-!
# Sylow normalizers for an inner action with central quotient A₅

If H acts through the full inner group of R and R/Z(R) is A₅, its Sylow
two-normalizer maps onto a subgroup of order twelve. Cauchy's theorem gives
an element of order three upstairs. Every normal subgroup of two-power index
contains that element. The kernel of the action is unrestricted.

The original Cartan application takes H = IT and the normal subgroup I.
It supplies the missing full-Sylow lift in Aschbacher--Smith 11.5.6(3),
printed pp.780--781, in CartanCore.Actions.FieldDetection.NilpotentFullNormalizer.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- An inner A₅ action supplies a cubic element in the specified normal subgroup
and the normalizer of the actual Sylow two-subgroup of the whole group. -/
theorem exists_cubic_in_normal_subgroup_sylow_normalizer_of_inner_action {H R : Type*} [Group H] [Finite H]
    [Group R] [Finite R]
    (I : Subgroup H) [I.Normal] (hq : IsPGroup 2 (H ⧸ I))
    (f : H →* MulAut R) (hf : f.range = MulAut.innerSubgroup R)
    (e : (R ⧸ center R) ≃* alternatingGroup (Fin 5)) (S : Sylow 2 H) :
    ∃ b : H, b ∈ I ∧ b ∈ normalizer (S : Set H) ∧ orderOf b = 3 := by
  let g : H →* MulAut.innerSubgroup R := f.codRestrict _ (fun x => hf ▸ ⟨x,rfl⟩)
  have hg : Function.Surjective g := by
    intro a
    have hm : (a : MulAut R) ∈ f.range := hf.symm ▸ a.property
    obtain ⟨x,hx⟩ := hm
    exact ⟨x,Subtype.ext hx⟩
  let a := (e.toMonoidHom.comp (innerEquivCentralQuotient (H := R)).toMonoidHom).comp g
  have ha : Function.Surjective a := e.surjective.comp ((innerEquivCentralQuotient (H := R)).surjective.comp hg)
  let P := S.mapSurjective ha
  have hn := S.normalizer_map_surjective a ha
  have hd : 3 ∣ Nat.card (normalizer (S : Set H)) := by
    have hc := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card P
    have h : 3 ∣ Nat.card ((normalizer (S : Set H)).map a) := by
      rw [hn]
      change 3 ∣ Nat.card (normalizer (P : Set (alternatingGroup (Fin 5))))
      rw [hc]
      decide
    exact h.trans (card_map_dvd _ a)
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (S : Set H)) 3 hd
  have hb3 : orderOf (b : H) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hq1 : QuotientGroup.mk' I (b : H) = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      (hq.orderOf_coprime (by decide : Nat.Coprime 2 3) _) dvd_rfl
      (hb3 ▸ orderOf_map_dvd (QuotientGroup.mk' I) (b : H))
  exact ⟨b,(QuotientGroup.eq_one_iff _).mp hq1,b.property,hb3⟩

end Theory.GroupTheory
