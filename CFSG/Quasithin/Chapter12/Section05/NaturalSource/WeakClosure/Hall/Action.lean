module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Action.Actor
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Primitive
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ThreeFree
public import Theory.GroupTheory.PermutingSupCard

/-!
# Odd-prime action exclusion on the original exterior module

Extend the marked L/O₂(L) actor to M ∩ N_G(V). Its surjectivity carries the
restriction of the actual ambient Sylow T to a Sylow of SL₅(2).
For p > 3, the permuting product AT has order prime to three. Its actor image
is a flag stabilizer and hence a two-group; the p-group image of A is trivial.
Literal equivariance therefore says that A centralizes the unchanged V.

The final theorem applies this constructed action input to the actual E.2.2
Hall subgroup. The independent Chapter 4 odd-normalizer control remains with
qt-d-1251-hall-normalizer, and the unconditional Hall conclusion remains with
qt-d-1251-fusion-hall.

Source: Aschbacher--Smith, A.3.15, pp.50--51, and 12.2.11(a), pp.798--799.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The specialized A.3.15 exclusion, with its source inputs constructed. -/
theorem exterior_odd_action_centralizes (s : SylowExteriorMarking D) :
    ExteriorOddActionCentralizes s := by
  classical
  intro p hp hp3 A _hA hAe hAM hAN hperm
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let N := s.marking.M ⊓ normalizer (V : Set G)
  have hLN : L ≤ N := le_inf L.le_normalizer D.normalizes
  have hTN : (T : Subgroup G) ≤ N :=
    le_inf D.sylow_normalizes_component (le_sup_right.trans s.normalizes)
  have hAN' : A ≤ N := le_inf hAM hAN
  obtain ⟨α, hαL, hαV⟩ := s.marking.exists_normalizer_actor
  have hα : Function.Surjective α := by
    intro g
    obtain ⟨q, rfl⟩ := s.marking.quotientEquiv.surjective g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    exact ⟨⟨l, hLN l.property⟩, hαL l⟩
  let β : N →* LinearGroup 5 := (slEquivLinear 5).toMonoidHom.comp α
  have hβ : Function.Surjective β := (slEquivLinear 5).surjective.comp hα
  let S := (T.subtype hTN).mapSurjective hβ
  let P := ((A ⊔ (T : Subgroup G)).subgroupOf N).map β
  have hSP : (S : Subgroup (LinearGroup 5)) ≤ P :=
    map_mono (comap_mono le_sup_right)
  have hdis : Disjoint A (T : Subgroup G) :=
    IsPGroup.disjoint_of_ne p 2 (by omega) A _ (IsElementaryAbelian.isPGroup p A) T.isPGroup'
  have hcard : Nat.card (A ⊔ (T : Subgroup G) : Subgroup G) = Nat.card A * Nat.card T :=
    card_sup_eq_mul_of_permutes_of_disjoint A _ hperm hdis
  have h3A : ¬ 3 ∣ Nat.card A := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    intro hd
    have hd' := (Nat.prime_three.dvd_of_dvd_pow hd)
    have he := (hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd'
    omega
  have h3T : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have h3P : ¬ 3 ∣ Nat.card P := by
    intro hd
    have hc := hd.trans (card_map_dvd ((A ⊔ (T : Subgroup G)).subgroupOf N) β)
    rw [Nat.card_congr (subgroupOfEquivOfLe (sup_le hAN' hTN)).toEquiv, hcard] at hc
    exact (Nat.prime_three.not_dvd_mul h3A h3T) hc
  have hP : IsPGroup 2 P :=
    BinaryLinear.FiveFlagGeometry.isPGroup_of_sylow_le_of_not_three_dvd S P hSP h3P
  let B := (A.subgroupOf N).map β
  have hB : IsPGroup p B := (IsElementaryAbelian.isPGroup p A).comap_subtype.map β
  have hBP : B ≤ P := map_mono (comap_mono le_sup_left)
  have hBbot : B = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne p 2 (by omega) B P hB hP
    exact (inf_eq_left.mpr hBP).symm.trans (disjoint_iff.mp hd)
  have hαA (a : A) : α ⟨a, hAN' a.property⟩ = 1 := by
    apply (slEquivLinear 5).injective
    have hm : β ⟨a, hAN' a.property⟩ ∈ B :=
      mem_map_of_mem β a.property
    rw [hBbot, mem_bot] at hm
    simpa only [β, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, map_one] using hm
  intro a ha
  apply mem_centralizer_iff.mpr
  intro v hv
  have he := hαV ⟨a, hAN' ha⟩ ⟨v, hv⟩
  rw [hαA ⟨a, ha⟩, map_one] at he
  have hc : a * v * a⁻¹ = v := congrArg Subtype.val (s.marking.coordinates.injective he)
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterB

/-- The literal Hall consumer now requires only the independent odd-normalizer
input, in addition to the earlier structural 12.2.2 theorem. -/
theorem exterior_hall_three_of_normalizer_control
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (control : ExteriorOddNormalizerControl s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H) :
    IsPGroup 3 d.witness.abelianGroup :=
  exterior_hall_three_of_controls s h structural (exterior_odd_action_centralizes s)
    control hH hHGi hlarge hP d hmax

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
