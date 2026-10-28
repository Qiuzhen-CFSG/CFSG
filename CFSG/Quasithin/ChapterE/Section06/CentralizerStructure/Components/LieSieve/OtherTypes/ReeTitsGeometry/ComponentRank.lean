module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal

/-!
# Odd-rank control of component normalization in E.6.8

A nonidentity element of U is an involution, so C_G(U) embeds in an
involution centralizer and is strongly quasithin. Two distinct commuting
centerless component conjugates of odd prime rank at least two would violate
this bound. Hence such a component is normal in C_G(U), and Q normalizes it.

This uses the actual embedded component and the source local rank condition;
it does not classify components or take normalization as an earlier premise.
Source: Aschbacher–Smith, E.6.8, printed p.247, with Definition E.6.4 and
Hypothesis 0.1.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

theorem obstructionCentralizer_stronglyQuasithin (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) :
    IsStronglyQuasithin (centralizer (U : Set G)) := by
  let := h.elementary
  obtain ⟨u, hu, hune⟩ := U.bot_or_exists_ne_one.resolve_left hU.2.1
  have ho : orderOf u = 2 := by
    have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u (hU.1 hu)
    exact (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu2) |>.resolve_left
      (fun he => hune (orderOf_eq_one_iff.mp he))
  have hc := h.simpleQTKE.toIsQTKE.involution_centralizer_stronglyQuasithin ho
  have hle : centralizer (U : Set G) ≤ centralizer ({u} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hu)
  exact hc.of_injective (inclusion hle) (inclusion_injective hle)

/-- A centerless component of odd prime rank at least two is normal in C_G(U). -/
theorem component_normal_of_odd_primeRank (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hZ : center L = ⊥) (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hr : 2 ≤ primeRank p L) : (L.subgroupOf (centralizer (U : Set G))).Normal := by
  let e := subgroupOfEquivOfLe hL.1
  have hZ' : center (L.subgroupOf (centralizer (U : Set G))) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxZ : e x ∈ center L := ((centerCongr e) ⟨x, hx⟩).property
    have hx1 : e x = 1 := mem_bot.mp (hZ ▸ hxZ)
    exact mem_bot.mpr (e.injective (hx1.trans (map_one e).symm))
  apply hL.2.normal_of_centerless_of_primeRank hZ' p
  have hl := primeRank_equiv p e
  have hbound := obstructionCentralizer_stronglyQuasithin h hU p (Fact.out : p.Prime) hp
  omega

/-- The component-normalizer equality needed by the quotient geometry. -/
theorem normalizes_of_odd_primeRank (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hZ : center L = ⊥) (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hr : 2 ≤ primeRank p L) : Q ≤ normalizer (L : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer hL.1).mp
    (component_normal_of_odd_primeRank h hU hL hZ p hp hr)
  apply le_trans _ hn
  rw [hQ]
  exact inf_le_right.trans (centralizer_le hU.1)

/-- A centerless odd-rank witness inside the component suffices; the component
itself may have a center. -/
theorem normalizes_of_centerless_embedding (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    {X : Type*} [Group X] [Finite X] (f : X →* L) (hf : Function.Injective f)
    (hZ : center X = ⊥) (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hr : 2 ≤ primeRank p X) : Q ≤ normalizer (L : Set G) := by
  let H := centralizer (U : Set G)
  let fH : X →* H := (inclusion hL.1).comp f
  have hfH : Function.Injective fH := (inclusion_injective hL.1).comp hf
  let e : X ≃* fH.range := MonoidHom.ofInjective hfH
  have hZ' : center fH.range = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxZ : e.symm x ∈ center X := ((centerCongr e).symm ⟨x, hx⟩).property
    have hx1 : e.symm x = 1 := mem_bot.mp (hZ ▸ hxZ)
    exact mem_bot.mpr (e.symm.injective (hx1.trans (map_one e.symm).symm))
  have hle : fH.range ≤ L.subgroupOf H := by
    rintro _ ⟨x, rfl⟩
    exact (f x).property
  have hn := hL.2.normal_of_centerless_subgroup_of_primeRank hle hZ' p (by
    change primeRank p H < 2 * primeRank p fH.range
    have he : primeRank p X = primeRank p fH.range := primeRank_equiv p e
    have hb := obstructionCentralizer_stronglyQuasithin h hU p (Fact.out : p.Prime) hp
    change primeRank p H ≤ 2 at hb
    omega)
  have hN := (normal_subgroupOf_iff_le_normalizer hL.1).mp hn
  apply le_trans _ hN
  rw [hQ]
  exact inf_le_right.trans (centralizer_le hU.1)

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
