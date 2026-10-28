module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Index

/-!
# The pure orbit with the original ambient Sylow marking

The one-dimensional fixed space supplies a nonidentity marked point.
Conjugacy in the original normalizer transports its ambient Sylow and
half-order formula to every pure point. At a natural point, the source
stabilizer lies in the inner layer and hence normalizes the literal dual
summand. The ambient Sylow assertion remains explicit in this transport;
the dimension-five application supplies it from the earlier weak closure.

Source: Aschbacher--Smith 12.1.5(1), printed p.791.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

namespace SourceModel
variable (S : B.SourceModel)
include S

/-- The exact original marked Sylow premise, in the full ambient centralizer. -/
def MarkedAmbientSylow (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) : Prop :=
  ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    ∀ hp : (B.coordinates w).toAdd.2 = 0,
    (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
      S.setup.naturalFixed (S.setup.naturalSylowNormalizer
        ((T.subtype hTM).mapSurjective B.actionProjection_surjective)) →
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G))
      (centralizer ({(w : G)} : Set G))

/-- The original fixed line contains a nonidentity natural point. -/
theorem exists_marked_point (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ w : componentOrbit V (T : Subgroup G), w ≠ 1 ∧
      ∃ hp : (B.coordinates w).toAdd.2 = 0,
        (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
          S.setup.naturalFixed (S.setup.naturalSylowNormalizer
            ((T.subtype hTM).mapSurjective B.actionProjection_surjective)) := by
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have hr := S.setup.naturalSylow_fixed_finrank P
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show
    0 < Module.finrank (ZMod 2) (S.setup.naturalFixed (S.setup.naturalSylowNormalizer P))
    from hr ▸ Nat.zero_lt_one)
  refine ⟨u.val.val.toMul, ?_, (S.natural_marking _).mp u.val.property, u.property⟩
  intro he
  apply hu
  exact Subtype.ext (Subtype.ext (congrArg Additive.ofMul he))

/-- A natural point's relative centralizer preserves the original dual summand. -/
theorem pure_centralizer_le_dualNormalizer
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) ≤
      normalizer (B.dualSummand : Set G) := by
  intro m hm
  let a : normalizer (L : Set G) := ⟨m, hm.1⟩
  have hstab : B.actionProjection a ∈ S.setup.stabilizer (Additive.ofMul w) := by
    change a ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection
    rw [S.stabilizer_comap]
    exact hm.2
  have hl := (S.setup.pure_stabilizer_eq_residual
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw).2 hstab
  rw [← S.component_layer] at hl
  obtain ⟨l, hl⟩ := hl
  apply mem_normalizer_fintype
  intro x hx
  let u : componentOrbit V (T : Subgroup G) := ⟨x, B.dualSummand_le hx⟩
  have he : B.quotientAction (B.actionProjection a) u = B.componentConjugation l u := by
    rw [← hl]
    rfl
  have hdual : (B.componentConjugation l u : G) ∈ B.dualSummand := by
    apply (B.mem_dualSummand _).mpr
    rw [B.coordinates_componentConjugation]
    simp only [toAdd_ofAdd, BinaryNaturalDual.naturalDualRepresentation_apply]
    rw [(B.mem_dualSummand u).mp hx, map_zero]
  have he' := congrArg Subtype.val he
  rw [B.quotientAction_projection_apply] at he'
  exact he' ▸ hdual

/-- Transport of the original marked Sylow, with its image still in M. -/
theorem pure_sylow_in_normalizer_of_marked
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : S.MarkedAmbientSylow hTM)
    (w : componentOrbit V (T : Subgroup G)) (hw : B.IsPureVector w) :
    ∃ P : Sylow 2 (centralizer ({(w : G)} : Set G)),
      (P : Subgroup _).map (centralizer ({(w : G)} : Set G)).subtype ≤
        normalizer (L : Set G) ∧ 2 * Nat.card P = Nat.card T := by
  obtain ⟨v, hv, hp, hfix⟩ := S.exists_marked_point hTM
  obtain ⟨m, hm, he⟩ := (S.ambient_orbit_iff v w hv hw.1).mpr
    (Or.inl ⟨⟨hv, Or.inl hp⟩, hw⟩)
  have hS := hs v hv hp hfix
  have ht := (Chapter1.IsSylowIn.map_iff (MulAut.conj m).toMonoidHom
    (MulAut.conj m).injective).mpr hS
  rw [map_centralizer_singleton, he] at ht
  obtain ⟨P, hP⟩ := ht
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    rintro x ⟨y, hy, rfl⟩
    exact (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem hm (hTM hy.1))
      ((normalizer (L : Set G)).inv_mem hm)
  · have hc := congrArg (fun A : Subgroup G => Nat.card A) hP
    rw [card_map_of_injective (centralizer ({(w : G)} : Set G)).subtype_injective,
      card_map_of_injective (MulAut.conj m).injective] at hc
    rw [hc]
    exact S.naturalSylowNormalizer_card hTM

/-- All pure points have the source half-Sylow order in the ambient group. -/
theorem pure_twoPart_of_marked
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : S.MarkedAmbientSylow hTM) :
    ∀ w, B.IsPureVector w → 2 * B.centralizerTwoPart w = Nat.card T := by
  intro w hw
  obtain ⟨P, _, hP⟩ := S.pure_sylow_in_normalizer_of_marked hTM hs w hw
  simpa only [centralizerTwoPart, P.card_eq_multiplicity] using hP

/-- The transported Sylow preserves W and the literal dual summand. -/
theorem purePointSylows_of_marked
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : S.MarkedAmbientSylow hTM) : B.PurePointSylows := by
  intro w hw hp
  obtain ⟨P, hPM, _⟩ := S.pure_sylow_in_normalizer_of_marked hTM hs w ⟨hw, Or.inl hp⟩
  refine ⟨P, le_inf ?_ ?_⟩
  · rwa [hNM]
  · exact (le_inf hPM (map_subtype_le _)).trans (S.pure_centralizer_le_dualNormalizer w hw hp)

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
