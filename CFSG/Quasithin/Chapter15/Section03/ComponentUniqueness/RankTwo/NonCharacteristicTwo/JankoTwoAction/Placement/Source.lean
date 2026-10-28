module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Models
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SubgroupProductCard


/-!
# Source inputs for the compatible Hall--Janko local marking

The exponent-three quotient makes Y₊ a two-by-three group. Relative
normalization therefore makes Y₊S prime to five. The actual map to Aut(J₂)
preserves its Sylow subgroup and its S₃ × S₃ shadow, so the image has order
divisible by nine.

The identity O²(Y₊) = Y₊ and the normalizing two-group supplement give
O²(Y₊S) = Y₊. Functoriality of residuals then shows that a conjugation
marking Y₊S automatically marks Y₊ with the same conjugator. No local
normalizer placement or action calculation is assumed by these reductions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.36,
15.3.41 and the final paragraph of 15.3.42, printed pp.1135 and 1138.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
variable {G : Type*} [Group G]
variable {I L M Yplus S : Subgroup G} [(L.subgroupOf I).Normal]

/-- The specified equivalence after the centralizer quotient is surjective. -/
theorem modelMap_surjective (j : JankoTwoIdentification I L) :
    Function.Surjective (modelMap j) :=
  j.equivalence.surjective.comp (QuotientGroup.mk'_surjective _)

/-- Contained joins transport to joins under the actual model map. -/
theorem modelImage_sup (j : JankoTwoIdentification I L) {X Z : Subgroup G}
    (hX : X ≤ I) (hZ : Z ≤ I) :
    modelImage j (X ⊔ Z) = modelImage j X ⊔ modelImage j Z := by
  rw [modelImage, subgroupOf_sup hX hZ, Subgroup.map_sup]
  rfl

/-- The source Sylow subgroup is a two-group in the ambient group. -/
theorem source_sylow_isTwoGroup (d : ComponentSetup I L M Yplus S) : IsPGroup 2 S := by
  obtain ⟨P, hP⟩ := d.sylow
  exact hP ▸ P.isPGroup'.map I.subtype

/-- The source Sylow subgroup maps to a full Sylow subgroup of Aut(J₂). -/
theorem modelImage_sylow [Finite G] (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) :
    ∃ P : Sylow 2 Model, (P : Subgroup Model) = modelImage j S := by
  obtain ⟨P, hP⟩ := d.sylow
  have he : (P : Subgroup I) = S.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le ((sylow_le_intersection d).trans inf_le_right)]
  refine ⟨P.mapSurjective (modelMap_surjective j), ?_⟩
  rw [Sylow.coe_mapSurjective, he]
  rfl

/-- The normalizing product Y₊S has no prime-five divisor. -/
theorem join_five_free [Finite G] (d : ComponentSetup I L M Yplus S) :
    ¬ 5 ∣ Nat.card (Yplus ⊔ S : Subgroup G) := by
  have h3 : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus) :=
    isPGroup_iff_pow_pow_eq_one.mpr fun x => ⟨1, by simpa using d.yplus_exponent x⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h3
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 (pCore 2 Yplus) from pCore_isPGroup)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (source_sylow_isTwoGroup d)
  have hY : Nat.card Yplus = 2 ^ m * 3 ^ n := by
    have hc := (pCore 2 Yplus).card_mul_index
    change Nat.card (pCore 2 Yplus) * Nat.card (Yplus ⧸ pCore 2 Yplus) = _ at hc
    rw [hm, hn] at hc
    exact hc.symm
  have hnorm : S ≤ normalizer (Yplus : Set G) :=
    (sylow_le_intersection d).trans (intersection_normalizes_yplus d)
  have hc := card_set_mul_mul_card_inf Yplus S
  rw [← coe_mul_of_right_le_normalizer_left Yplus S hnorm, hY, hk] at hc
  intro hd
  have hd' : 5 ∣ (2 ^ m * 3 ^ n) * 2 ^ k :=
    hc ▸ dvd_mul_of_dvd_left hd _
  rcases Nat.prime_five.dvd_mul.mp hd' with h | h
  · rcases Nat.prime_five.dvd_mul.mp h with h | h
    · have := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at this
    · have := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at this
  · have := Nat.prime_five.dvd_of_dvd_pow h
    norm_num at this

/-- Prime-five freeness survives the actual component-action quotient. -/
theorem modelImage_join_five_free [Finite G] (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) : ¬ 5 ∣ Nat.card (modelImage j (Yplus ⊔ S)) := by
  have hI : Yplus ⊔ S ≤ I := sup_le (d.yplus_le.trans d.component_le)
    ((sylow_le_intersection d).trans inf_le_right)
  intro hd
  apply join_five_free d
  have hm := ((Yplus ⊔ S).subgroupOf I).card_map_dvd (modelMap j)
  rw [Nat.card_congr (subgroupOfEquivOfLe hI).toEquiv] at hm
  exact hd.trans hm

/-- The two-group kernel preserves the full S₃ × S₃ shadow. -/
theorem modelImage_shadow [Finite G] (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) : RankTwoShadow (modelImage j Yplus) (modelImage j S) :=
  rankTwoShadow_map _ (modelMap_kernel_isTwoGroup d j)
    (rankTwoShadow_subgroupOf (d.yplus_le.trans d.component_le)
      ((sylow_le_intersection d).trans inf_le_right) d.shadow)

/-- The surviving rank-two shadow forces a factor of nine. -/
theorem modelImage_join_nine_dvd [Finite G] (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) : 9 ∣ Nat.card (modelImage j (Yplus ⊔ S)) := by
  rw [modelImage_sup j (d.yplus_le.trans d.component_le)
    ((sylow_le_intersection d).trans inf_le_right)]
  let H := modelImage j Yplus ⊔ modelImage j S
  obtain ⟨e⟩ := modelImage_shadow d j
  have hc : Nat.card (H ⧸ twoFrattiniCore H) = 36 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hi : (twoFrattiniCore H).index = 36 := hc
  have hd := (twoFrattiniCore H).index_dvd_card
  rw [hi] at hd
  exact (by decide : 9 ∣ 36).trans hd

/-- Adjoining the normalizing Sylow two-group preserves the two-residual. -/
theorem join_twoResidual [Finite G] (d : ComponentSetup I L M Yplus S) :
    Stellmacher.twoResidualAmbient (Yplus ⊔ S) = Yplus := by
  have hp : IsPPerfect 2 Yplus := by
    apply (pResidual_eq_top_iff 2 Yplus).mp
    apply map_injective Yplus.subtype_injective
    rw [← ComponentIntersection.twoResidualAmbient_eq_map_pResidual, d.yplus_twoResidual]
    simp only [← MonoidHom.range_eq_map, range_subtype]
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact embedded_pResidual_join_pGroup Yplus S hp (source_sylow_isTwoGroup d)
    ((sylow_le_intersection d).trans (intersection_normalizes_yplus d))

/-- Residuals commute with the actual model image for subgroups of I. -/
theorem modelImage_twoResidual [Finite G] (j : JankoTwoIdentification I L)
    (X : Subgroup G) (hX : X ≤ I) :
    modelImage j (Stellmacher.twoResidualAmbient X) =
      Stellmacher.twoResidualAmbient (modelImage j X) := by
  have hres : (Stellmacher.twoResidualAmbient X).subgroupOf I =
      (pResidual 2 (X.subgroupOf I)).map (X.subgroupOf I).subtype := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (by
      rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
      exact (map_subtype_le _).trans hX),
      map_embedded_pResidual, map_subgroupOf_eq_of_le hX,
      ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  rw [modelImage, hres, map_embedded_pResidual,
    ← ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  rfl

/-- A single marking of the join also marks its residual, with no further premise. -/
noncomputable def localMarkingOfJoinConjugacy [Finite G] (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) (g : Model)
    (hg : (modelImage j (Yplus ⊔ S)).map (MulAut.conj g).toMonoidHom = secondNormalizer) :
    LocalMarking j Yplus S := by
  refine ⟨g, hg, ?_⟩
  have hr : Stellmacher.twoResidualAmbient (modelImage j (Yplus ⊔ S)) = modelImage j Yplus := by
    rw [← modelImage_twoResidual j _ (sup_le (d.yplus_le.trans d.component_le)
      ((sylow_le_intersection d).trans inf_le_right)), join_twoResidual d]
  rw [← hr, ComponentIntersection.twoResidualAmbient_eq_map_pResidual,
    map_embedded_pResidual, hg, ← ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  rfl
end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
