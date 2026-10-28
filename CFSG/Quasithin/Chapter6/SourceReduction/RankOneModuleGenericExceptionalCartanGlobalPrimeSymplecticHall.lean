module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSymplecticHall
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowAlternating

/-!
# The original symplectic Hall plane and Cartan normalization

The marked single-component source row identifies the prescribed right
Hall subgroup B with Fˣ × Fˣ. At field order four this constructs the
literal elementary subgroup B of order nine. A cubic escaping actor
centralizes B and joins it to E₂₇ in N_G(L), contradicting quasithinness.
The saved smaller-Sylow alternating calculation forces precisely that
cubic prime, so it now also excludes A₇ and its central triple cover when
the selected right factor is inside a parabolic. The original H-component
C and the selected factor R remain separate throughout.

More generally, the full right torus has rank two at each prime dividing
|F|−1, whereas an escaping actor leaves at most rank one in B. This proves
normalization when the original left degree is two or four and divides
the marked right degree. The two degrees are not identified. Source-row
selection, the missing field comparisons and the other branches remain
with the Cartan local-to-global assembly; this is not the whole 5.2.2.

Source: Aschbacher–Smith E.2.2(2b), 5.1.10 and 5.2.2,
printed pp.215–216,634,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The prescribed right Hall group is the rank-two torus of the source symplectic row. -/
theorem CartanPair.right_equiv_of_symplectic_source
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) : Nonempty (B ≃* (Fˣ × Fˣ)) := by
  let S := T.subtype hH.1.1.2
  have hP := hstar_minimalParabolic_of_generation_gt_one hTL hH hgen
  let M := (normalizer (L : Set G)).subgroupOf H
  have hmax : ChapterB.minimalParabolicMax S hP = M := by
    let J := ChapterB.minimalParabolicMax S hP
    have hJ := ChapterB.minimalParabolicMax_spec S hP
    have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
      have hh := map_mono (f := H.subtype) hJ.2
      change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    have hJH : J.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
      change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    have hJM : J ≤ M := map_le_iff_le_comap.mp
      (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
    have hn : M ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
    exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm
  have hs : ∀ Y : Subgroup M, IsHallSubgroup OddHall.oddPrimes Y →
      Nonempty (Y ≃* (Fˣ × Fˣ)) := by
    have hh := SymplecticCartan.hall_equiv (F := F) S hP (K := C)
    rw [hmax] at hh
    exact hh hC hc hf hF e he
  let eM : M ≃* (normalizer (L : Set G) ⊓ H : Subgroup G) :=
    (M.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype _ _))
  let Y := (B.subgroupOf (normalizer (L : Set G) ⊓ H)).map eM.symm.toMonoidHom
  have hY : IsHallSubgroup OddHall.oddPrimes Y :=
    ⟨fun p hp => c.right_hall.p_in_pi_of_p_dvd_card p
        (hp.trans (card_map_dvd _ eM.symm.toMonoidHom)),
      fun p hp => c.right_hall.p_in_pi_of_p_dvd_index p
        (hp.trans (index_map_dvd _ eM.symm.surjective))⟩
  obtain ⟨eY⟩ := hs Y hY
  exact ⟨((subgroupOfEquivOfLe c.right_le).symm.trans
    (eM.symm.subgroupMap (B.subgroupOf (normalizer (L : Set G) ⊓ H)))).trans eY⟩

/-- At field order four, the original supplied B itself is elementary of order nine. -/
theorem CartanPair.right_cubic_plane_of_symplectic_four
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 := by
  obtain ⟨eB⟩ := c.right_equiv_of_symplectic_source hTL hH hgen hC hc
    (f := 2) (by decide) hF e he
  have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units,hF]
  let : IsElementaryAbelian 3 (Fˣ × Fˣ) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact hu ▸ pow_card_eq_one' (x := x.1)
      · exact hu ▸ pow_card_eq_one' (x := x.2)) }
  refine ⟨IsElementaryAbelian.of_injective eB.toMonoidHom eB.injective,?_⟩
  rw [Nat.card_congr eB.toEquiv,Nat.card_prod,hu]

/-- The full split torus has two independent p-directions when p divides its order. -/
theorem CartanPair.symplectic_torus_prime_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) : ¬ p ∣ 2 ^ f - 1 := by
  intro hdiv
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨eB⟩ := c.right_equiv_of_symplectic_source h.sylow_normalizes hH hgen hC hc hf hF e he
  have hr := c.right_primeRank_le_one h hd hH.1.1.1
  rw [primeRank_equiv p eB,primeRank_prod_eq_add] at hr
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units,hF]
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdvd
  let E := zpowers x
  have hE : Nat.card E = p := (Nat.card_zpowers x).trans hx
  have hl : 1 ≤ primeRank p Fˣ := primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hE] using pow_card_eq_one' (x := y))
    (by simpa using hE) E.subtype E.subtype_injective
  omega

/-- The source symplectic four-field row excludes every cubic escaping actor,
using the actual E₉ and the literal E₂₇ contradiction inside N_G(L). -/
theorem CartanPair.symplectic_four_actor_not_cubic {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) : p ≠ 3 := by
  intro hp
  subst p
  obtain ⟨hB,hBc⟩ := c.right_cubic_plane_of_symplectic_four h.sylow_normalizes hH hgen hC hc hF e he
  exact h.prime_actor_excluded_of_cubic_plane c hd hB hBc
    ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H))
    (h.prime_actor_not_normalizes hH hd)

/-- In the symplectic source row, the original small-degree Cartan normalizes
the residual whenever its degree divides the marked right degree. -/
theorem Input.cartan_normalizes_of_symplectic_small_degree {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4) (hnf : n ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) : A ≤ normalizer (residual H : Set G) := by
  by_contra hnot
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hs := cartanSmallGeneration_of_degree_two_or_four hH hcard hn
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hnot
  apply c.symplectic_torus_prime_not_dvd h hd hH hgen hC hc hf hF e he
  have hdiv : p ∣ 2 ^ n - 1 := by
    rw [←hcard,←hd.card]
    exact card_dvd_of_le hd.le_cartan
  exact hdiv.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The symplectic four-field row excludes both alternating containing models,
even when R is selected inside a parabolic rather than an H-component. -/
theorem LocalData.symplectic_four_not_alternating_seven_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hm
  exact c.symplectic_four_actor_not_cubic h hd hH hgen hC hc hF e he
    (d.source_overcomponent_alternating_seven_prime h hH c hd hz hSyl hRK hKX hK hKn hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
