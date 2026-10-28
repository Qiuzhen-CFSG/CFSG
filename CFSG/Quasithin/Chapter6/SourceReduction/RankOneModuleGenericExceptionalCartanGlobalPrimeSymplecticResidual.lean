module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSymplecticResidual
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticHall

/-!
# The original symplectic residual in the Cartan argument

The literal residual quotient supplies a genuine normal C-component and
its source Borel marking. The resulting split-torus equivalence applies
to the prescribed right Hall subgroup B, constructing B ≅ E₉ at field
order four and feeding the actual E₂₇ contradiction.

For any symplectic field, an A₅ selected right factor has |B∩R| = 3.
Thus three divides each of the two torus coordinate orders. The right
Hall rank bound excludes a cubic actor, and the smaller-Sylow prime
calculation excludes A₇ and its triple cover as containing models.
This argument permits a selected parabolic factor and compares no field
degrees. Separately, the full normalization conclusion follows when the
original degree is two or four and divides the residual model degree.

The remaining source selection, exchanged row, higher-field and zero-core
branches belong to the same local-to-global assembly. These theorems do
not assert that the original residual always has symplectic type.
Source: Aschbacher–Smith 5.1.10–13 and 5.2.2, pp.634–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem right_torus_of_residual
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ f ∧ Nonempty (B ≃* (Fˣ × Fˣ)) := by
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
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hgen) ChapterE.generationParameter_le_one_of_solvable
  have hh := SymplecticCartan.residual_hall_equiv S hP hs hf hm
  rw [hmax] at hh
  let eM : M ≃* (normalizer (L : Set G) ⊓ H : Subgroup G) :=
    (M.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype _ _))
  let Y := (B.subgroupOf (normalizer (L : Set G) ⊓ H)).map eM.symm.toMonoidHom
  have hY : IsHallSubgroup OddHall.oddPrimes Y :=
    ⟨fun p hp => c.right_hall.p_in_pi_of_p_dvd_card p
        (hp.trans (card_map_dvd _ eM.symm.toMonoidHom)),
      fun p hp => c.right_hall.p_in_pi_of_p_dvd_index p
        (hp.trans (index_map_dvd _ eM.symm.surjective))⟩
  obtain ⟨F,hF,hfin,hchar,hcard,⟨eY⟩⟩ := hh Y hY
  exact ⟨F,hF,hfin,hchar,hcard,⟨((subgroupOfEquivOfLe c.right_le).symm.trans
    (eM.symm.subgroupMap (B.subgroupOf (normalizer (L : Set G) ⊓ H)))).trans eY⟩⟩

/-- The actual residual quotient Sp₄(4) constructs the original B as E₉.
No component choice or Borel marking is an additional hypothesis. -/
theorem CartanPair.right_cubic_plane_of_symplectic_residual
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 := by
  obtain ⟨F,_,_,_,hF,⟨eB⟩⟩ := right_torus_of_residual c hTL hH hgen (f := 2) (by decide) hm
  have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units,hF]; norm_num
  let : IsElementaryAbelian 3 (Fˣ × Fˣ) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact hu ▸ pow_card_eq_one' (x := x.1)
      · exact hu ▸ pow_card_eq_one' (x := x.2)) }
  refine ⟨IsElementaryAbelian.of_injective eB.toMonoidHom eB.injective,?_⟩
  rw [Nat.card_congr eB.toEquiv,Nat.card_prod,hu]

private theorem residual_actor_not_cubic {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4) : p ≠ 3 := by
  intro hp
  subst p
  obtain ⟨hB,hBc⟩ := c.right_cubic_plane_of_symplectic_residual h.sylow_normalizes hH hgen hm
  exact h.prime_actor_excluded_of_cubic_plane c hd hB hBc
    ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H))
    (h.prime_actor_not_normalizes hH hd)

/-- The actual symplectic residual row normalizes the original small Cartan;
only the comparison between the two distinct field degrees remains explicit. -/
theorem Input.cartan_normalizes_of_symplectic_residual_small_degree {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4) (hf : 1 < f) (hnf : n ∣ f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  by_contra hnot
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hs := cartanSmallGeneration_of_degree_two_or_four hH hcard hn
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hnot
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,_,hF,⟨eB⟩⟩ := right_torus_of_residual c h.sylow_normalizes hH hgen hf hm
  have hr := c.right_primeRank_le_one h hd hH.1.1.1
  rw [primeRank_equiv p eB,primeRank_prod_eq_add] at hr
  have hdiv : p ∣ 2 ^ n - 1 := by
    rw [←hcard,←hd.card]
    exact card_dvd_of_le hd.le_cartan
  have hdvd : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units,hF]
    exact hdiv.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdvd
  let E := zpowers x
  have hE : Nat.card E = p := (Nat.card_zpowers x).trans hx
  have hl : 1 ≤ primeRank p Fˣ := primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hE] using pow_card_eq_one' (x := y))
    (by simpa using hE) E.subtype E.subtype_injective
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original Sp₄(4) residual excludes the two alternating containers
for every selected factor, including a factor inside a rank-one parabolic. -/
theorem LocalData.symplectic_residual_not_alternating_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hmodel
  exact residual_actor_not_cubic c h hd hH hgen hm
    (d.source_overcomponent_alternating_seven_prime h hH c hd hz hSyl hRK hKX hK hKn hmodel)


/-- An A₅ right factor in any original symplectic residual row forces the
escaping actor to be quintic, even when the factor belongs to a parabolic. -/
theorem LocalData.A5_right_symplectic_residual_actor_prime
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : p = 5 := by
  rcases hd.prime with hp | hp
  · subst p
    exfalso
    obtain ⟨F,_,_,_,hF,⟨eB⟩⟩ := right_torus_of_residual c h.sylow_normalizes hH hgen hf hm
    have hr := c.right_primeRank_le_one h hd hH.1.1.1
    rw [primeRank_equiv 3 eB,primeRank_prod_eq_add] at hr
    have hBR : Nat.card (B ⊓ R : Subgroup G) = 3 := by
      simpa using d.right_cartan_card c (m := 2) hA5
    have hdiv : 3 ∣ Nat.card B := hBR ▸ card_dvd_of_le (show B ⊓ R ≤ B from inf_le_left)
    rw [Nat.card_congr eB.toEquiv,Nat.card_prod] at hdiv
    have hdvd : 3 ∣ Nat.card Fˣ :=
      ((by decide : Nat.Prime 3).dvd_mul.mp hdiv).elim id id
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
    let E := zpowers x
    have hE : Nat.card E = 3 := (Nat.card_zpowers x).trans hx
    have hl : 1 ≤ primeRank 3 Fˣ := primeRank_ge_of_elementary_embedding
      (fun y : E => by simpa only [hE] using pow_card_eq_one' (x := y))
      (by simpa using hE) E.subtype E.subtype_injective
    omega
  · exact hp

/-- The actual A₅ Hall intersection excludes both alternating containing
models in every symplectic source field; no field-degree comparison is needed. -/
theorem LocalData.A5_right_symplectic_residual_not_alternating_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hmodel
  have hp := d.A5_right_symplectic_residual_actor_prime h hH hgen c hd hf hm hA5
  have hthree := d.source_overcomponent_alternating_seven_prime h hH c hd hz hSyl hRK hKX hK hKn hmodel
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
