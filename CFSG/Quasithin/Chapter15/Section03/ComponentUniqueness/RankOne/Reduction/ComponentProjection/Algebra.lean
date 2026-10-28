module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ComponentProjection.Placement
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreRestriction


/-!
# Algebra of the central-product projection

The preimage in `L` and `Y` induce the same group of inner automorphisms
of `L`. The kernel on the preimage is a subgroup of the central two-core.
The common image is two-perfect, and its two-core index divides three.
Core lifting and the two-residual therefore give a nontrivial projection
with two-core index exactly three. Inner representatives also give the
commutator bound needed for residual normalization.

No containment in the local intersection, or in `Y`, is assumed here.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, the inner-action projection on printed p.1139.
-/

public section

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
variable {G : Type*} [Group G]

private theorem normalizes_of_inner {Y L : Subgroup G}
    (hi : ∀ y ∈ Y, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G)) :
    Y ≤ normalizer (L : Set G) := by
  intro y hy
  obtain ⟨l, hl, hc⟩ := hi y hy
  have hm := (normalizer (L : Set G)).mul_mem (L.le_normalizer hl)
    (Subgroup.centralizer_le_normalizer _ hc)
  simpa only [mul_inv_cancel_left] using hm

private theorem representative_in_preimage {Y L : Subgroup G}
    (hi : ∀ y ∈ Y, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G))
    {y : G} (hy : y ∈ Y) :
    ∃ l ∈ preimage Y L, l⁻¹ * y ∈ centralizer (L : Set G) := by
  obtain ⟨l, hl, hc⟩ := hi y hy
  refine ⟨l, ⟨hl, ?_⟩, hc⟩
  have hm := (Y ⊔ centralizer (L : Set G)).mul_mem
    ((le_sup_left : Y ≤ Y ⊔ centralizer (L : Set G)) hy)
    ((le_sup_right : centralizer (L : Set G) ≤ Y ⊔ centralizer (L : Set G))
      ((centralizer (L : Set G)).inv_mem hc))
  change l ∈ Y ⊔ centralizer (L : Set G)
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hm

private theorem action_eq_of_centralizer (L : Subgroup G)
    (a b : normalizer (L : Set G))
    (h : (a : G)⁻¹ * b ∈ centralizer (L : Set G)) :
    L.normalizerMonoidHom a = L.normalizerMonoidHom b := by
  have hk : a⁻¹ * b ∈ L.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact h
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
  exact hk

private theorem core_index_image_dvd {H D : Type*} [Group H] [Group D]
    (f : H →* D) (hf : Function.Surjective f) :
    (pCore 2 D).index ∣ (pCore 2 H).index := by
  have hn : ((pCore 2 H).map f).Normal := Normal.map inferInstance f hf
  have hle : (pCore 2 H).map f ≤ pCore 2 D :=
    le_sSup ⟨hn, pCore_isPGroup.map f⟩
  exact (index_dvd_of_le hle).trans ((pCore 2 H).index_map_dvd hf)

private theorem core_index_injective_dvd {H D : Type*} [Group H] [Group D]
    (f : H →* D) (hf : Function.Injective f) :
    (pCore 2 H).index ∣ (pCore 2 D).index := by
  have hle : (pCore 2 D).comap f ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective f hf⟩
  exact (index_dvd_of_le hle).trans (by
    rw [index_comap]
    exact relIndex_dvd_index_of_normal _ _)

private theorem index_three_of_nontrivial {A : Subgroup G}
    (hp : IsPPerfect 2 A) (hne : A ≠ ⊥) (hi : (pCore 2 A).index ∣ 3) :
    (pCore 2 A).index = 3 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hi with h | h
  · have ht : pCore 2 A = ⊤ := index_eq_one.mp h
    have htwo : IsPGroup 2 A := (ht ▸ pCore_isPGroup).of_equiv topEquiv
    have hz := hp.hom_eq_one_of_isPGroup htwo (MonoidHom.id A)
    exact (hne ((eq_bot_iff_forall A).mpr fun a ha =>
      congrArg Subtype.val (DFunLike.congr_fun hz (⟨a, ha⟩ : A)))).elim
  · exact h

private theorem commutator_le_core_of_index_dvd {H : Type*} [Group H]
    (hi : (pCore 2 H).index ∣ 3) : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ pCore 2 H := by
  let : IsCyclic (H ⧸ pCore 2 H) := isCyclic_of_card_dvd_prime (p := 3) (by
    rwa [← index_eq_card])
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

private theorem preimage_algebra [Finite G] {Y L : Subgroup G}
    (hi : ∀ y ∈ Y, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G))
    (hZ : center L ≤ pCore 2 L) (hp : IsPPerfect 2 Y)
    (hindex : (pCore 2 Y).index = 3) (hact : ⁅L, Y⁆ ≠ ⊥) :
    projection Y L ≠ ⊥ ∧ (pCore 2 (preimage Y L)).index ∣ 3 := by
  let P := preimage Y L
  have hPL : P ≤ L := inf_le_left
  have hn := normalizes_of_inner hi
  let ψ : Y →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  let φ : P →* MulAut L := L.normalizerMonoidHom.comp
    (inclusion (hPL.trans L.le_normalizer))
  have hr : ψ.range = φ.range := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨l, hl, hc⟩ := representative_in_preimage hi y.property
      refine ⟨⟨l, hl⟩, ?_⟩
      exact action_eq_of_centralizer L _ _ hc
    · rintro _ ⟨l, rfl⟩
      have hl : (l : G) ∈ (Y ⊔ centralizer (L : Set G) : Subgroup G) := l.property.2
      have hYC := hn.trans (normalizer_le_normalizer_centralizer L)
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hYC] at hl
      obtain ⟨y, hy, c, hc, he⟩ := hl
      refine ⟨⟨y, hy⟩, ?_⟩
      apply action_eq_of_centralizer L
      change y⁻¹ * (l : G) ∈ centralizer (L : Set G)
      rw [← he, inv_mul_cancel_left]
      exact hc
  let g : Y →* φ.range := ψ.codRestrict φ.range (fun y => hr ▸ ⟨y, rfl⟩)
  have hg : Function.Surjective g := by
    intro d
    have hd : (d : MulAut L) ∈ ψ.range := hr.symm ▸ d.property
    obtain ⟨y, hy⟩ := hd
    exact ⟨y, Subtype.ext hy⟩
  have hpD : IsPPerfect 2 φ.range := hp.of_surjective g hg
  have hiD : (pCore 2 φ.range).index ∣ 3 :=
    (core_index_image_dvd g hg).trans (hindex ▸ dvd_rfl)
  have hk : IsPGroup 2 φ.ker := by
    let j := inclusion hPL
    have hker : φ.ker ≤ (pCore 2 L).comap j := by
      intro x hx
      have hxC : (x : G) ∈ centralizer (L : Set G) := by
        have hx' : inclusion (hPL.trans L.le_normalizer) x ∈ L.normalizerMonoidHom.ker := hx
        rw [normalizerMonoidHom_ker] at hx'
        exact hx'
      exact hZ (mem_center_iff.mpr fun l => Subtype.ext (hxC l l.property))
    exact (pCore_isPGroup.comap_of_injective j (inclusion_injective hPL)).to_le hker
  have hkr : IsPGroup 2 φ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  have hiP : (pCore 2 P).index ∣ 3 := by
    rw [← φ.rangeRestrict.comap_pCore_of_ker_isPGroup φ.rangeRestrict_surjective hkr,
      (pCore 2 φ.range).index_comap_of_surjective φ.rangeRestrict_surjective]
    exact hiD
  refine ⟨?_, hiP⟩
  intro hb
  have hbP : pResidual 2 P = ⊥ := by
    apply map_injective P.subtype_injective
    exact hb.trans (Subgroup.map_bot _).symm
  have hm := map_pResidual_of_surjective 2 φ.rangeRestrict φ.rangeRestrict_surjective
  rw [hbP, Subgroup.map_bot, (pResidual_eq_top_iff 2 φ.range).mpr hpD] at hm
  have hgzero (y : Y) : ψ y = 1 := by
    have hz : g y ∈ (⊥ : Subgroup φ.range) := hm.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hz)
  apply hact
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  intro y hy
  have hky : inclusion hn (⟨y, hy⟩ : Y) ∈ L.normalizerMonoidHom.ker := hgzero ⟨y, hy⟩
  rw [normalizerMonoidHom_ker] at hky
  exact hky

/-- The intrinsic projection has the required nontrivial cubic structure.
The only action assumption is actual inner conjugation on `L`. -/
theorem projection_algebra [Finite G] {Y L : Subgroup G}
    (hi : ∀ y ∈ Y, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G))
    (hZ : center L ≤ pCore 2 L) (hp : IsPPerfect 2 Y)
    (hindex : (pCore 2 Y).index = 3) (hact : ⁅L, Y⁆ ≠ ⊥) :
    projection Y L ≠ ⊥ ∧ (pCore 2 (projection Y L)).index = 3 ∧
      ⁅projection Y L, Y⁆ ≤ (projection Y L).pCoreIn 2 := by
  obtain ⟨hne, hiP⟩ := preimage_algebra hi hZ hp hindex hact
  have hAP := projection_le_preimage Y L
  have hiA : (pCore 2 (projection Y L)).index ∣ 3 :=
    (core_index_injective_dvd (inclusion hAP) (inclusion_injective hAP)).trans hiP
  refine ⟨hne, index_three_of_nontrivial (projection_isPPerfect Y L) hne hiA, ?_⟩
  have hPP : ⁅preimage Y L, preimage Y L⁆ ≤ (preimage Y L).pCoreIn 2 := by
    have hm := map_mono (f := (preimage Y L).subtype) (commutator_le_core_of_index_dvd hiP)
    simpa only [pCoreIn, map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hm
  have hYP := normalizes_projection Y.le_normalizer (normalizes_of_inner hi)
  have hcommA : ⁅projection Y L, Y⁆ ≤ projection Y L :=
    le_normalizer_iff_commutator_le_left.mp hYP
  have hcommP : ⁅projection Y L, Y⁆ ≤ (preimage Y L).pCoreIn 2 := by
    apply commutator_le.mpr
    intro a ha y hy
    obtain ⟨l, hl, hc⟩ := representative_in_preimage hi hy
    have hc' : ⁅a, l⁻¹ * y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hc a (projection_le_component Y L ha))
    have he : ⁅a, y⁆ = ⁅a, l⁆ := by
      calc
        ⁅a, y⁆ = ⁅a, l * (l⁻¹ * y)⁆ := by rw [mul_inv_cancel_left]
        _ = ⁅a, l⁆ := by rw [commutatorElement_mul_right_eq_mul_conj, hc']; simp
    rw [he]
    exact hPP (commutator_mem_commutator (hAP ha) hl)
  exact (le_inf hcommA hcommP).trans (inf_pCoreIn_le_of_le 2 hAP)

end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
