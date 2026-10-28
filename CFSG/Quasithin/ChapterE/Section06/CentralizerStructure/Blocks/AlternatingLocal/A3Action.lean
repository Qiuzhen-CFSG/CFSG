module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SylowAction
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The ambient action on an A₃ block

The marked A₃ block L is A₄. Its characteristic Klein four A has order four,
but F = A ∩ C_G(J) is proper when [L,J] = L: otherwise normality of C_G(A)
in N_G(A) would force L to centralize A, contradicting Z(L) = 1. Thus |F| ≤ 2.
If V centralizes J and acts on L through inner conjugators in A, centerlessness
forces those conjugators to lie in F. The actual action image consequently has
order at most two, and exactly two when L does not centralize V.

The final theorem obtains the inner witnesses and the intrinsic Sylow
intersection from the ambient characteristic-two and block hypotheses. Only J
is assumed contained in Q; its normalization of L follows from [L,J] = L.
No assertion that the intrinsic A₄ omega-center quotient has order two is made.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.13(c),
printed pp.124–125, and the ambient A₃ action in E.6.7(2), printed p.246.
This supplies the ambient argument needed in place of the incorrect intrinsic
order-two calculation, whose order-four obstruction is preserved in AlternatingLocal.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.AlternatingLocal

private theorem conj_injective {L : Type*} [Group L] (hc : center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : L →* MulAut L).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hz : x ∈ center L := by
    rw [mem_center_iff]
    intro y
    have hy := MulEquiv.congr_fun (show MulAut.conj x = 1 from hx) y
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [hc, mem_bot] using hz

private theorem four_inner_action_bound {G : Type*} [Group G] [Finite G]
    (L J V : Subgroup G) (A : Subgroup L) [A.Characteristic]
    (hA : Nat.card A = 4) (hc : center L = ⊥)
    (hLJ : ⁅L, J⁆ = L) (hVJ : V ≤ centralizer (J : Set G))
    (hVN : V ≤ normalizer (L : Set G))
    (hinner : ∀ v : V, ∃ z : A, MulAut.conj (z : L) =
      (L.normalizerMonoidHom.comp (inclusion hVN)) v) :
    Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range ≤ 2 := by
  let A' := A.map L.subtype
  let F := A' ⊓ centralizer (J : Set G)
  have hAL : A' ≤ L := map_subtype_le A
  have hAN : L ≤ normalizer (A' : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L A)
  have hJN : J ≤ normalizer (L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hLJ.le
  have hFne : F ≠ A' := by
    intro he
    have hAJ : A' ≤ centralizer (J : Set G) := he ▸ (inf_le_right : F ≤ _)
    have hJA : J ≤ centralizer (A' : Set G) := le_centralizer_iff.mp hAJ
    have hLC : L ≤ normalizer (centralizer (A' : Set G) : Set G) := by
      apply le_normalizer_iff.mpr
      intro l hl c hcc
      exact (normal_subgroupOf_iff (centralizer_le_normalizer (A' : Set G))).mp
        (normal_subgroupOf_centralizer_normalizer (A' : Set G)) c l hcc (hAN hl)
    have hLA : L ≤ centralizer (A' : Set G) := by
      rw [← hLJ]
      exact (commutator_mono le_rfl hJA).trans
        (le_normalizer_iff_commutator_le_right.mp hLC)
    have hAbot : A = ⊥ := by
      apply A.eq_bot_iff_forall.mpr
      intro a ha
      have hz : a ∈ center L := by
        apply mem_center_iff.mpr
        intro l
        apply Subtype.ext
        exact (mem_centralizer_iff.mp (hLA l.property) a (mem_map_of_mem L.subtype ha)).symm
      simpa only [hc, mem_bot] using hz
    have : Nat.card A = 1 := hAbot ▸ card_bot
    omega
  have hAc : Nat.card A' = 4 := (card_map_of_injective L.subtype_injective).trans hA
  have hFc : Nat.card F ≤ 2 := by
    have hd : Nat.card F ∣ 4 := hAc ▸ card_dvd_of_le (inf_le_left : F ≤ A')
    have hlt : Nat.card F < 4 := by
      by_contra! hh
      exact hFne (eq_of_le_of_card_ge inf_le_left (hAc ▸ hh))
    have hd' : Nat.card F ∣ 2 ^ 2 := by simpa using hd
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
    interval_cases k
    · simpa only [he, pow_zero] using (show 1 ≤ 2 by decide)
    · simp only [he, pow_one, le_refl]
    · norm_num [he] at hlt
  let f := L.normalizerMonoidHom.comp (inclusion hVN)
  let g : F →* MulAut L := MulAut.conj.comp (inclusion ((inf_le_left : F ≤ A').trans hAL))
  have hfg : f.range ≤ g.range := by
    rintro a ⟨v, rfl⟩
    obtain ⟨z, hz⟩ := hinner v
    have hzF : ((z : L) : G) ∈ F := by
      refine ⟨mem_map_of_mem L.subtype z.property, ?_⟩
      apply mem_centralizer_iff.mpr
      intro j hj
      let aj := L.normalizerMonoidHom ⟨j, hJN hj⟩
      have hcomm : Commute aj (f v) := by
        apply Commute.map (f := L.normalizerMonoidHom)
        apply Subtype.ext
        exact mem_centralizer_iff.mp (hVJ v.property) j hj
      have he : MulAut.conj (aj (z : L)) = MulAut.conj (z : L) := by
        apply MulEquiv.ext
        intro x
        have hh := congrArg (fun a : MulAut L => a (aj.symm x)) hcomm.eq
        rw [← hz] at hh
        simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.apply_symm_apply] using hh
      have hzfix := conj_injective hc he
      have hzg : j * (z : L).val * j⁻¹ = (z : L).val := congrArg Subtype.val hzfix
      exact mul_inv_eq_iff_eq_mul.mp hzg
    exact ⟨⟨((z : L) : G), hzF⟩, hz⟩
  exact (card_le_of_le hfg).trans
    ((Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective).trans hFc)

/-- An A₃ block has an ambient action image of order at most two when
`[L,J] = L`, V centralizes J, and V acts by elements of a Sylow two-subgroup
of L. All the normalizer actions and inner conjugations are literal.
In E.6.7, J is J(Q); no normalization by the whole of Q is required. -/
theorem a3_ambient_action_card_le_two {G : Type*} [Group G] [Finite G]
    (L J V : Subgroup G) (e : L ≃* alternatingGroup (Fin 4))
    (S : Sylow 2 L) (hLJ : ⁅L, J⁆ = L)
    (hVJ : V ≤ centralizer (J : Set G))
    (hVN : V ≤ normalizer (L : Set G))
    (hinner : ∀ v ∈ V, ∃ z ∈ (S : Subgroup L).map L.subtype,
      ∀ l ∈ L, z * l * z⁻¹ = v * l * v⁻¹) :
    Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range ≤ 2 := by
  let K := alternatingGroup.kleinFour (Fin 4)
  let A := K.comap e.toMonoidHom
  let : K.Characteristic := alternatingGroup.characteristic_kleinFour (Nat.card_fin 4)
  let : A.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    have hh := characteristic_iff_le_comap.mp (inferInstance : K.Characteristic)
      ((e.symm.trans a).trans e) hx
    change e (a (e.symm (e x))) ∈ K at hh
    change e (a x) ∈ K
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hA : Nat.card A = 4 := by
    dsimp [A]
    rw [comap_equiv_eq_map_symm]
    exact (card_map_of_injective e.symm.injective).trans
      (alternatingGroup.kleinFour_card_of_card_eq_four (Nat.card_fin 4))
  have hc : center L = ⊥ := by
    apply (center L).eq_bot_of_card_eq
    calc
      Nat.card (center L) = Nat.card (center (alternatingGroup (Fin 4))) :=
        Nat.card_congr (centerCongr e).toEquiv
      _ = 1 := by
        rw [alternatingGroup.center_eq_bot (by simp)]
        exact card_bot
  have hSA : (S : Subgroup L) ≤ A := by
    intro x hx
    change e x ∈ alternatingGroup.kleinFour (Fin 4)
    rw [← alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (Nat.card_fin 4)
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)]
    change e x ∈ (S : Subgroup L).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom hx
  apply four_inner_action_bound L J V A hA hc hLJ hVJ hVN
  intro v
  obtain ⟨z, ⟨zL, hzL, rfl⟩, hz⟩ := hinner v v.property
  refine ⟨⟨zL, hSA hzL⟩, ?_⟩
  apply MulEquiv.ext
  intro l
  apply Subtype.ext
  exact hz l l.property

/-- If the A₃ block escapes the centralizer of V, its actual action image
has order exactly two. Nontriviality is derived from the subgroup condition,
without selecting an escaping actor in the hypotheses. -/
theorem a3_ambient_action_card_eq_two {G : Type*} [Group G] [Finite G]
    (L J V : Subgroup G) (e : L ≃* alternatingGroup (Fin 4))
    (S : Sylow 2 L) (hLJ : ⁅L, J⁆ = L)
    (hVJ : V ≤ centralizer (J : Set G))
    (hVN : V ≤ normalizer (L : Set G))
    (hinner : ∀ v ∈ V, ∃ z ∈ (S : Subgroup L).map L.subtype,
      ∀ l ∈ L, z * l * z⁻¹ = v * l * v⁻¹)
    (hescape : ¬ L ≤ centralizer (V : Set G)) :
    Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range = 2 := by
  have hle := a3_ambient_action_card_le_two L J V e S hLJ hVJ hVN hinner
  let f := L.normalizerMonoidHom.comp (inclusion hVN)
  have hne : f.range ≠ ⊥ := by
    intro he
    apply hescape
    apply le_centralizer_iff.mpr
    intro v hv
    apply mem_centralizer_iff.mpr
    intro l hl
    have hf : f ⟨v, hv⟩ = 1 := by
      have : f ⟨v, hv⟩ ∈ f.range := ⟨⟨v, hv⟩, rfl⟩
      rwa [he, mem_bot] at this
    have hh := congrArg (fun a : MulAut L => (a ⟨l, hl⟩ : G)) hf
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hgt := f.range.one_lt_card_iff_ne_bot.mpr hne
  change Nat.card f.range ≤ 2 at hle
  change Nat.card f.range = 2
  omega

/-- Direct adapter from the omega-center witnesses proved by `SylowAction`.
The marked equality identifies the actual Sylow intersection with the intrinsic
Sylow subgroup; J need only centralize V and satisfy the source commutator equality. -/
theorem a3_omega_inner_action_card_le_two {G : Type*} [Group G] [Finite G]
    (L J V Q : Subgroup G) (e : L ≃* alternatingGroup (Fin 4))
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hLJ : ⁅L, J⁆ = L) (hVJ : V ≤ centralizer (J : Set G))
    (hVN : V ≤ normalizer (L : Set G))
    (hinner : ∀ v ∈ V, ∃ z ∈ Stellmacher.omegaOneCenterAmbient (L ⊓ Q),
      ∀ l ∈ L, z * l * z⁻¹ = v * l * v⁻¹) :
    Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range ≤ 2 := by
  apply a3_ambient_action_card_le_two L J V e S hLJ hVJ hVN
  intro v hv
  obtain ⟨z, hz, he⟩ := hinner v hv
  exact ⟨z, hS ▸ (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.1, he⟩

/-- The A₃ action bound from the actual E.6.7 block and Sylow data.
The generalized-Fitting, block, and marked A₄ inputs are the earlier source
facts. The inner witnesses are proved by `central_elementary_sylow_block_action`. -/
theorem a3_central_elementary_sylow_action {G : Type*} [Group G] [Finite G]
    (hG : generalizedFitting G = pCore 2 G) (Q : Sylow 2 G)
    (L : Subgroup G) (hL : ChapterC.IsBlock L)
    (e : L ≃* alternatingGroup (Fin 4))
    (J : Subgroup G) (hJQ : J ≤ (Q : Subgroup G)) (hLJ : ⁅L, J⁆ = L)
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : V ≤ (Q : Subgroup G) ⊓ centralizer (Q : Set G)) :
    ∃ hVN : V ≤ normalizer (L : Set G),
      Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range ≤ 2 ∧
        (¬ L ≤ centralizer (V : Set G) →
          Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range = 2) := by
  obtain ⟨hVN, hi⟩ := central_elementary_sylow_block_action hG Q L hL V hV
  obtain ⟨S, hS⟩ := Q.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  have hSmap : (S : Subgroup L).map L.subtype = L ⊓ (Q : Subgroup G) := by
    rw [hS, subgroupOf_map_subtype, inf_comm]
  have hVJ : V ≤ centralizer (J : Set G) :=
    (hV.trans inf_le_right).trans (centralizer_le hJQ)
  have hinner : ∀ v ∈ V, ∃ z ∈ (S : Subgroup L).map L.subtype,
      ∀ l ∈ L, z * l * z⁻¹ = v * l * v⁻¹ := by
    intro v hv
    obtain ⟨z, hz, he⟩ := hi v hv
    refine ⟨z, ?_, he⟩
    rw [hSmap]
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact ⟨hVN, a3_ambient_action_card_le_two L J V e S hLJ hVJ hVN hinner,
    a3_ambient_action_card_eq_two L J V e S hLJ hVJ hVN hinner⟩

end CFSG.Quasithin.ChapterE.Section06.AlternatingLocal
