module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Binary.Natural
public import Theory.Representation.PSL3Two.DoubledNaturalPlane
public import Theory.GroupAction.FourPointResidual

/-!
# The doubled-natural plane span in original 14.6.10(5)

A Sylow two-subgroup fixes a nonidentity element of the original four-group.
Its two coordinates are fixed by the quotient Sylow. The natural fixed-space
bound puts that pair in a summand or in the diagonal. Each of these three
copies is invariant under the full matrix group and has order eight.

The two-perfect moving subgroup is transitive on the three nonidentity plane
elements, so the whole plane lies in the same copy. Its component span has
order at most eight. Perfectness excludes order four, giving the exact order.
The coordinates below retain the literal section quotient and conjugation
conventions of `HasSectionModel`; no plane classification is assumed.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
The source-branch assembly remains in the parent Binary development.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Binary
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open BinaryLinearThree BinaryLinearThree.DoubledNaturalPlane
variable {G : Type*} [Group G] [Finite G]

private theorem PlaneConfiguration.orbit {C V : Subgroup G}
    (h : PlaneConfiguration C V) {A : Subgroup G}
    (hp : IsPPerfect 2 A) (hAV : A ≤ normalizer (V : Set G)) (hm : ⁅V,A⁆ = V)
    (x : V) (hx : x ≠ 1) :
    ∀ y : V, y ≠ 1 → ∃ a : A, (V.normalizerMonoidHom (inclusion hAV a)) x = y := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V C) := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V C)
  let f := V.normalizerMonoidHom.comp (inclusion hAV)
  have hmove : ∃ a : A, f a x ≠ x := by
    by_contra! hn
    have hf := MulAction.four_action_eq_one_of_twoPerfect_fixed hp h.card f x hx hn
    have hcent : A ≤ centralizer (V : Set G) := by
      intro a ha v hv
      have he := congrArg (fun k : A →* MulAut V => (k ⟨a,ha⟩ ⟨v,hv⟩ : G)) hf
      change a * v * a⁻¹ = v at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hb : V = ⊥ := by
      rw [← hm,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hh := h.card
    rw [hb,card_bot] at hh
    omega
  exact MulAction.four_orbit_of_twoPerfect hp h.card f x hx hmove

/-- A moving Sylow-invariant plane in a doubled natural envelope spans eight elements. -/
theorem PlaneConfiguration.span_card_of_doubled_natural
    {C V E : Subgroup G} (h : PlaneConfiguration C V)
    (hUE : conjugateSpanBy V C ≤ E)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel C E ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural 3))) :
    Nat.card (conjugateSpanBy V C) = 8 := by
  classical
  obtain ⟨_,hCE,_,hn,f₀,hf₀⟩ := hm
  let f : E ≃* Multiplicative (Vector × Vector) :=
    ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf (G := G) E)).trans
      QuotientGroup.quotientBot).symm.trans f₀
  have hf (c : C) (x y : E) (he : (y : G) = c * (x : G) * (c : G)⁻¹) :
      (f y).toAdd = (W.prod W) (linearThreeActor e c) (f x).toAdd := by
    exact hf₀ c x y he
  have hVE : V ≤ E := (le_conjugateSpanBy V C).trans hUE
  let vE : V →* E := inclusion hVE
  have hfv (c : C) (x y : V) (he : (y : G) = c * (x : G) * (c : G)⁻¹) :
      (f (vE y)).toAdd = (W.prod W) (linearThreeActor e c) (f (vE x)).toAdd :=
    hf c (vE x) (vE y) he
  obtain ⟨P,hP⟩ := h.sylow
  let pN : P →* normalizer (V : Set G) :=
    (C.subtype.comp (P : Subgroup C).subtype).codRestrict _
      (fun p => hP ⟨p.val,p.property,rfl⟩)
  let fp : P →* MulAut V := V.normalizerMonoidHom.comp pN
  let := MulAction.compHom V fp
  obtain ⟨x,hx,hxne⟩ := P.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point V
    (by rw [h.card]; decide) (a := 1) (fun p => map_one (fp p))
  have hx1 : x ≠ 1 := Ne.symm hxne
  have hs : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pbar : Sylow 2 Group := P.mapSurjective hs
  have hfix : ∀ p : Pbar, (W.prod W) p (f (vE x)).toAdd = (f (vE x)).toAdd := by
    intro p
    have hp : (p : Group) ∈ (P : Subgroup C).map (linearThreeActor e) := p.property
    obtain ⟨c,hc,he⟩ := hp
    have hpx : fp ⟨c,hc⟩ x = x := hx ⟨c,hc⟩
    have hh := hfv c x (fp ⟨c,hc⟩ x) rfl
    rw [hpx,he] at hh
    exact hh.symm
  obtain ⟨i,hi⟩ := fixed_pair_mem_copy Pbar (f (vE x)).toAdd hfix
  let D : Subgroup E := ((copyMap i).range).comap f.toMonoidHom
  let N : Subgroup G := D.map E.subtype
  have hN (y : E) : (y : G) ∈ N ↔ f y ∈ (copyMap i).range := by
    exact mem_map_iff_mem E.subtype_injective
  have hNC : C ≤ normalizer (N : Set G) := by
    have hstable (c : C) (y : G) (hy : y ∈ N) : c * y * (c : G)⁻¹ ∈ N := by
      obtain ⟨z,hz,rfl⟩ := hy
      have hzE := (mem_normalizer_iff.mp (hCE c.property) z).mp z.property
      apply (hN ⟨_,hzE⟩).mpr
      have hh := copy_stable i (linearThreeActor e c) (f z) hz
      have he := hf c z ⟨_,hzE⟩ rfl
      rwa [← he] at hh
    intro c hc
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · exact hstable ⟨c,hc⟩ y
    · intro hy
      simpa only [inv_mul_cancel_left,mul_inv_cancel_right,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using
        hstable ⟨c⁻¹,C.inv_mem hc⟩ _ hy
  have hVN : V ≤ N := by
    obtain ⟨A,hAC,hAp,hAV,hmA⟩ := h.moved
    intro y hy
    by_cases hy1 : y = 1
    · simpa only [hy1] using N.one_mem
    obtain ⟨a,ha⟩ := h.orbit hAp hAV hmA x hx1 ⟨y,hy⟩
      (fun he => hy1 (congrArg Subtype.val he))
    apply (hN (vE ⟨y,hy⟩)).mpr
    have hh := copy_stable i (linearThreeActor e ⟨a,hAC a.property⟩) (f (vE x)) hi
    have he := hfv ⟨a,hAC a.property⟩ x
      (V.normalizerMonoidHom (inclusion hAV a) x) rfl
    rw [ha] at he
    rwa [← he] at hh
  have hcardN : Nat.card N = 8 := by
    rw [show N = D.map E.subtype from rfl,card_map_of_injective E.subtype_injective]
    change Nat.card ((copyMap i).range.comap f.toMonoidHom) = 8
    rw [comap_equiv_eq_map_symm',card_map_of_injective f.symm.injective]
    exact card_copy i
  have hUN := conjugateSpanBy_le hVN hNC
  let U := conjugateSpanBy V C
  let := h.perfect
  have hd : Nat.card U ∣ 8 := hcardN ▸ card_dvd_of_le hUN
  have hlo : 4 ≤ Nat.card U := h.card ▸ card_le_of_le (le_conjugateSpanBy V C)
  have hhi : Nat.card U ≤ 8 := Nat.le_of_dvd (by decide) hd
  have hne : Nat.card U ≠ 4 := by
    intro hc
    have hz : ⁅U,C⁆ ≤ ⊥ := commutator_le_of_perfect_normalized_small_index C U ⊥
      (le_normalizer_conjugateSpanBy V C) (by rw [normalizer_eq_top]; exact le_top)
      (by simpa using hc.le)
    rw [h.span_moved] at hz
    have hv : V = ⊥ := bot_unique ((le_conjugateSpanBy V C).trans hz)
    have hh := h.card
    rw [hv,card_bot] at hh
    omega
  interval_cases hc : Nat.card U <;> norm_num at *
end CFSG.Quasithin.Chapter14.Section06.Binary
