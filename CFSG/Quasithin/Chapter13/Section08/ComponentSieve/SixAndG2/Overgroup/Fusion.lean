module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.FullDenominators
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverSymplecticGeometry.Seed
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer

/-!
# Hyperplane fusion and endpoint escape in 13.8.27(3)

The symplectic natural A₆ action is transitive on hyperplanes: take perpendicular
lines and use the original L-action. Thus the source bound on C_G(V₃) transports
to every hyperplane of every conjugate of V. A conjugate of V centralizing V₃
has action image of order at most two, so its nontrivial action would have an
order-eight kernel. The transported bound makes V normalize that conjugate,
contradicting the intersecting-conjugate commutativity in 13.8.3.

The final application selects a moving seed V₃^(g_b h) from the endpoint span.
The H-adjustment is explicit, and the original critical pair and conjugator
remain unchanged. Full denominators and the genuine earlier 13.5.4(4)
centralizer bound imply Vγ is not contained in Q_H; no seed or fusion conclusion
is supplied as a premise. Source: Aschbacher–Smith, 13.5.4(4), 13.8.3,
and 13.8.27(3), printed pp.916,946,963 (PDF pp.933,963,980).
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)


include d

theorem hyperplane_conjugate (A : Subgroup G) (hA : A ≤ V) (hc : Nat.card A = 8) :
    ∃ l ∈ L, U.conjBy l = A := by
  let W := image d A
  have hW : Module.finrank (ZMod 2) W = 3 := image_dim d A hA 3 hc
  have hperp : Module.finrank (ZMod 2) (form.orthogonal W) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide), hW]
    rfl
  have hn : form.orthogonal W ≠ ⊥ := by
    intro he
    rw [he] at hperp
    have hz : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (natural (Fin 6))) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let x : V := d.coordinate.symm (Multiplicative.ofAdd w)
  have hx0 : (x : G) ≠ 1 := by
    intro he
    have he' : x = 1 := Subtype.ext he
    have := congrArg (fun a : V => (d.coordinate a).toAdd) he'
    exact hw0 (by simpa [x] using this)
  obtain ⟨z, hz, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : P)).mp d.line_card
  have hz0 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hPV := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  obtain ⟨l, hl, hlx⟩ := Section07.natural_nonzero_transitive d (hPV z.property)
    x.property hz0 hx0
  refine ⟨l, hl, eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    let yV : V := ⟨y, d.seed_le hy⟩
    let zV : V := ⟨z, hPV z.property⟩
    let lLT : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨l, mem_sup_left hl⟩
    let y' := V.normalizerMonoidHom ⟨l, d.normalizes_V lLT.property⟩ yV
    have hzpair : form (d.coordinate zV).toAdd (d.coordinate yV).toAdd = 0 := by
      have hyi : (d.coordinate yV).toAdd ∈ image d U := ⟨yV, hy, rfl⟩
      rw [seed_perpendicular d] at hyi
      exact hyi _ ⟨zV, z.property, rfl⟩
    have hzimage : naturalRepresentation (Fin 6) (permutation d lLT)
        (d.coordinate zV).toAdd = w := by
      rw [← conjugation d lLT zV]
      have he : V.normalizerMonoidHom ⟨l, d.normalizes_V lLT.property⟩ zV = x := by
        apply Subtype.ext
        exact hlx
      rw [he]
      simp [x]
    have horth : (d.coordinate y').toAdd ∈ form.orthogonal (form.orthogonal W) := by
      intro v hv
      have hwn : (⟨w, hw⟩ : form.orthogonal W) ≠ 0 := fun he => hw0 (congrArg Subtype.val he)
      obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : form.orthogonal W) hwn).mp hperp ⟨v,hv⟩
      have he : a • w = v := congrArg Subtype.val ha
      rw [← he, LinearMap.BilinForm.smul_left]
      have hi := form_invariant (permutation d lLT) (d.coordinate zV).toAdd (d.coordinate yV).toAdd
      rw [hzimage, hzpair] at hi
      change a * form w (d.coordinate y').toAdd = 0
      rw [show (d.coordinate y').toAdd = naturalRepresentation (Fin 6)
        (permutation d lLT) (d.coordinate yV).toAdd from conjugation d lLT yV, hi, mul_zero]
    rw [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at horth
    obtain ⟨v, hv, he⟩ := (mem_image d A _).mp horth
    have hev : v = y' := d.coordinate.injective he
    change y'.val ∈ A
    exact hev ▸ hv
  · change Nat.card A ≤ Nat.card (U.map _)
    rw [card_map_of_injective (MulAut.conj l).injective, d.seed_card, hc]

omit d [Finite G] in
private theorem centralizer_conj (A : Subgroup G) (g : G) :
    (centralizer (A : Set G)).conjBy g = centralizer (A.conjBy g : Set G) := by
  have he := map_inf_centralizer_of_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective ⊤ A
  rw [map_top_of_surjective _ (MulAut.conj g).surjective, top_inf_eq, top_inf_eq] at he
  exact he.symm

theorem centralizer_hyperplane (hcentral : centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G))
    (A : Subgroup G) (hA : A ≤ V) (hc : Nat.card A = 8) :
    centralizer (A : Set G) ≤ normalizer (V : Set G) := by
  obtain ⟨l, hl, he⟩ := hyperplane_conjugate d A hA hc
  have hh := map_mono (f := (MulAut.conj l).toMonoidHom) (hcentral.trans inf_le_right)
  rw [map_equiv_normalizer_eq] at hh
  have hv : V.conjBy l = V := mem_normalizer_iff_map_conj_eq.mp
    (d.normalizes_V (mem_sup_left hl))
  change (centralizer (U : Set G)).conjBy l ≤ normalizer (V.conjBy l : Set G) at hh
  rwa [centralizer_conj, he, hv] at hh

theorem centralizer_conjugate_hyperplane
    (hcentral : centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G))
    (g : G) (A : Subgroup G) (hA : A ≤ V.conjBy g) (hc : Nat.card A = 8) :
    centralizer (A : Set G) ≤ normalizer (V.conjBy g : Set G) := by
  have hA' : A.conjBy g⁻¹ ≤ V := by
    have hi := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hA
    change A.conjBy g⁻¹ ≤ (V.conjBy g).conjBy g⁻¹ at hi
    simpa only [conjBy_inv] using hi
  have hc' : Nat.card (A.conjBy g⁻¹) = 8 := by
    rw [conjBy, card_map_of_injective (MulAut.conj g⁻¹).injective, hc]
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
    (centralizer_hyperplane d hcentral _ hA' hc')
  rw [map_equiv_normalizer_eq] at hh
  change (centralizer (A.conjBy g⁻¹ : Set G)).conjBy g ≤ normalizer (V.conjBy g : Set G) at hh
  rwa [centralizer_conj, conjBy_inv'] at hh


open TransvectionQuotients.FiveSeed.BarMarking
open TransvectionQuotients.FiveSeed
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer

theorem seed_fixer_kernel_card (W : Subgroup G)
    (hW : W ≤ centralizer (U : Set G))
    (hcentral : centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hc : Nat.card W = 16) (hne : ⁅V, W⁆ ≠ ⊥) :
    Nat.card (W ⊓ centralizer (V : Set G) : Subgroup G) = 8 := by
  let := elementary d
  let B := M ⊓ normalizer (V : Set G)
  have hLB : L ≤ B := le_inf (by rw [d.local_normalizer]; exact L.le_normalizer)
    (le_sup_left.trans d.normalizes_V)
  have hBL : B ≤ normalizer (L : Set G) := by rw [← d.local_normalizer]; exact inf_le_left
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hα : Function.Surjective α :=
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f, _, hf, hk⟩ := natural_extension B L V hLB hBL inf_le_right α hα
    (linearCoordinate d) (fun l v => d.conjugation l v.toMul)
  have hWB : W ≤ B := hW.trans hcentral
  let fW := f.comp (inclusion hWB)
  have hker : fW.ker = (centralizer (V : Set G)).subgroupOf W := by
    ext w
    change f (inclusion hWB w) = 1 ↔ _
    change inclusion hWB w ∈ f.ker ↔ _
    rw [hk]
    rfl
  obtain ⟨t, ht, htf⟩ := exists_swap_bound_line (image d P)
    (image_dim d P (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
  have him : fW.range ≤ zpowers t := by
    rintro _ ⟨w, rfl⟩
    have hfix : ∀ y ∈ form.orthogonal (image d P),
        naturalRepresentation (Fin 6) (fW w) y = y := by
      intro y hy
      rw [← seed_perpendicular d] at hy
      obtain ⟨a, ha, rfl⟩ := (mem_image d U _).mp hy
      have he := hf (inclusion hWB w) (Additive.ofMul a)
      change (d.coordinate (V.normalizerMonoidHom ⟨w.val, (hWB w.property).2⟩ a)).toAdd =
        naturalRepresentation (Fin 6) (fW w) (d.coordinate a).toAdd at he
      rw [← he]
      apply congrArg (fun b : V => (d.coordinate b).toAdd)
      apply Subtype.ext
      change w.val * a.val * w.val⁻¹ = a.val
      rw [← mem_centralizer_iff.mp (hW w.property) a.val ha, mul_inv_cancel_right]
    rcases htf (fW w) hfix with he | he
    · exact he ▸ (zpowers t).one_mem
    · exact he ▸ mem_zpowers t
  have hrne : fW.range ≠ ⊥ := by
    intro he
    apply hne
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro w hw
    have hh : (⟨w,hw⟩ : W) ∈ fW.ker := by
      change fW ⟨w,hw⟩ = 1
      exact mem_bot.mp (he ▸ (show fW ⟨w,hw⟩ ∈ fW.range from ⟨⟨w,hw⟩,rfl⟩))
    rwa [hker] at hh
  have hr : Nat.card fW.range = 2 := by
    have hd : Nat.card fW.range ∣ 2 := by
      have hi := card_dvd_of_le him
      rwa [Nat.card_zpowers, ht.orderOf] at hi
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun h => hrne (card_eq_one.mp h))
  have hcount := fW.ker.card_mul_index
  rw [index_ker, hr, hc, hker] at hcount
  have he : Nat.card ((centralizer (V : Set G)).subgroupOf W) =
      Nat.card (W ⊓ centralizer (V : Set G) : Subgroup G) := by
    have hh : (centralizer (V : Set G)).subgroupOf W =
        (W ⊓ centralizer (V : Set G)).subgroupOf W := by
      ext w
      exact ⟨fun h => ⟨w.property,h⟩, fun h => h.2⟩
    rw [hh]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  omega

theorem conjugate_commutes_of_seed_centralization
    (hspan : IsMulCommutative (conjugateSpanBy V H))
    (hcentral : centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G))
    (g : G) (hg : V.conjBy g ≤ centralizer (U : Set G)) :
    ⁅V, V.conjBy g⁆ = ⊥ := by
  by_contra hne
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card,
      ZMod.card, finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hWcard : Nat.card (V.conjBy g) = 16 := by
    rw [conjBy, card_map_of_injective (MulAut.conj g).injective, hVcard]
  have hk := seed_fixer_kernel_card d (V.conjBy g) hg hcentral hWcard hne
  have hn := centralizer_conjugate_hyperplane d hcentral g
    (V.conjBy g ⊓ centralizer (V : Set G)) inf_le_left hk
  have hVN : V ≤ normalizer (V.conjBy g : Set G) := by
    apply le_trans _ hn
    exact le_centralizer_iff.mp inf_le_right
  have hWN : V.conjBy g ≤ normalizer (V : Set G) := hg.trans (hcentral.trans inf_le_right)
  have hc : ⁅V, V.conjBy g⁆ ≤ V ⊓ V.conjBy g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hWN)
      (le_normalizer_iff_commutator_le_right.mp hVN)
  have hi : V ⊓ V.conjBy g ≠ ⊥ := by
    intro he
    exact hne (le_bot_iff.mp (hc.trans he.le))
  exact hne (d.intersecting_conjugates_commute hspan g hi)

open CriticalGeometry TransvectionRecognition.Component.ModelExtension

omit d in
theorem full_denominators_escape
    (d : LocalSetup T L V P E U M H)
    {J : Subgroup G}
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V U P J).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) J V)
    (hDH : Source.DH (Source.UH J U) (c.Ugamma U) (c.Aone P) = Source.UH J U)
    (hDg : Source.Dgamma (c.Ugamma U) (Source.UH J U) P = c.Ugamma U)
    (hcentral : centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G)) :
    ¬ c.Vgamma ≤ Source.QH J := by
  intro hcore
  obtain ⟨hcent, hcomm⟩ := core_containment_seed_centralizer d hF9 c hDH hDg hcentral hcore
  have hn : ⁅(Source.UH J U).conjBy (c.gb : G), V⁆ ≠ ⊥ := by
    rw [commutator_comm]
    change ⁅V,c.Ugamma U⁆ ≠ ⊥
    rw [(full_denominators_commutator d hF9 c hDH hDg).2.1]
    intro he
    have hp := d.line_card
    rw [he,card_bot] at hp
    contradiction
  obtain ⟨h, hh, hmove⟩ :=
    AsymmetricPair.CoverGeometry.exists_noncommuting_conjugate J U V (c.gb : G) hn
  have hW : V.conjBy ((c.gb : G) * h) ≤ c.Vgamma := by
    rw [conjBy_mul]
    apply map_mono
    rintro _ ⟨v, hv, rfl⟩
    exact subset_closure ⟨h,hh,v,hv,rfl⟩
  have hc := conjugate_commutes_of_seed_centralization (localNaturalSetup d) d.abelian_span
    hcentral ((c.gb : G) * h) (hW.trans hcent)
  apply hmove
  apply le_bot_iff.mp
  rw [commutator_comm] at hc
  exact (commutator_mono (map_mono d.seed_le) le_rfl).trans hc.le

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
