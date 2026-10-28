module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.Construction

/-!
# Torus centralizers in the literal odd-normalizer quotient

Write A = M°, N = N_M(S), and K for the source torus. Centralizers of odd
subgroups lift through N → image(N → M/A) → N/S. The first kernel embeds
in the elementary subgroup A; the second embeds in the elementary image
of S in M/A. Coprime fixed-point lifting applies separately to these two
abelian kernels, without requiring S itself to be abelian.

For a nonidentity element of K, the ambient centralizer bound places its
centralizer in N ∩ D, which normalizes K. For the whole torus, the explicit
source identity C_{N∩D}(K) = KU gives self-centralization after quotienting
by S. The identity remains a premise for the source assembly to discharge.
The final pair supplies the two centralizer fields of the native ActionData.

Source: GLS4, Chapter 2, Lemma 14.9 and (14G),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2600–2620.
-/

noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise

/-- Fixed points lift through an abelian kernel of coprime order. -/
private theorem centralizer_map_abelian {H Q : Type*} [Group H] [Finite H] [Group Q]
    (f : H →* Q) (hf : Function.Surjective f) [IsMulCommutative f.ker]
    (D : Subgroup H) (hcop : Nat.Coprime (Nat.card D) (Nat.card f.ker)) :
    (centralizer (D : Set H)).map f = centralizer (D.map f : Set Q) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ f) ?_
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have hx := mem_centralizer_sup_of_coprime_fixed_coset (⊤ : Subgroup H) f.ker D
    le_top (by rw [(⊤ : Subgroup H).normalizer_eq_top]; exact le_top)
    (by rw [f.ker.normalizer_eq_top]; exact le_top) hcop x (mem_top _) (by
      intro d hd
      rw [MonoidHom.mem_ker]
      change f (d * x * d⁻¹ / x) = 1
      simp only [map_div, map_mul, map_inv]
      rw [(hy (f d) (mem_map_of_mem f hd)), mul_inv_cancel_right, div_self'])
  have hm := mem_map_of_mem f hx
  simpa only [Subgroup.map_sup, top_inf_eq,
    (Subgroup.map_eq_bot_iff f.ker).mpr le_rfl, sup_bot_eq] using hm

/-- Factor the literal quotient map through a surjection with two abelian
kernel layers, and apply fixed-point lifting at each layer. -/
private theorem centralizer_map_two_layers
    {H B Q : Type*} [Group H] [Finite H] [Group B] [Finite B] [Group Q]
    (f : H →* B) (hf : Function.Surjective f)
    (q : H →* Q) (hq : Function.Surjective q) (hk : f.ker ≤ q.ker)
    [IsMulCommutative f.ker] [IsMulCommutative (q.ker.map f)]
    (D : Subgroup H) (hcop : Nat.Coprime (Nat.card D) (Nat.card q.ker)) :
    (centralizer (D : Set H)).map q = centralizer (D.map q : Set Q) := by
  let r : B →* Q := f.liftOfSurjective hf ⟨q, hk⟩
  have hr (x : H) : r (f x) = q x :=
    f.liftOfRightInverse_comp_apply _ _ _ x
  have hrcomp : r.comp f = q := MonoidHom.ext hr
  have hrsurj : Function.Surjective r := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨f x, hr x⟩
  have hrker : r.ker = q.ker.map f := by
    ext b
    obtain ⟨x, rfl⟩ := hf b
    constructor
    · intro hx
      exact ⟨x, MonoidHom.mem_ker.mpr (hr x ▸ hx), rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [MonoidHom.mem_ker, ← hyx, hr]
      exact hy
  let : IsMulCommutative r.ker := hrker.symm ▸ inferInstance
  have hc1 : Nat.Coprime (Nat.card D) (Nat.card f.ker) :=
    hcop.of_dvd_right (card_dvd_of_le hk)
  have hc2 : Nat.Coprime (Nat.card (D.map f)) (Nat.card r.ker) := by
    rw [hrker]
    exact (hcop.of_dvd_left (card_dvd_of_surjective _ (f.subgroupMap_surjective D))).of_dvd_right
      (card_dvd_of_surjective _ (f.subgroupMap_surjective q.ker))
  rw [← hrcomp, ← map_map, centralizer_map_abelian f hf D hc1,
    centralizer_map_abelian r hrsurj (D.map f) hc2, map_map]

namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Here the two layers are the actual restrictions of M° and S/M°.
Their orders divide the two-power order of S. -/
private theorem odd_centralizer_map (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (he : ElementaryQuotient d g)
    (D : Subgroup (normalizerInM g)) (hD : Odd (Nat.card D)) :
    (centralizer (D : Set (normalizerInM g))).map (projection g) =
      centralizer (D.map (projection g) : Set (quotient g)) := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  let : IsElementaryAbelian 2 (sylowImage d g) := he
  let f₀ := (pointProjection d).comp (normalizerInM g).subtype
  let f := f₀.rangeRestrict
  let q := projection g
  have hfker : f.ker = (A.subgroupOf M).subgroupOf (normalizerInM g) := by
    ext n
    rw [MonoidHom.ker_rangeRestrict]
    change pointProjection d (n : M) = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hqker : q.ker = (g.S.subgroupOf M).subgroupOf (normalizerInM g) :=
    QuotientGroup.ker_mk' _
  have hk : f.ker ≤ q.ker := by
    rw [hfker, hqker]
    exact subgroupOf_mono _ (subgroupOf_mono M g.closure_le_S)
  let : IsMulCommutative f.ker := IsMulCommutative.of_comm fun a b => by
    have ha : (((a : normalizerInM g) : M) : G) ∈ A := hfker.le a.property
    have hb : (((b : normalizerInM g) : M) : G) ∈ A := hfker.le b.property
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : A => (x : G)) (mul_comm (⟨_, ha⟩ : A) ⟨_, hb⟩)
  have hmap : ∀ b ∈ q.ker.map f, (b : pointQuotient d) ∈ sylowImage d g := by
    rintro b ⟨n, hn, rfl⟩
    have hnS : (n : M) ∈ g.S.subgroupOf M := by
      rw [hqker] at hn
      exact hn
    exact mem_map_of_mem (pointProjection d) hnS
  let : IsMulCommutative (q.ker.map f) := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : sylowImage d g => (v : pointQuotient d)) (mul_comm
      (⟨_, hmap a a.property⟩ : sylowImage d g) ⟨_, hmap b b.property⟩)
  have htwo : IsPGroup 2 q.ker := by
    rw [hqker]
    obtain ⟨V, hV⟩ := s.S_sylow
    have hS : IsPGroup 2 g.S := hV ▸ V.isPGroup'
    exact hS.comap_subtype.comap_subtype
  obtain ⟨i, hi⟩ := htwo.exists_card_eq
  apply centralizer_map_two_layers f f₀.rangeRestrict_surjective q
    (QuotientGroup.mk'_surjective _) hk D
  rw [hi]
  exact hD.coprime_two_right.pow_right i

private theorem torus_odd (d : Context Z M z t m) :
    Odd (Nat.card (residualCommutator M t)) := by
  rw [d.torus_card]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Even.pow_of_ne_zero even_two (by omega : 2 * m + 1 ≠ 0)) odd_one

private theorem torus_le_pointStabilizer (d : Context Z M z t m) : residualCommutator M t ≤ M := by
  rw [d.torus_eq_local_pair]
  exact inf_le_left.trans inf_le_left

private theorem torus_le_normalizerInM (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) : (residualCommutator M t).subgroupOf M ≤ normalizerInM g := by
  intro k hk
  exact le_normalizer_comap M.subtype (d.torus_le_normalizer_S g s hk)

private theorem ambient_normalizer (g : LocalGeometry Z M z t m) (n : normalizerInM g) :
    ((n : M) : G) ∈ normalizer (g.S : Set G) := by
  have h := le_normalizer_map M.subtype (mem_map_of_mem M.subtype n.property)
  rwa [map_subgroupOf_eq_of_le g.S_le_M] at h

/-- Nonidentity torus elements have centralizers normalizing the literal torus image. -/
public theorem torusImage_element_centralizers (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (s : SylowGeometry g) (he : ElementaryQuotient d g) :
    ∀ x ∈ torusImage g, x ≠ 1 →
      centralizer ({x} : Set (quotient g)) ≤ normalizer (torusImage g : Set (quotient g)) := by
  rintro x ⟨k, hk, rfl⟩ hx1
  have hk1 : (((k : normalizerInM g) : M) : G) ≠ 1 := by
    intro hh
    apply hx1
    have h : k = 1 := Subtype.ext (Subtype.ext hh)
    rw [h, map_one]
  have hodd : Odd (Nat.card (zpowers k)) := by
    rw [Nat.card_zpowers]
    apply Odd.of_dvd_nat (torus_odd d)
    rw [← orderOf_submonoid k, ← orderOf_submonoid (k : M)]
    exact (residualCommutator M t).orderOf_dvd_natCard hk
  have hmap := odd_centralizer_map d g s he (zpowers k) hodd
  rw [MonoidHom.map_zpowers] at hmap
  simp only [zpowers_eq_closure, centralizer_closure] at hmap
  rw [← hmap]
  apply (map_mono ?_).trans (le_normalizer_map (projection g))
  intro n hn
  have hnD := d.torus_centralizer_le_pair hsemi hk hk1
    ⟨(n : M).property, mem_centralizer_singleton_iff.mpr
      (congrArg (fun a : normalizerInM g => ((a : M) : G))
        (mem_centralizer_singleton_iff.mp hn))⟩
  exact le_normalizer_comap (normalizerInM g).subtype
    (le_normalizer_comap M.subtype (d.pair_normalizes_torus hnD))

/-- The literal torus image is self-centralizing, conditional on the independent
ambient source identity C_{N∩D}(K)=KU. -/
public theorem torusImage_centralizer (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (s : SylowGeometry g) (he : ElementaryQuotient d g)
    (hambient : (normalizer (g.S : Set G) ⊓ residualPairStabilizer M t) ⊓
      centralizer (residualCommutator M t : Set G) = residualCommutator M t ⊔ g.U) :
    centralizer (torusImage g : Set (quotient g)) = torusImage g := by
  let K := ((residualCommutator M t).subgroupOf M).subgroupOf (normalizerInM g)
  let e : K ≃* residualCommutator M t :=
    (subgroupOfEquivOfLe (torus_le_normalizerInM d g s)).trans
      (subgroupOfEquivOfLe (torus_le_pointStabilizer d))
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_congr e.toEquiv]
    exact torus_odd d
  change centralizer (K.map (projection g) : Set (quotient g)) = _
  rw [← odd_centralizer_map d g s he K hodd]
  apply le_antisymm ?_ ?_
  · rintro y ⟨n, hn, rfl⟩
    have hnK : (((n : normalizerInM g) : M) : G) ∈
        centralizer (residualCommutator M t : Set G) := by
      intro k hk
      let kN : normalizerInM g := ⟨⟨k, torus_le_pointStabilizer d hk⟩, torus_le_normalizerInM d g s hk⟩
      exact congrArg (fun a : normalizerInM g => ((a : M) : G)) (hn kN hk)
    have hne : residualCommutator M t ≠ ⊥ := by
      apply (one_lt_card_iff_ne_bot _).mp
      rw [d.torus_card]
      have hm := d.parameter_pos
      have hp : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨k, hk, hk1⟩ := (residualCommutator M t).bot_or_exists_ne_one.resolve_left hne
    have hnD := d.torus_centralizer_le_pair hsemi hk hk1
      ⟨(n : M).property, mem_centralizer_singleton_iff.mpr (hnK k hk).symm⟩
    have hnKU := hambient ▸ (show (((n : normalizerInM g) : M) : G) ∈
      (normalizer (g.S : Set G) ⊓ residualPairStabilizer M t) ⊓
        centralizer (residualCommutator M t : Set G) from
      ⟨⟨ambient_normalizer g n, hnD⟩, hnK⟩)
    have hUK : g.U ≤ normalizer (residualCommutator M t : Set G) :=
      (g.U_le_centralizer.trans (centralizer_le (show residualCommutator M t ≤
        residualGenerated M z t from le_sup_right))).trans (Subgroup.centralizer_le_normalizer _)
    have hnprod : (((n : normalizerInM g) : M) : G) ∈
        (residualCommutator M t : Set G) * (g.U : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hUK]
      exact hnKU
    obtain ⟨a, ha, u, hu, hau⟩ := hnprod
    let aN : normalizerInM g := ⟨⟨a, torus_le_pointStabilizer d ha⟩, torus_le_normalizerInM d g s ha⟩
    let uN : normalizerInM g := ⟨⟨u, g.S_le_M (g.U_le_S hu)⟩,
      (g.S.subgroupOf M).le_normalizer (g.U_le_S hu)⟩
    have hnu : n = aN * uN := Subtype.ext (Subtype.ext hau.symm)
    have huq : projection g uN = 1 := (QuotientGroup.eq_one_iff _).mpr (g.U_le_S hu)
    refine ⟨aN, ha, ?_⟩
    rw [hnu, map_mul, huq, mul_one]
  · apply map_mono
    let : IsCyclic (residualCommutator M t) := d.torus_cyclic
    intro a ha b hb
    exact Subtype.ext (Subtype.ext (congrArg (fun v : residualCommutator M t => (v : G))
      (mul_comm (⟨_, hb⟩ : residualCommutator M t) ⟨_, ha⟩)))

/-- Both centralizer clauses required by `actionData_of_torus_centralizers`.
Only the independently produced ambient source identity remains explicit. -/
public theorem torusImage_centralizer_clauses (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (s : SylowGeometry g) (he : ElementaryQuotient d g)
    (hambient : (normalizer (g.S : Set G) ⊓ residualPairStabilizer M t) ⊓
      centralizer (residualCommutator M t : Set G) = residualCommutator M t ⊔ g.U) :
    (∀ x ∈ torusImage g, x ≠ 1 →
      centralizer ({x} : Set (quotient g)) ≤
        normalizer (torusImage g : Set (quotient g))) ∧
      centralizer (torusImage g : Set (quotient g)) = torusImage g :=
  ⟨torusImage_element_centralizers d g hsemi s he,
    torusImage_centralizer d g hsemi s he hambient⟩

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
