module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.CubicBorelChoice
public import Theory.SpecificGroups.PSL2.SixteenCubicDetector

/-!
# Comparing the original cubic Borel action with the marked detector

Earlier 14.6.12 gives quotient order 72. The quotient Sylow therefore has
order eight, and its faithful residual action has the same kernel as the
literal quotient map. The cubic Borel residual is exactly the two-residual
of its join with the original Sylow.

For the Borel lifted from the marked normal square in Mc/O₂(Mc), a detector
kernel element moves its cubic residual only inside the original Sylow.
Intersecting with that residual identifies this displacement with its own
two-core. The resulting kernel inclusion forces detector image order eight.
All Borel, quotient and conjugation maps are the literal source maps.
CubicBorelCompletion applies this to the original normalizer and support.

Source: Aschbacher--Smith 14.6.14, final paragraph, printed p.1033.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The earlier quotient order gives order eight in the actual residual action. -/
theorem cubic_residual_action_card
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hprim : PrimitiveResidual H 3)
    (hc : Nat.card (H ⧸ pCore 2 H) = 72)
    (hn : (T : Subgroup G) ≤ normalizer (residual H : Set G)) :
    Nat.card ((quotientAut (pCore 2 (residual H))).comp
      ((residual H).normalizerMonoidHom.comp (inclusion hn))).range = 8 := by
  let α := (quotientAut (pCore 2 (residual H))).comp
    ((residual H).normalizerMonoidHom.comp (inclusion hn))
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hTH)
  have hk : α.ker = f.ker := residual_quotient_action_kernel H T hTH hprim hn
  let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange f))
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have he : f.range = (S : Subgroup (H ⧸ pCore 2 H)) := by
    change f.range = ((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    rw [MonoidHom.range_comp,inclusion_range]
  change Nat.card α.range = 8
  rw [Nat.card_congr er.toEquiv,he]
  rw [S.card_eq_multiplicity,hc]
  rw [show 72 = 2^3 * 9 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 9)]
  rfl

/-- Adjoining the original Sylow leaves the two-perfect cubic residual unchanged. -/
theorem cubic_borel_action_card
    (T : Sylow 2 G) (X : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) (hp : IsPPerfect 2 X)
    (hprim : PrimitiveResidual (X ⊔ (T : Subgroup G)) 3)
    (hc : Nat.card ((X ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) = 72) :
    Nat.card ((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hn))).range = 8 := by
  have hr : residual (X ⊔ (T : Subgroup G)) = X :=
    embedded_pResidual_join_pGroup X (T : Subgroup G) hp T.isPGroup' hn
  have hh : ∀ h : (T : Subgroup G) ≤ normalizer (residual (X ⊔ (T : Subgroup G)) : Set G),
      Nat.card ((quotientAut (pCore 2 (residual (X ⊔ (T : Subgroup G))))).comp
        ((residual (X ⊔ (T : Subgroup G))).normalizerMonoidHom.comp (inclusion h))).range = 8 :=
    fun h => cubic_residual_action_card T (X ⊔ (T : Subgroup G)) le_sup_right hprim hc h
  rw [hr] at hh
  exact hh hn
open WreathTwoElementaryRank AutomorphismSquare
local notation "F16" => GaloisField 2 4
local notation "L16" => Theory.PSL2.Group F16

omit [Finite G] in
private theorem cubic_sylow_intersection
    (T : Sylow 2 G) (X : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9) :
    (T : Subgroup G).subgroupOf X = pCore 2 X := by
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hnQ := hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    exact sup_eq_left.mp (T.is_maximal'
      (T.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 X) hnQ) le_sup_left)
  apply le_antisymm
  · let q := QuotientGroup.mk' (pCore 2 X)
    have hp : IsPGroup 3 (X ⧸ pCore 2 X) := IsPGroup.of_card (n := 2) hc
    have hd := IsPGroup.disjoint_of_coprime
      ((T.isPGroup'.comap_subtype (K := X)).map q) (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)
    have hz : ((T : Subgroup G).subgroupOf X).map q = ⊥ := by
      simpa only [disjoint_top,subgroupOf] using hd
    simpa only [q,QuotientGroup.ker_mk'] using
      (map_eq_bot_iff ((T : Subgroup G).subgroupOf X)).mp hz
  · intro x hx
    exact hQT (mem_map_of_mem X.subtype hx)

/-- The detector kernel fixes the original cubic residual modulo its own
 two-core. The Borel and both ambient quotient maps are the literal ones. -/
theorem cubic_borel_detector_kernel
    (T : Sylow 2 G) (Mc : Subgroup G) (hTMc : (T : Subgroup G) ≤ Mc)
    (N : Subgroup (Mc ⧸ pCore 2 Mc)) [N.Normal] (k : N ≃* L16 × L16)
    (ρ : (Mc ⧸ pCore 2 Mc) →* W (MulAut L16))
    (hact : ∀ g (x : N), (k.symm (wreathHom (ρ g) (k x)) : Mc ⧸ pCore 2 Mc) =
      g * x * g⁻¹)
    (B X : Subgroup G) (hB : B = squareBorelPreimage (T : Subgroup G) Mc N)
    (hBMc : B ≤ Mc) (hX : X = (primeToResidual 3 B).map B.subtype)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9) :
    ((Theory.PSL2.SixteenCubicWreath.cubicWreathAction F16).comp
      (ρ.comp ((QuotientGroup.mk' (pCore 2 Mc)).comp (inclusion hTMc)))).ker ≤
    ((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hn))).ker := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let S := (T.subtype hTMc).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let U := (P : Subgroup N).map N.subtype
  have hU : U = (S : Subgroup (Mc ⧸ pCore 2 Mc)) ⊓ N := by
    rw [show U = ((S : Subgroup (Mc ⧸ pCore 2 Mc)).subgroupOf N).map N.subtype by rw [←hP],
      subgroupOf_map_subtype]
  let D := normalizer (P : Set N)
  have hD : D.map N.subtype = N ⊓ normalizer (U : Set (Mc ⧸ pCore 2 Mc)) := by
    have hu : U.subgroupOf N = (P : Subgroup N) :=
      comap_map_eq_self_of_injective N.subtype_injective _
    rw [show D = normalizer (U.subgroupOf N : Set N) by rw [hu]; rfl,
      ←subgroupOf_normalizer_eq (map_subtype_le _),subgroupOf_map_subtype,inf_comm]
  have hB' : B = ((D.map N.subtype).comap q).map Mc.subtype := by
    rw [hD,hU,hB]
    rfl
  have hb (b : B) : q (inclusion hBMc b) ∈ D.map N.subtype := by
    have hh : inclusion hBMc b ∈ B.subgroupOf Mc := b.property
    have he : B.subgroupOf Mc = (D.map N.subtype).comap q := by
      rw [hB',subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective]
    rw [he] at hh
    exact hh
  let bN : B →* N := (q.comp (inclusion hBMc)).codRestrict N
    (fun b => (map_subtype_le D) (hb b))
  have hbD (b : B) : bN b ∈ D := by
    obtain ⟨z,hz,he⟩ := hb b
    have he' : z = bN b := Subtype.ext he
    exact he' ▸ hz
  let P' := P.mapSurjective (f := k.toMonoidHom) k.surjective
  have hDP : D.map k.toMonoidHom = normalizer (P' : Set (L16 × L16)) :=
    map_normalizer_eq_of_bijective _ k.bijective
  let f : B →* normalizer (P' : Set (L16 × L16)) :=
    (k.toMonoidHom.comp bN).codRestrict _ (fun b => by
      rw [←hDP]
      exact mem_map_of_mem k.toMonoidHom (hbD b))
  have hf (b : B) : (k.symm (f b : L16 × L16) : Mc ⧸ pCore 2 Mc) = q (inclusion hBMc b) := by
    change (k.symm (k (bN b)) : Mc ⧸ pCore 2 Mc) = _
    rw [k.symm_apply_apply]
    rfl
  have hXMc : X ≤ Mc := (hX ▸ map_subtype_le _).trans hBMc
  have hTP : (pCore 2 Mc) ≤ (T : Subgroup G).subgroupOf Mc :=
    pCore_isPGroup.le_sylow_of_normal (T.subtype hTMc)
  have hpre : (S : Subgroup (Mc ⧸ pCore 2 Mc)).comap q = (T : Subgroup G).subgroupOf Mc := by
    change (((T : Subgroup G).subgroupOf Mc).map q).comap q = _
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hTP]
  intro t ht
  let g := q (inclusion hTMc t)
  have hg : g ∈ (S : Subgroup (Mc ⧸ pCore 2 Mc)) :=
    mem_map_of_mem q (show inclusion hTMc t ∈ (T : Subgroup G).subgroupOf Mc from t.property)
  have hw : Theory.PSL2.SixteenCubicWreath.cubicWreathAction F16 (ρ g) = 1 := ht
  have hpres : (P' : Subgroup (L16 × L16)).map (wreathHom (ρ g)).toMonoidHom = P' := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨z,hz,rfl⟩
      obtain ⟨y,hy,rfl⟩ := hz
      let v := k.symm (wreathHom (ρ g) (k y))
      have hv : v ∈ (P : Subgroup N) := by
        rw [hP]
        change (v : Mc ⧸ pCore 2 Mc) ∈ (S : Subgroup (Mc ⧸ pCore 2 Mc))
        rw [hact]
        have hyS : (y : Mc ⧸ pCore 2 Mc) ∈ (S : Subgroup (Mc ⧸ pCore 2 Mc)) := by
          change y ∈ (S : Subgroup (Mc ⧸ pCore 2 Mc)).subgroupOf N
          rwa [←hP]
        exact mul_mem (mul_mem hg hyS) (inv_mem hg)
      exact ⟨v,hv,k.apply_symm_apply _⟩
    · rw [card_map_of_injective (wreathHom (ρ g)).injective]
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) v
  have hxB : x.val ∈ (primeToResidual 3 B).map B.subtype := hX ▸ x.property
  obtain ⟨b,hbR,hbx⟩ := hxB
  have hfx := map_primeToResidual_le_of_hom 3 f (mem_map_of_mem f hbR)
  have hd := Theory.PSL2.SixteenCubicWreath.cubic_kernel_displacement_square F16
    (GaloisField.card 2 4 (by decide)) P' (ρ g) hpres hw (f b) hfx
  have hdP : k.symm ((f b : L16 × L16)⁻¹ * wreathHom (ρ g) (f b)) ∈ (P : Subgroup N) := by
    obtain ⟨y,hy,he⟩ := hd
    rw [←he,MulEquiv.coe_toMonoidHom,k.symm_apply_apply]
    exact hy
  have hdS : (k.symm ((f b : L16 × L16)⁻¹ * wreathHom (ρ g) (f b)) : Mc ⧸ pCore 2 Mc) ∈
      (S : Subgroup (Mc ⧸ pCore 2 Mc)) := by
    rw [hP] at hdP
    exact hdP
  have heq : (k.symm ((f b : L16 × L16)⁻¹ * wreathHom (ρ g) (f b)) : Mc ⧸ pCore 2 Mc) =
      (q (inclusion hXMc x))⁻¹ * g * q (inclusion hXMc x) * g⁻¹ := by
    rw [map_mul,map_inv]
    have hbval : q (inclusion hBMc b) = q (inclusion hXMc x) :=
      congrArg q (Subtype.ext hbx)
    have ha := hact g (k.symm (f b))
    rw [k.apply_symm_apply,hf,hbval] at ha
    rw [coe_mul,coe_inv,hf,hbval,ha]
    group
  rw [heq] at hdS
  let y := x⁻¹ * X.normalizerMonoidHom (inclusion hn t) x
  have hyT : y.val ∈ (T : Subgroup G) := by
    have hh : inclusion hXMc y ∈ (S : Subgroup (Mc ⧸ pCore 2 Mc)).comap q := by
      change q (inclusion hXMc y) ∈ (S : Subgroup (Mc ⧸ pCore 2 Mc))
      have hval : inclusion hXMc y = (inclusion hXMc x)⁻¹ * inclusion hTMc t *
          inclusion hXMc x * (inclusion hTMc t)⁻¹ := by
        apply Subtype.ext
        change x.val⁻¹ * (t.val * x.val * t.val⁻¹) = x.val⁻¹ * t.val * x.val * t.val⁻¹
        group
      rw [hval]
      simpa only [g,map_inv,map_mul] using hdS
    rw [hpre] at hh
    exact hh
  have hyQ : y ∈ pCore 2 X := by
    rw [←cubic_sylow_intersection T X hn hc]
    exact hyT
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn t))
    (QuotientGroup.mk' (pCore 2 X) x) = QuotientGroup.mk' (pCore 2 X) x
  rw [quotientAut_apply_mk]
  exact (QuotientGroup.eq.mpr hyQ).symm

/-- The actual Sylow cubic action forces order eight in the marked detector.
The conclusion concerns the original ambient action, not an assumed outer image. -/
theorem cubic_borel_detector_card
    (T : Sylow 2 G) (Mc : Subgroup G) (hTMc : (T : Subgroup G) ≤ Mc)
    (N : Subgroup (Mc ⧸ pCore 2 Mc)) [N.Normal] (k : N ≃* L16 × L16)
    (ρ : (Mc ⧸ pCore 2 Mc) →* W (MulAut L16))
    (hact : ∀ g (x : N), (k.symm (wreathHom (ρ g) (k x)) : Mc ⧸ pCore 2 Mc) =
      g * x * g⁻¹)
    (B X : Subgroup G) (hB : B = squareBorelPreimage (T : Subgroup G) Mc N)
    (hBMc : B ≤ Mc) (hX : X = (primeToResidual 3 B).map B.subtype)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hc : Nat.card (X ⧸ pCore 2 X) = 9)
    (hprim : PrimitiveResidual (X ⊔ (T : Subgroup G)) 3)
    (h72 : Nat.card ((X ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) = 72) :
    Nat.card ((Theory.PSL2.SixteenCubicWreath.cubicWreathAction F16).comp ρ).range = 8 := by
  let a := (quotientAut (pCore 2 X)).comp
    (X.normalizerMonoidHom.comp (inclusion hn))
  let δ := (Theory.PSL2.SixteenCubicWreath.cubicWreathAction F16).comp ρ
  let f := δ.comp ((QuotientGroup.mk' (pCore 2 Mc)).comp (inclusion hTMc))
  have hk : f.ker ≤ a.ker := cubic_borel_detector_kernel T Mc hTMc N k ρ hact B X hB hBMc hX hn hc
  have ha : Nat.card a.range = 8 := cubic_borel_action_card T X hn hp hprim h72
  have hd : Nat.card a.range ∣ Nat.card f.range := by
    rw [←index_ker,←index_ker]
    exact index_dvd_of_le hk
  have hle : Nat.card f.range ≤ Nat.card δ.range :=
    card_le_of_le (by rintro _ ⟨t,rfl⟩; exact ⟨_,rfl⟩)
  have htarget := Theory.PSL2.SixteenCubicWreath.cubic_target_card F16 (GaloisField.card 2 4 (by decide))
  exact Nat.le_antisymm ((card_le_card_group δ.range).trans_eq htarget)
    (ha ▸ (Nat.le_of_dvd Nat.card_pos hd).trans hle)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
