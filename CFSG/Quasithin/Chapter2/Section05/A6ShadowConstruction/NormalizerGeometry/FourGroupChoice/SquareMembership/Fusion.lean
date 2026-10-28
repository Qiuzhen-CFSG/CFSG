module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.SquareMembership
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.ActionNormalizer

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.Reflection
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Crossing-square membership from involution nonfusion

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.557, 567, and 569–570: Lemmas 2.5.11(2), 2.5.22(2), and the terminal
construction after 2.5.27.

Let `b = eˣ` centralize `N_K(E)`. Transitivity of `N_K(E)` on the three
nonidentity elements of `E` shows that `eb` is conjugate to `z = t zK`.
If `e^(x²)` lies outside `E`, the A₆ coboundary identity makes `b e^(x²)`
conjugate to `b`, hence to `t`. These two products are conjugate by `x`.
Thus nonfusion of `t` and `z` forces `x²` to stabilize `E`.

The nonfusion is recovered from `C_G(t) ≤ H`: the crossing two-group has
order 256 and centralizes `z`, whereas a Sylow two-subgroup of `H` has
order 128. A conjugacy between `t` and `z` would contradict these orders.
The complete source wrapper constructs the four-group and uses the already
proved reflection replacement to obtain `x² ∈ S_K S_Kˣ`.

`ModelFacts` contains only identities in the actual A₆ and `MulAut A₆`.
Its coboundary equation lifts an actual conjugator using action compatibility;
no ambient image-fusion assertion is substituted for that equation.

The full-centralizer premise is present in the source but absent from `Setup`.
It remains explicit here, so this is a corrected source route, not a proof of
the original `Setup`-only statement. Neither `Setup` nor the shared assembly
modules are changed. The parent must supply that source input and discharge
the concrete model identities before claiming the terminal source theorem.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction.SquareMembership.Fusion
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem square_normalizes_of_reflection_mem (d : Setup G)
    (E : Subgroup G) [IsKleinFour E] (hz : d.zK ∈ E)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hf : (d.x ^ 2)⁻¹ * e * d.x ^ 2 ∈ E) :
    d.x ^ 2 ∈ normalizer (E : Set G) := by
  have hzC : d.zK ∈ (center d.S).map d.S.subtype := by
    rw [d.center_s]
    exact mem_sup_right (mem_zpowers _)
  obtain ⟨a, ha, haeq⟩ := hzC
  change (a : G) = d.zK at haeq
  have hcomm : d.x ^ 2 * d.zK = d.zK * d.x ^ 2 := by
    simpa only [coe_mul, Subtype.coe_mk, haeq] using congrArg Subtype.val
      (mem_center_iff.mp ha (⟨d.x ^ 2, d.square_mem⟩ : d.S))
  have hzfix : (MulAut.conj (d.x ^ 2)⁻¹) d.zK = d.zK := by
    simp only [MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hcomm]
    group
  have hle : conjugate (d.x ^ 2) E ≤ E := by
    unfold conjugate
    nth_rw 1 [NormalizerCalculation.four_generators d E hz he heout]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · simpa only [MulEquiv.coe_toMonoidHom, hzfix] using hz
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hf
  have heq : conjugate (d.x ^ 2) E = E :=
    eq_of_le_of_card_ge hle (by
      have hcard := Nat.card_congr ((MulAut.conj (d.x ^ 2)⁻¹).subgroupMap E).toEquiv
      exact hcard.le)
  have hn : (d.x ^ 2)⁻¹ ∈ normalizer (E : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr heq
  simpa only [inv_inv] using (normalizer (E : Set G)).inv_mem hn

/-- The fusion calculation behind the omitted square-stability step. The two
witness premises will be supplied by identities in the actual A₆ model. -/
private theorem square_normalizes_of_fusion_witnesses (d : Setup G)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) (hz : d.zK ∈ E)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G))
    (hsep : ¬ IsConj d.t d.z)
    (htrans : ∃ k ∈ d.K ⊓ normalizer (E : Set G), k * e * k⁻¹ = d.zK)
    (houtside : ∀ f ∈ d.sk, f ^ 2 = 1 → f ∉ E →
      ∃ k ∈ d.K, k * (d.x⁻¹ * e * d.x) * k⁻¹ = f * (d.x⁻¹ * e * d.x)) :
    d.x ^ 2 ∈ normalizer (E : Set G) := by
  let b := d.x⁻¹ * e * d.x
  let f := (d.x ^ 2)⁻¹ * e * d.x ^ 2
  by_cases hfE : f ∈ E
  · exact square_normalizes_of_reflection_mem d E hz he heout hfE
  have he2 : e ^ 2 = 1 := by
    simpa only [pow_two, coe_mul, coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
  have hf2 : f ^ 2 = 1 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      (show ((MulAut.conj (d.x ^ 2)⁻¹) e) ^ 2 = 1 from by rw [← map_pow, he2, map_one])
  have hKN := (normal_subgroupOf_iff_le_normalizer (CoreReduction.k_le_h d)).mp d.normalK
  have hsqN : d.x ^ 2 ∈ normalizer (d.sk : Set G) :=
    inf_normalizer_le_normalizer_inf
      ⟨d.S.le_normalizer d.square_mem, hKN (CoreReduction.s_le_h d d.square_mem)⟩
  have hfD : f ∈ d.sk := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      ((normalizer (d.sk : Set G)).inv_mem hsqN) e).mp (hE he)
  obtain ⟨k, hk, hke⟩ := htrans
  have hbt : IsConj b d.t := by
    have ht := (MulAut.conj d.x⁻¹).toMonoidHom.map_isConj
      (isConj_iff.mpr ⟨k, hke⟩)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, d.zK_conjugate] using ht
  have hkb : k * b * k⁻¹ = b := by
    have hh : k * b = b * k := hc k hk
    rw [hh]
    group
  have hkt : k * d.t * k⁻¹ = d.t := by
    rw [d.t_mem.2 k hk.1]
    group
  have heb : IsConj (e * b) (d.zK * b) := isConj_iff.mpr ⟨k, by
    calc
      k * (e * b) * k⁻¹ = (k * e * k⁻¹) * (k * b * k⁻¹) := by group
      _ = d.zK * b := by rw [hke, hkb]⟩
  have hte : IsConj (d.t * e) d.z := isConj_iff.mpr ⟨k, by
    calc
      k * (d.t * e) * k⁻¹ = (k * d.t * k⁻¹) * (k * e * k⁻¹) := by group
      _ = d.t * d.zK := by rw [hkt, hke]
      _ = d.z := d.z_eq.symm⟩
  have hteX : IsConj (d.t * e) (d.zK * b) := isConj_iff.mpr ⟨d.x⁻¹, by
    calc
      d.x⁻¹ * (d.t * e) * (d.x⁻¹)⁻¹ = (d.x⁻¹ * d.t * d.x) * b := by dsimp [b]; group
      _ = d.zK * b := by rw [d.t_conjugate]⟩
  have hebz := heb.trans (hteX.symm.trans hte)
  have hbX : d.x⁻¹ * b * d.x = f := by dsimp [b, f]; simp only [pow_two]; group
  have hbF : b * f = f * b :=
    d.sk_centralizes_conjugate hfD b (show b ∈ conjugate d.x d.sk from
      ⟨e, hE he, by simp [b]⟩)
  have hebX : IsConj (e * b) (f * b) := isConj_iff.mpr ⟨d.x⁻¹, by
    calc
      d.x⁻¹ * (e * b) * (d.x⁻¹)⁻¹ = b * (d.x⁻¹ * b * d.x) := by dsimp [b]; group
      _ = b * f := by rw [hbX]
      _ = f * b := hbF⟩
  obtain ⟨l, _, hl⟩ := houtside f hfD hf2 hfE
  have hbf : IsConj b (f * b) := isConj_iff.mpr ⟨l, hl⟩
  exact (hsep (hbt.symm.trans (hbf.trans (hebX.symm.trans hebz)))).elim


/-- The two finite calculations used in the fusion argument. They concern the
actual alternating group and its automorphisms. The second is a coboundary
identity, so its transport gives an actual conjugator, not just image fusion. -/
public structure ModelFacts : Prop where
  four_transitive : ∀ F : Subgroup (alternatingGroup (Fin 6)), IsKleinFour F →
    ∀ a ∈ F, a ≠ 1 → ∀ b ∈ F, b ≠ 1 →
      ∃ k ∈ normalizer (F : Set (alternatingGroup (Fin 6))), k * a * k⁻¹ = b
  outside_coboundary : ∀ D F : Subgroup (alternatingGroup (Fin 6)),
    Nonempty (D ≃* DihedralGroup 4) → IsKleinFour F → F ≤ D →
    ∀ β : MulAut (alternatingGroup (Fin 6)), β ^ 2 = 1 → β ≠ 1 →
      (∀ k ∈ normalizer (F : Set (alternatingGroup (Fin 6))), β k = k) →
      ∀ f ∈ D, f ^ 2 = 1 → f ∉ F →
        ∃ k : alternatingGroup (Fin 6), k * (β k)⁻¹ = f

private def modelSubgroup (d : Setup G) (E : Subgroup G) : Subgroup (alternatingGroup (Fin 6)) :=
  (E.subgroupOf d.K).map d.modelK.toMonoidHom

omit [Finite G] in
private theorem modelSubgroup_mem (d : Setup G) (E : Subgroup G) (q : alternatingGroup (Fin 6)) :
    q ∈ modelSubgroup d E ↔ (d.modelK.symm q : G) ∈ E := by
  change q ∈ (E.subgroupOf d.K).map d.modelK.toMonoidHom ↔ _
  rw [mem_map_equiv]
  rfl

private noncomputable def modelEquiv (d : Setup G) (E : Subgroup G) (hE : E ≤ d.K) :
    E ≃* modelSubgroup d E :=
  (subgroupOfEquivOfLe hE).symm.trans (d.modelK.subgroupMap (E.subgroupOf d.K))

omit [Finite G] in
private theorem model_normalizer_mem (d : Setup G) (E : Subgroup G) (hE : E ≤ d.K)
    (q : alternatingGroup (Fin 6)) :
    q ∈ normalizer (modelSubgroup d E : Set (alternatingGroup (Fin 6))) ↔
      (d.modelK.symm q : G) ∈ normalizer (E : Set G) := by
  have heq : ((normalizer (E : Set G)).subgroupOf d.K).map d.modelK.toMonoidHom =
      normalizer (modelSubgroup d E : Set (alternatingGroup (Fin 6))) := by
    rw [subgroupOf_normalizer_eq hE, map_equiv_normalizer_eq]
    rfl
  rw [← heq, mem_map_equiv]
  rfl

/-- Nonfusion of the two distinguished involutions forces square stability.
The nonfusion is source 2.5.11(2); it is absent from `Setup`. Both remaining
model hypotheses are explicit identities on the actual A₆ carrier. -/
public theorem square_normalizes_of_model (d : Setup G) (m : ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) (hz : d.zK ∈ E)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G))
    (hsep : ¬ IsConj d.t d.z) : d.x ^ 2 ∈ normalizer (E : Set G) := by
  let F := modelSubgroup d E
  let D := modelSubgroup d d.sk
  have hEK : E ≤ d.K := hE.trans inf_le_right
  have hF : IsKleinFour F := by
    let j := modelEquiv d E hEK
    exact ⟨(Nat.card_congr j.toEquiv).symm.trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv j).symm.trans IsKleinFour.exponent_two⟩
  have hFD : F ≤ D := map_mono (subgroupOf_mono d.K hE)
  have hD : Nonempty (D ≃* DihedralGroup 4) := by
    obtain ⟨j⟩ := d.sk_dihedral
    exact ⟨(modelEquiv d d.sk inf_le_right).symm.trans j⟩
  let eK : d.K := ⟨e, hEK he⟩
  let zK : d.K := ⟨d.zK, hEK hz⟩
  have he1 : e ≠ 1 := fun h => heout (h ▸ (zpowers d.zK).one_mem)
  have hz1 : d.zK ≠ 1 := by
    intro h
    apply d.t_ne_one
    rw [← d.zK_conjugate, h]
    simp
  have heF : d.modelK eK ∈ F := by
    rw [modelSubgroup_mem]
    simpa only [MulEquiv.symm_apply_apply] using he
  have hzF : d.modelK zK ∈ F := by
    rw [modelSubgroup_mem]
    simpa only [MulEquiv.symm_apply_apply] using hz
  have heM1 : d.modelK eK ≠ 1 := fun h => he1
    (congrArg Subtype.val (d.modelK.injective (h.trans d.modelK.map_one.symm)))
  have hzM1 : d.modelK zK ≠ 1 := fun h => hz1
    (congrArg Subtype.val (d.modelK.injective (h.trans d.modelK.map_one.symm)))
  apply square_normalizes_of_fusion_witnesses d E hE hz he heout hc hsep
  · obtain ⟨k, hk, heq⟩ := m.four_transitive F hF _ heF heM1 _ hzF hzM1
    refine ⟨d.modelK.symm k, ⟨(d.modelK.symm k).property,
      (model_normalizer_mem d E hEK k).mp hk⟩, ?_⟩
    have hh := congrArg (fun a => (d.modelK.symm a : G)) heq
    simpa only [map_mul, map_inv, coe_mul, coe_inv, MulEquiv.symm_apply_apply] using hh
  · intro f hf hf2 hfout
    let bS : d.S := ⟨d.x⁻¹ * e * d.x,
      CoreReduction.conjugate_le d (hE.trans inf_le_left) (CoreReduction.conjugate_mem d he)⟩
    let bH : d.H := ⟨bS, CoreReduction.s_le_h d bS.property⟩
    let β := d.action bH
    have he2 : e ^ 2 = 1 := by
      simpa only [pow_two, coe_mul, coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
    have hb2 : bH ^ 2 = 1 := by
      apply Subtype.ext
      change (d.x⁻¹ * e * d.x) ^ 2 = 1
      simpa only [MulAut.conj_apply, inv_inv] using
        (show ((MulAut.conj d.x⁻¹) e) ^ 2 = 1 from by rw [← map_pow, he2, map_one])
    have hβ2 : β ^ 2 = 1 := by change (d.action bH) ^ 2 = 1; rw [← map_pow, hb2, map_one]
    have hβ1 : β ≠ 1 := by
      have ho := CoreReduction.conjugate_involution_noninner d (hE he) he2 heout
      intro h
      apply ho
      change β ∈ CoreReduction.innerSylow (CoreReduction.imageSylow d)
      rw [h]
      exact one_mem _
    have hfix : ∀ k ∈ normalizer (F : Set (alternatingGroup (Fin 6))), β k = k := by
      intro k hk
      let kK := d.modelK.symm k
      have hkn : (kK : G) ∈ normalizer (E : Set G) :=
        (model_normalizer_mem d E hEK k).mp hk
      have hcomm : (kK : G) * bS = (bS : G) * kK := hc kK ⟨kK.property, hkn⟩
      apply d.modelK.symm.injective
      apply Subtype.ext
      have ha := d.action_compatible bH kK
      change (d.modelK.symm (β (d.modelK kK)) : G) =
        (bS : G) * kK * (bS : G)⁻¹ at ha
      simpa only [kK, MulEquiv.apply_symm_apply, ← hcomm, mul_assoc, mul_inv_cancel, mul_one] using ha
    let fK : d.K := ⟨f, hf.2⟩
    have hfD : d.modelK fK ∈ D := by
      rw [modelSubgroup_mem]
      simpa only [MulEquiv.symm_apply_apply] using hf
    have hfM2 : (d.modelK fK) ^ 2 = 1 := by
      rw [← map_pow, show fK ^ 2 = 1 from Subtype.ext hf2, map_one]
    have hfF : d.modelK fK ∉ F := by
      intro h
      rw [modelSubgroup_mem] at h
      exact hfout (by simpa only [MulEquiv.symm_apply_apply] using h)
    obtain ⟨k, hk⟩ := m.outside_coboundary D F hD hF hFD β hβ2 hβ1 hfix
      _ hfD hfM2 hfF
    let kK := d.modelK.symm k
    have hh := congrArg (fun a => (d.modelK.symm a : G)) hk
    simp only [map_mul, map_inv, coe_mul, coe_inv, MulEquiv.symm_apply_apply] at hh
    have ha := d.action_compatible bH kK
    change (d.modelK.symm (β (d.modelK kK)) : G) = (bS : G) * kK * (bS : G)⁻¹ at ha
    simp only [kK, MulEquiv.apply_symm_apply] at ha
    rw [ha] at hh
    refine ⟨kK, kK.property, ?_⟩
    change (kK : G) * (bS : G) * (kK : G)⁻¹ = f * bS
    calc
      (kK : G) * (bS : G) * (kK : G)⁻¹ =
          ((kK : G) * ((bS : G) * kK * (bS : G)⁻¹)⁻¹) * bS := by group
      _ = f * bS := by rw [hh]


omit [Finite G] in
private theorem centralizes_of_center_image (S : Subgroup G) {a : G}
    (ha : a ∈ (center S).map S.subtype) : S ≤ centralizer ({a} : Set G) := by
  obtain ⟨b, hb, hba⟩ := ha
  change (b : G) = a at hba
  intro s hs
  apply mem_centralizer_singleton_iff.mpr
  simpa only [coe_mul, Subtype.coe_mk, hba] using
    congrArg Subtype.val (mem_center_iff.mp hb (⟨s, hs⟩ : S))

omit [Finite G] in
/-- The crossing group centralizes the source involution `z`. This only uses
the displayed center and conjugation relations in `Setup`. -/
public theorem crossing_centralizes_z (d : Setup G) : crossing d ≤ centralizer ({d.z} : Set G) := by
  have ht : d.S ≤ centralizer ({d.t} : Set G) := centralizes_of_center_image d.S (by
    rw [d.center_s]
    exact mem_sup_left (mem_zpowers _))
  have hk : d.S ≤ centralizer ({d.zK} : Set G) := centralizes_of_center_image d.S (by
    rw [d.center_s]
    exact mem_sup_right (mem_zpowers _))
  have htk : d.t * d.zK = d.zK * d.t := mem_centralizer_singleton_iff.mp (hk d.t_mem.1)
  refine sup_le ?_ (zpowers_le.mpr ?_)
  · intro s hs
    apply mem_centralizer_singleton_iff.mpr
    rw [d.z_eq]
    calc
      s * (d.t * d.zK) = (s * d.t) * d.zK := (mul_assoc _ _ _).symm
      _ = (d.t * s) * d.zK := by rw [mem_centralizer_singleton_iff.mp (ht hs)]
      _ = d.t * (s * d.zK) := mul_assoc _ _ _
      _ = d.t * (d.zK * s) := by rw [mem_centralizer_singleton_iff.mp (hk hs)]
      _ = (d.t * d.zK) * s := (mul_assoc _ _ _).symm
  · have hfix : d.x⁻¹ * d.z * d.x = d.z := by
      rw [d.z_eq]
      calc
        d.x⁻¹ * (d.t * d.zK) * d.x =
            (d.x⁻¹ * d.t * d.x) * (d.x⁻¹ * d.zK * d.x) := by group
        _ = d.zK * d.t := by rw [d.t_conjugate, d.zK_conjugate]
        _ = d.t * d.zK := htk.symm
    apply mem_centralizer_singleton_iff.mpr
    calc
      d.x * d.z = d.x * (d.x⁻¹ * d.z * d.x) := by rw [hfix]
      _ = d.z * d.x := by group

/-- Recover the nonfusion used in source 2.5.11(2) from the full-centralizer
statement in 2.5.22(2). If `t` fused to `z`, conjugating the crossing two-group
would put a subgroup of order 256 in `H`, whose Sylow two-subgroups have order
128. The displayed containment is a genuine extra source input, not a field
of `Setup`. -/
public theorem not_isConj_of_full_centralizer (d : Setup G) (r : CoreReduction d)
    (hC : centralizer ({d.t} : Set G) ≤ d.H) : ¬ IsConj d.t d.z := by
  rintro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let W := (crossing d).map (MulAut.conj g⁻¹).toMonoidHom
  have hWH : W ≤ d.H := by
    rintro _ ⟨a, ha, rfl⟩
    apply hC
    apply mem_centralizer_singleton_iff.mpr
    have hc := mem_centralizer_singleton_iff.mp (crossing_centralizes_z d ha)
    rw [← hg] at hc
    have hh := congrArg (fun b => g⁻¹ * b * g) hc
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mul_assoc, inv_mul_cancel, mul_inv_cancel, inv_mul_cancel_left, one_mul, mul_one] using hh
  have hp : IsPGroup 2 (crossing d) :=
    d.twoT.of_injective (inclusion (crossing_le_t d)) (inclusion_injective _)
  have hpW : IsPGroup 2 W := hp.map _
  obtain ⟨P, hP⟩ := (hpW.comap_of_injective d.H.subtype d.H.subtype_injective).exists_le_sylow
  have hWcard : Nat.card W = 256 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, crossing_card d r]
  have hScard : Nat.card (d.sylow : Subgroup d.H) = 128 := by
    rw [← card_map_of_injective d.H.subtype_injective, d.sylow_eq, r.card_s]
  have hPcard : Nat.card (P : Subgroup d.H) = 128 := by
    rw [P.card_eq_multiplicity, ← d.sylow.card_eq_multiplicity, hScard]
  have hle := card_le_of_le hP
  change Nat.card (W.subgroupOf d.H) ≤ Nat.card (P : Subgroup d.H) at hle
  rw [Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv, hWcard, hPcard] at hle
  omega


private theorem normalizer_card (d : Setup G) (r : CoreReduction d)
    (n : ActionNormalizer.ModelFacts) (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G)) :
    Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64 := by
  have hgen := ActionNormalizer.normalizer_eq_of_model d r n E hE he heout
  have hdisj := (NormalizerCalculation.factors_disjoint d r E hE he heout).mono
    le_rfl (show d.K ⊓ normalizer (E : Set G) ≤ d.K from inf_le_left)
  have hcomm := NormalizerCalculation.factors_commute d E hc
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) (d.K ⊓ normalizer (E : Set G)) hdisj hcomm
  obtain ⟨a⟩ := NormalizerCalculation.conjugate_dihedral d r E hE he heout
  obtain ⟨b⟩ := ActionNormalizer.normalizer_symmetric_of_model d n E hE
  have hcard := NormalizerCalculation.card_base_of_normalizer_model d E hE
    ⟨(MulEquiv.subgroupCongr hgen).trans (f.symm.trans (a.prodCongr b))⟩
  exact hcard

/-- The source nonfusion gives membership in the product of the two inner
Sylow factors. The four-group and compatible reflection are the independently
constructed choices used by the parent; their normalizer order is derived. -/
public theorem square_mem_of_nonfusion (d : Setup G) (r : CoreReduction d)
    (m : ModelFacts) (n : ActionNormalizer.ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) (hz : d.zK ∈ E)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G))
    (hsep : ¬ IsConj d.t d.z) : d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk := by
  have hcard := normalizer_card d r n E hE he heout hc
  have hs : d.x ^ 2 ∈ d.S ⊓ normalizer (E : Set G) :=
    ⟨d.square_mem, square_normalizes_of_model d m E hE hz he heout hc hsep⟩
  rwa [d.four_normalizer_eq_factor_product d.sk_card E hE hcard] at hs

/-- A corrected source route retaining the full centralizer statement
`C_G(t) ≤ H` from 2.5.22(2). This premise is absent from `Setup` and must be
supplied by the source assembly. No square or square-stability premise occurs. -/
public theorem square_mem_of_full_centralizer (d : Setup G) (r : CoreReduction d)
    (m : ModelFacts) (n : ActionNormalizer.ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) (hz : d.zK ∈ E)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G))
    (hC : centralizer ({d.t} : Set G) ≤ d.H) :
    d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk :=
  square_mem_of_nonfusion d r m n E hE hz he heout hc
    (not_isConj_of_full_centralizer d r hC)


omit [Finite G] in
private theorem exists_four_with_reflection (d : Setup G)
    (hD : Nonempty (d.sk ≃* DihedralGroup 4)) :
    ∃ (E : Subgroup G) (e : G), IsKleinFour E ∧ E ≤ d.sk ∧ d.zK ∈ E ∧
      e ∈ E ∧ e ∉ zpowers d.zK := by
  obtain ⟨j⟩ := hD
  let e := j.symm (DihedralGroup.sr 0)
  have he2 : (e : G) * e = 1 := by
    have hh : e ^ 2 = 1 := by
      apply j.injective
      simp only [map_pow, map_one, e, j.apply_symm_apply]
      decide
    simpa only [pow_two, coe_mul, coe_one] using congrArg Subtype.val hh
  have heout : (e : G) ∉ zpowers d.zK := by
    intro heZ
    have hecenter : e ∈ center d.sk := by
      have hh : (e : G) ∈ (center d.sk).map d.sk.subtype := by
        change (e : G) ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype
        rw [d.center_sk]
        exact heZ
      obtain ⟨k, hk, hke⟩ := hh
      exact (show k = e from Subtype.ext hke) ▸ hk
    have hc := congrArg j (mem_center_iff.mp hecenter (j.symm (DihedralGroup.r 1)))
    have hbad : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 =
        DihedralGroup.sr 0 * DihedralGroup.r 1 := by
      simpa only [map_mul, e, j.apply_symm_apply] using hc
    exact (by decide : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1) hbad
  have hz2 : d.zK * d.zK = 1 := by
    have hh : ((MulAut.conj d.x⁻¹) d.t) ^ 2 = 1 := by
      rw [← map_pow, d.t_square, map_one]
    simpa only [MulAut.conj_apply, inv_inv, d.t_conjugate, pow_two] using hh
  have hz1 : d.zK ≠ 1 := by
    intro h
    apply d.t_ne_one
    rw [← d.zK_conjugate, h]
    simp
  have he1 : (e : G) ≠ 1 := fun h => heout (h ▸ (zpowers d.zK).one_mem)
  have hze : d.zK ≠ (e : G) := fun h => heout (h ▸ mem_zpowers d.zK)
  have hzcenter : (⟨d.zK, CoreReduction.zK_mem_sk d⟩ : d.sk) ∈ center d.sk := by
    have hh : d.zK ∈ (center d.sk).map d.sk.subtype := by
      change d.zK ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype
      rw [d.center_sk]
      exact mem_zpowers _
    obtain ⟨k, hk, hval⟩ := hh
    exact (show k = ⟨d.zK, CoreReduction.zK_mem_sk d⟩ from Subtype.ext hval) ▸ hk
  have hcomm : Commute d.zK (e : G) :=
    (congrArg Subtype.val (mem_center_iff.mp hzcenter e)).symm
  let E := closure ({d.zK, (e : G)} : Set G)
  refine ⟨E, e, isKleinFour_closure_pair d.zK (e : G) hz2 he2 hz1 he1 hze hcomm,
    ?_, subset_closure (by simp), subset_closure (by simp), heout⟩
  apply (closure_le d.sk).2
  intro a ha
  rcases (show a = d.zK ∨ a = (e : G) from by simpa only
    [Set.mem_insert_iff, Set.mem_singleton_iff] using ha) with rfl | rfl
  · exact CoreReduction.zK_mem_sk d
  · exact e.property

/-- Construct all auxiliary choices and recover square membership from the
nonfusion in source 2.5.11(2). No compatible-choice witness is assumed. -/
public theorem square_mem_of_source_nonfusion (d : Setup G) (r : CoreReduction d)
    (m : ModelFacts) (n : ActionNormalizer.ModelFacts)
    (o : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (hsep : ¬ IsConj d.t d.z) :
    d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk := by
  obtain ⟨E, e, hfour, hE, hz, he, heout⟩ := exists_four_with_reflection d d.sk_dihedral
  let : IsKleinFour E := hfour
  obtain ⟨s, hc⟩ := FourGroupChoice.exists_replaceX_centralizing d o E hE he heout
  have hcard := normalizer_card (d.replaceX s) (CoreReduction.replaceX d r s)
    n E hE he heout hc
  have hsq := square_normalizes_of_model (d.replaceX s) m E hE hz he heout hc
    hsep
  have hs : d.x ^ 2 ∈ d.S ⊓ normalizer (E : Set G) :=
    ⟨d.square_mem, (d.four_square_replaceX_iff r d.sk_card E hE hcard s).mp hsq⟩
  rwa [d.four_normalizer_eq_factor_product d.sk_card E hE hcard] at hs

/-- The exact unresolved branch from `Setup` produces fusion of the two
distinguished involutions. The source excludes this fusion in 2.5.11(2). -/
public theorem isConj_of_square_notMem (d : Setup G) (r : CoreReduction d)
    (m : ModelFacts) (n : ActionNormalizer.ModelFacts)
    (o : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (hbad : d.x ^ 2 ∉ d.sk ⊔ conjugate d.x d.sk) : IsConj d.t d.z := by
  by_contra hsep
  exact hbad (square_mem_of_source_nonfusion d r m n o hsep)

/-- Recover crossing-square membership from the complete involution-centralizer
input of source 2.5.22. The auxiliary choices are constructed, and the original
`Setup`-only obligation remains separate from the omitted source input. -/
public theorem square_mem_of_source (d : Setup G) (r : CoreReduction d)
    (m : ModelFacts) (n : ActionNormalizer.ModelFacts)
    (o : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (hC : centralizer ({d.t} : Set G) ≤ d.H) :
    d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk :=
  square_mem_of_source_nonfusion d r m n o (not_isConj_of_full_centralizer d r hC)

end CFSG.Quasithin.Chapter2.A6ShadowConstruction.SquareMembership.Fusion
