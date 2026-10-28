module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Residual
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Centralizing
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Centerless
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Normalization.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Normalization.SylowTransvection

/-!
# Normalization and compatible models in the graph-field cover case

The centralizer of E fixes L and r, hence normalizes the actual residual
D = O²(C_L(r)). The two marked models supply transvections with different
centers. Explicitly correcting the images of z and r by these transvections
reduces every element of N_G(E) to C_G(E), proving N_G(E) ≤ N_G(D).
Frattini transitivity then gives the embedded residual-intersection identity,
with normality relative to N_G(E).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1191. The opposite residual equality and both intrinsic
models remain explicit inputs, as do the prepared Sylow and transport choices.

Sylow conjugacy inside C_G(E) places C_Q(E) in T while preserving all model
fields. The genuine graph-field fixed-Sylow theorem realizes the marked
transvection in the original T. Correcting Sylow conjugacy by this actor
then places the entire Q in T, and hence in N_T(E)Y, while fixing both
marks and preserving L and the actual residual. The intrinsic model
witnesses, graph-field marking and residual E₉ facts remain explicit inputs.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z r g : G} {L R : Subgroup G}

/-- Fixing both marks preserves C_L(r) and its characteristic two-residual. -/
theorem centralizer_four_le_residual_normalizer (h : IntersectionSetup T z L g R) :
    centralizer (fourGroup r z : Set G) ≤ normalizer (residual L r : Set G) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer ({r} : Set G)) (pResidual 2 _))
  apply le_trans ?_ inf_normalizer_le_normalizer_inf
  apply le_inf
  · apply le_trans ?_ (Centerless.centralizer_z_le_normalizer h)
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (ha z (mem_sup_right (mem_zpowers z))).symm
  · intro a ha
    apply (centralizer ({r} : Set G)).le_normalizer
    exact mem_centralizer_singleton_iff.mpr (ha r (mem_sup_left (mem_zpowers r))).symm

private theorem four_nonidentity_cases
    (hE : IsElementaryAbelian 2 (fourGroup r z))
    (hcard : Nat.card (fourGroup r z) = 4)
    (hr : r ≠ 1) (hz : z ≠ 1) (hrz : r ≠ z)
    {x : G} (hx : x ∈ fourGroup r z) (hx1 : x ≠ 1) :
    x = r ∨ x = z ∨ x = r * z := by
  let E := fourGroup r z
  let : IsElementaryAbelian 2 E := hE
  let : Nontrivial E := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; decide)
  let : IsKleinFour E := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  by_cases hxr : x = r
  · exact Or.inl hxr
  by_cases hxz : x = z
  · exact Or.inr (Or.inl hxz)
  right; right
  exact congrArg Subtype.val (IsKleinFour.eq_mul_of_ne_all
    (x := (⟨r, mem_sup_left (mem_zpowers r)⟩ : E))
    (y := (⟨z, mem_sup_right (mem_zpowers z)⟩ : E))
    (z := (⟨x, hx⟩ : E))
    (fun he => hr (congrArg Subtype.val he))
    (fun he => hz (congrArg Subtype.val he))
    (fun he => hrz (congrArg Subtype.val he))
    (fun he => hx1 (congrArg Subtype.val he))
    (fun he => hxr (congrArg Subtype.val he))
    (fun he => hxz (congrArg Subtype.val he)))

private theorem normalizer_four_le_of_transvections {D : Subgroup G}
    (hE : IsElementaryAbelian 2 (fourGroup r z))
    (hcard : Nat.card (fourGroup r z) = 4)
    (hr : r ≠ 1) (hz : z ≠ 1) (hrz : r ≠ z)
    (hC : centralizer (fourGroup r z : Set G) ≤ normalizer (D : Set G))
    {t s : G} (ht : t ∈ normalizer (D : Set G)) (hs : s ∈ normalizer (D : Set G))
    (htN : t ∈ normalizer (fourGroup r z : Set G))
    (hsN : s ∈ normalizer (fourGroup r z : Set G))
    (htr : MulAut.conj t r = r * z) (htz : MulAut.conj t z = z)
    (hsz : MulAut.conj s z = z * r) :
    normalizer (fourGroup r z : Set G) ≤ normalizer (D : Set G) := by
  have hrE : r ∈ fourGroup r z := mem_sup_left (mem_zpowers r)
  have hzE : z ∈ fourGroup r z := mem_sup_right (mem_zpowers z)
  have hz2 : z * z = 1 := by
    let : IsElementaryAbelian 2 (fourGroup r z) := hE
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzE
    simpa only [pow_two] using this
  have hcomm : z * r = r * z := by
    let : IsElementaryAbelian 2 (fourGroup r z) := hE
    exact congrArg Subtype.val (mul_comm (⟨z, hzE⟩ : fourGroup r z) ⟨r, hrE⟩)
  have hfix {a : G} (har : MulAut.conj a r = r) (haz : MulAut.conj a z = z) :
      a ∈ normalizer (D : Set G) := by
    apply hC
    have hb : fourGroup r z ≤ centralizer ({a} : Set G) := by
      apply sup_le <;> apply zpowers_le.mpr <;> apply mem_centralizer_singleton_iff.mpr
      · exact ((mul_inv_eq_iff_eq_mul).mp har).symm
      · exact ((mul_inv_eq_iff_eq_mul).mp haz).symm
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hb hx)
  have hfixz {a : G} (ha : a ∈ normalizer (fourGroup r z : Set G))
      (haz : MulAut.conj a z = z) : a ∈ normalizer (D : Set G) := by
    have ha1 : MulAut.conj a r ≠ 1 := fun he => hr ((MulAut.conj a).map_eq_one_iff.mp he)
    have harz : MulAut.conj a r ≠ z := fun he => hrz ((MulAut.conj a).injective (he.trans haz.symm))
    rcases four_nonidentity_cases hE hcard hr hz hrz
      ((mem_normalizer_iff.mp ha r).mp hrE) ha1 with har | har | har
    · exact hfix har haz
    · exact (harz har).elim
    · have hk : t⁻¹ * a ∈ normalizer (D : Set G) := by
        apply hfix
        · have he : MulAut.conj (t⁻¹ * a) r = (MulAut.conj t).symm (MulAut.conj a r) := by
            simp [MulAut.conj_apply, mul_assoc]
          change MulAut.conj a r = r * z at har
          rw [he, har, ← htr, MulEquiv.symm_apply_apply]
        · have he : MulAut.conj (t⁻¹ * a) z = (MulAut.conj t).symm (MulAut.conj a z) := by
            simp [MulAut.conj_apply, mul_assoc]
          rw [he, haz]
          exact (congrArg (MulAut.conj t).symm htz.symm).trans
            ((MulAut.conj t).symm_apply_apply z)
      simpa only [mul_inv_cancel_left] using (normalizer (D : Set G)).mul_mem ht hk
  intro x hx
  have hx1 : MulAut.conj x z ≠ 1 := fun he => hz ((MulAut.conj x).map_eq_one_iff.mp he)
  have hrep : ∃ a ∈ normalizer (D : Set G), a ∈ normalizer (fourGroup r z : Set G) ∧
      MulAut.conj a z = MulAut.conj x z := by
    rcases four_nonidentity_cases hE hcard hr hz hrz
      ((mem_normalizer_iff.mp hx z).mp hzE) hx1 with he | he | he
    · refine ⟨t * s, (normalizer (D : Set G)).mul_mem ht hs,
        (normalizer (fourGroup r z : Set G)).mul_mem htN hsN, ?_⟩
      have hh : MulAut.conj (t * s) z = MulAut.conj t (MulAut.conj s z) := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [hh, hsz, map_mul, htz, htr, ← mul_assoc, hcomm, mul_assoc, hz2, mul_one]
      exact he.symm
    · exact ⟨1, one_mem _, one_mem _, by simpa only [MulAut.conj_apply, one_mul, inv_one, mul_one] using he.symm⟩
    · exact ⟨s, hs, hsN, hsz.trans (hcomm.trans he.symm)⟩
  obtain ⟨a, ha, haE, haz⟩ := hrep
  have hk : a⁻¹ * x ∈ normalizer (D : Set G) := by
    apply hfixz ((normalizer (fourGroup r z : Set G)).mul_mem
      ((normalizer (fourGroup r z : Set G)).inv_mem haE) hx)
    have he : MulAut.conj (a⁻¹ * x) z = (MulAut.conj a).symm (MulAut.conj x z) := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [he, ← haz, MulEquiv.symm_apply_apply]
  simpa only [mul_inv_cancel_left] using (normalizer (D : Set G)).mul_mem ha hk
/-- Paired marked models and the opposite residual equality normalize D under all of N_G(E). -/
theorem normalizer_four_le_residual_normalizer
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (d' : NormalizerData (L.conjBy g) z r) (c' : CoverActionData d')
    (hopp : residual (L.conjBy g) z = residual L r) :
    normalizer (fourGroup r z : Set G) ≤ normalizer (residual L r : Set G) := by
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hrz : r ≠ z := by
    intro he
    exact hout (mem_sup_left (he ▸ central_involution_mem_centralizer h))
  obtain ⟨t, ht, htr⟩ := c.transvection
  obtain ⟨s, hs, hsz⟩ := c'.transvection
  have htz : MulAut.conj t z = z := by
    change t * z * t⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (c.fixes_z ht), mul_inv_cancel_right]
  have hsD : s ∈ normalizer (residual L r : Set G) :=
    hopp ▸ d'.normalizes_residual hs
  have hsN : s ∈ normalizer (fourGroup r z : Set G) := by
    simpa only [fourGroup, sup_comm] using d'.normalizes_four hs
  exact normalizer_four_le_of_transvections hE.1 hE.2 hr1 hz1 hrz
    (centralizer_four_le_residual_normalizer h) (d.normalizes_residual ht) hsD
    (d.normalizes_four ht) hsN htr htz hsz

/-- The actual embedded intersection identity, together with relative normality. -/
theorem residual_eq_coverIntersection_prepared
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d)
    (d' : NormalizerData (L.conjBy g) z r) (c' : CoverActionData d')
    (hopp : residual (L.conjBy g) z = residual L r) :
    residual L r = (pResidual 2 (coverComponentIntersection L r z)).map
      (coverComponentIntersection L r z).subtype ∧
    ((residual L r).subgroupOf (normalizer (fourGroup r z : Set G))).Normal := by
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have htrans := coverY_transitive_of_models hE.1 hE.2 hr1 hz1 hs d c d' c'
  have he := residual_eq_coverComponentIntersection_of_normalizes h hr hr2
    (compatible_conjugator_sends_z h hTC htransport hr hr2) htrans
    (normalizer_four_le_residual_normalizer h hr hr2 hout d c d' c' hopp)
  exact ⟨he, residual_normal_of_coverComponentIntersection he⟩

omit [Finite G] in
private theorem centralizes_four_of_fixes {a : G}
    (har : MulAut.conj a r = r) (haz : MulAut.conj a z = z) :
    a ∈ centralizer (fourGroup r z : Set G) := by
  have hb : fourGroup r z ≤ centralizer ({a} : Set G) := by
    apply sup_le <;> apply zpowers_le.mpr <;> apply mem_centralizer_singleton_iff.mpr
    · exact ((mul_inv_eq_iff_eq_mul).mp har).symm
    · exact ((mul_inv_eq_iff_eq_mul).mp haz).symm
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hb hx)

omit [Finite G] in
private theorem fixes_of_centralizes {a x : G}
    (ha : a ∈ centralizer ({x} : Set G)) : MulAut.conj a x = x := by
  change a * x * a⁻¹ = x
  rw [mem_centralizer_singleton_iff.mp ha, mul_inv_cancel_right]

private theorem conjugate_into_sylow {S A H : Subgroup G} (hs : SylowIn S H)
    (ha : IsPGroup 2 A) (hle : A ≤ H) : ∃ a ∈ H, A.conjBy a ≤ S := by
  obtain ⟨U, hU⟩ := (ha.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  obtain ⟨a, ha, he⟩ := (show SylowIn ((U : Subgroup H).map H.subtype) H from
    ⟨U, rfl⟩).exists_conjugator hs
  refine ⟨a, ha, ?_⟩
  rw [← he]
  apply map_mono
  rw [← map_subgroupOf_eq_of_le hle]
  exact map_mono hU

omit [Finite G] in
private theorem marks_of_centralizes_four {a : G}
    (ha : a ∈ centralizer (fourGroup r z : Set G)) :
    MulAut.conj a r = r ∧ MulAut.conj a z = z := by
  constructor <;> apply fixes_of_centralizes <;> apply mem_centralizer_singleton_iff.mpr
  · exact (ha r (mem_sup_left (mem_zpowers r))).symm
  · exact (ha z (mem_sup_right (mem_zpowers z))).symm

/-- Conjugation inside C_G(E) places C_Q(E) and transports every model field.
Both marks, L, and the actual embedded residual are preserved. -/
theorem exists_compatible_model_centralizer_in_sylow
    (h : IntersectionSetup T z L g R)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d) :
    ∃ a ∈ centralizer (fourGroup r z : Set G), ∃ d0 : NormalizerData L r z,
      CoverActionData d0 ∧ d0.Q = d.Q.conjBy a ∧
      (residual L r).conjBy a = residual L r ∧
      d0.Q ⊓ centralizer (fourGroup r z : Set G) ≤ (T : Subgroup G) := by
  obtain ⟨a, ha, hplace⟩ := conjugate_into_sylow hs
    (d.two_group.to_inf_left (K := centralizer (fourGroup r z : Set G))) inf_le_right
  have hmarks := marks_of_centralizes_four ha
  have hLa : L.conjBy a = L := mem_normalizer_iff_map_conj_eq.mp
    (Centerless.centralizer_z_le_normalizer h
      (mem_centralizer_singleton_iff.mpr (ha z (mem_sup_right (mem_zpowers z))).symm))
  let d0 := d.transport (MulAut.conj a) hLa hmarks.1 hmarks.2
  have hQ0 : d0.Q = d.Q.conjBy a := d.transport_Q _ _ _ _
  refine ⟨a, ha, d0, c.transport (MulAut.conj a) hLa hmarks.1 hmarks.2, hQ0,
    mem_normalizer_iff_map_conj_eq.mp (centralizer_four_le_residual_normalizer h ha), ?_⟩
  have hCE : (centralizer (fourGroup r z : Set G)).conjBy a =
      centralizer (fourGroup r z : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((centralizer (fourGroup r z : Set G)).le_normalizer ha)
  have he : (d.Q ⊓ centralizer (fourGroup r z : Set G)).conjBy a =
      d0.Q ⊓ centralizer (fourGroup r z : Set G) := by
    change (d.Q ⊓ centralizer (fourGroup r z : Set G)).map (MulAut.conj a).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj a).injective]
    change d.Q.conjBy a ⊓ (centralizer (fourGroup r z : Set G)).conjBy a = _
    rw [hCE, hQ0]
  exact (he ▸ hplace).trans inf_le_left

/-- A transvection already in T upgrades the Sylow centralizer to a Sylow
subgroup of the normalizer of E fixing z. -/
theorem sylow_marked_normalizer_of_transvection
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    {t : G} (htT : t ∈ (T : Subgroup G)) (htN : t ∈ normalizer (fourGroup r z : Set G))
    (htr : MulAut.conj t r = r * z) :
    SylowIn ((T : Subgroup G) ⊓ normalizer (fourGroup r z : Set G))
      (centralizer ({z} : Set G) ⊓ normalizer (fourGroup r z : Set G)) := by
  let E := fourGroup r z
  let H := centralizer ({z} : Set G) ⊓ normalizer (E : Set G)
  let S := (T : Subgroup G) ⊓ normalizer (E : Set G)
  have hSH : S ≤ H := le_inf (inf_le_left.trans h.sylow_centralizes) inf_le_right
  have hSp := T.isPGroup'.to_inf_left (K := normalizer (E : Set G))
  obtain ⟨P, hP⟩ := (hSp.of_equiv (subgroupOfEquivOfLe hSH).symm).exists_le_sylow
  let U := (P : Subgroup H).map H.subtype
  have hSU : S ≤ U := by
    rw [← map_subgroupOf_eq_of_le hSH]
    exact map_mono hP
  have hUH : U ≤ H := map_subtype_le _
  have hUE : U ⊓ centralizer (E : Set G) = (T : Subgroup G) ⊓ centralizer (E : Set G) :=
    hs.maximal ((P.isPGroup'.map H.subtype).to_inf_left (K := centralizer (E : Set G)))
      inf_le_right (le_inf ((inf_le_inf_left _ (centralizer_le_normalizer _)).trans hSU) inf_le_right)
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hrz : r ≠ z := by
    intro he
    exact hout (mem_sup_left (he ▸ central_involution_mem_centralizer h))
  have hUT : U ≤ (T : Subgroup G) := by
    intro x hx
    have hxN := (hUH hx).2
    have hxz := fixes_of_centralizes (hUH hx).1
    have hx1 : MulAut.conj x r ≠ 1 := fun he => hr1 ((MulAut.conj x).map_eq_one_iff.mp he)
    have hxr : MulAut.conj x r ≠ z := fun he => hrz ((MulAut.conj x).injective (he.trans hxz.symm))
    rcases four_nonidentity_cases hE.1 hE.2 hr1 hz1 hrz
      ((mem_normalizer_iff.mp hxN r).mp (mem_sup_left (mem_zpowers r))) hx1 with he | he | he
    · exact (hUE.le ⟨hx, centralizes_four_of_fixes he hxz⟩).1
    · exact (hxr he).elim
    · have hkU : t⁻¹ * x ∈ U := U.mul_mem (U.inv_mem (hSU ⟨htT, htN⟩)) hx
      have hkC : t⁻¹ * x ∈ centralizer (E : Set G) := by
        apply centralizes_four_of_fixes
        · have hh : MulAut.conj (t⁻¹ * x) r = (MulAut.conj t).symm (MulAut.conj x r) := by
            simp [MulAut.conj_apply, mul_assoc]
          change MulAut.conj x r = r * z at he
          rw [hh, he, ← htr, MulEquiv.symm_apply_apply]
        · exact fixes_of_centralizes (hUH hkU).1
      have hkT := (hUE.le ⟨hkU, hkC⟩).1
      simpa only [mul_inv_cancel_left] using (T : Subgroup G).mul_mem htT hkT
  exact ⟨P, le_antisymm (le_inf hUT (hUH.trans inf_le_right)) hSU⟩

/-- Once the marked transvection is realized in T, Sylow conjugacy can be
corrected inside T to fix r as well as z. The whole Q is then placed in T. -/
theorem exists_compatible_model_in_sylow_of_transvection
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d)
    {t : G} (htT : t ∈ (T : Subgroup G)) (htN : t ∈ normalizer (fourGroup r z : Set G))
    (htr : MulAut.conj t r = r * z) :
    ∃ a ∈ centralizer (fourGroup r z : Set G), ∃ d0 : NormalizerData L r z,
      CoverActionData d0 ∧ d0.Q = d.Q.conjBy a ∧
      (residual L r).conjBy a = residual L r ∧
      d0.Q ≤ (T : Subgroup G) ∧ d0.Q ≤ coverOvergroup T r z := by
  have hS := sylow_marked_normalizer_of_transvection h hr hr2 hout hs htT htN htr
  obtain ⟨a, ha, hQa⟩ := conjugate_into_sylow hS d.two_group
    (le_inf c.fixes_z d.normalizes_four)
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hrz : r ≠ z := by
    intro he
    exact hout (mem_sup_left (he ▸ central_involution_mem_centralizer h))
  have haz := fixes_of_centralizes ha.1
  have ha1 : MulAut.conj a r ≠ 1 := fun he => hr1 ((MulAut.conj a).map_eq_one_iff.mp he)
  have harz : MulAut.conj a r ≠ z := fun he => hrz ((MulAut.conj a).injective (he.trans haz.symm))
  have hplaced : ∃ b ∈ centralizer (fourGroup r z : Set G), d.Q.conjBy b ≤ (T : Subgroup G) := by
    rcases four_nonidentity_cases hE.1 hE.2 hr1 hz1 hrz
      ((mem_normalizer_iff.mp ha.2 r).mp (mem_sup_left (mem_zpowers r))) ha1 with he | he | he
    · exact ⟨a, centralizes_four_of_fixes he haz, hQa.trans inf_le_left⟩
    · exact (harz he).elim
    · refine ⟨t⁻¹ * a, ?_, ?_⟩
      · apply centralizes_four_of_fixes
        · have hh : MulAut.conj (t⁻¹ * a) r = (MulAut.conj t).symm (MulAut.conj a r) := by
            simp [MulAut.conj_apply, mul_assoc]
          change MulAut.conj a r = r * z at he
          rw [hh, he, ← htr, MulEquiv.symm_apply_apply]
        · have hc : t⁻¹ * a ∈ centralizer ({z} : Set G) :=
            (centralizer ({z} : Set G)).mul_mem
              ((centralizer ({z} : Set G)).inv_mem (h.sylow_centralizes htT)) ha.1
          exact fixes_of_centralizes hc
      · rw [← conjBy_conjBy]
        have hh := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) (hQa.trans inf_le_left)
        have hT : (T : Subgroup G).conjBy t⁻¹ = (T : Subgroup G) :=
          mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ((T : Subgroup G).inv_mem htT))
        exact hT ▸ hh
  obtain ⟨b, hb, hQb⟩ := hplaced
  have hmarks := marks_of_centralizes_four hb
  have hLb : L.conjBy b = L := mem_normalizer_iff_map_conj_eq.mp
    (Centerless.centralizer_z_le_normalizer h
      (mem_centralizer_singleton_iff.mpr (hb z (mem_sup_right (mem_zpowers z))).symm))
  let d0 := d.transport (MulAut.conj b) hLb hmarks.1 hmarks.2
  have hQ0 : d0.Q = d.Q.conjBy b := d.transport_Q _ _ _ _
  have hQT : d0.Q ≤ (T : Subgroup G) := hQ0.symm ▸ hQb
  refine ⟨b, hb, d0, c.transport (MulAut.conj b) hLb hmarks.1 hmarks.2, hQ0,
    mem_normalizer_iff_map_conj_eq.mp (centralizer_four_le_residual_normalizer h hb), hQT, ?_⟩
  exact (le_inf hQT d0.normalizes_four).trans le_sup_left


/-- The prepared source saturation supplies the Sylow centralizer used above. -/
theorem four_centralizer_sylow_of_empty
    (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G))) :
    SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)) := by
  have hc := hsmall _ h.mem_delta (fun hm => hempty ⟨_, hm⟩) R h.sylow
  have hR : zpowers r = R := eq_of_le_of_card_ge (zpowers_le.mpr hr)
    (by rw [Nat.card_zpowers, hr2, hc])
  exact Centerless.four_centralizer_sylow h hR hr2 hsat

/-- Compatible placement of the entire quaternion model in the original
prepared T. The marked transvection is derived from the actual graph-field
action, and centralizer saturation follows from the source Sylow choice.
The conjugator fixes both marks, preserves the actual residual, and transports
all normalizer and cover-action fields, including their relative quotients. -/
theorem exists_compatible_model_in_sylow_prepared {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d) :
    ∃ a ∈ centralizer (fourGroup r z : Set G), ∃ d0 : NormalizerData L r z,
      CoverActionData d0 ∧ d0.Q = d.Q.conjBy a ∧
      (residual L r).conjBy a = residual L r ∧
      d0.Q ≤ (T : Subgroup G) ∧ d0.Q ≤ coverOvergroup T r z := by
  obtain ⟨t, ht, htr⟩ := SylowTransvection.exists_transvection_prepared
    hG h hr hr2 hout hTC hcore hmodel hD h9 d c
  exact exists_compatible_model_in_sylow_of_transvection h hr hr2 hout
    (four_centralizer_sylow_of_empty h hsmall hempty hr hr2 hsat) d c ht.1 ht.2 htr

/-- The complete normalization and intersection deduction on the saturated
source choices. No residual normalization or intersection identity is assumed. -/
theorem cover_normalization_prepared
    (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z)
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (d' : NormalizerData (L.conjBy g) z r) (c' : CoverActionData d')
    (hopp : residual (L.conjBy g) z = residual L r) :
    normalizer (fourGroup r z : Set G) ≤ normalizer (residual L r : Set G) ∧
    residual L r = (pResidual 2 (coverComponentIntersection L r z)).map
      (coverComponentIntersection L r z).subtype ∧
    ((residual L r).subgroupOf (normalizer (fourGroup r z : Set G))).Normal :=
  ⟨normalizer_four_le_residual_normalizer h hr hr2 hout d c d' c' hopp,
    residual_eq_coverIntersection_prepared h hr hr2 hout hTC htransport
      (four_centralizer_sylow_of_empty h hsmall hempty hr hr2 hsat) d c d' c' hopp⟩

/-- The centralizing alternative needs only the C_Q(E) placement, which is
constructed here. No placement of the entire Q is assumed. -/
theorem coverY_not_le_residual_centralizer
    (h : IntersectionSetup T z L g R) (hqt : IsQuasithin G)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d)
    (d' : NormalizerData (L.conjBy g) z r) (c' : CoverActionData d')
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9) :
    ¬ coverY T r z ≤ centralizer (residual L r : Set G) := by
  intro hfix
  obtain ⟨_, _, d0, c0, _, _, hplace⟩ :=
    exists_compatible_model_centralizer_in_sylow h hs d c
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have htrans := coverY_transitive_of_models hE.1 hE.2 hr1 hz1 hs d0 c0 d' c'
  obtain ⟨x, hx, hx3, hxD, hxf⟩ := independent_three_of_coverY_centralizes
    d0 c0 hD h9 hplace hE.2 hz1 htrans hfix
  exact no_independent_centralizing_three h hqt hr hr2 hout hD h9
    (coverY_le_normalizer T r z hx) hx3 hxD hxf

end CFSG.Quasithin.Chapter16.Intersections.GraphField
