module

public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransportAlgebra
public import Theory.GroupTheory.ElementaryCosetSquareRoots

/-!
# Eight square roots in Parrott's elementary cosets

The commutator map from F to F induced by x has image ⟨t,v⟩:
it sends v to t, u to v, and the other three basis elements to one.
The image has order four, so its kernel C_F(x) has order eight.
The elementary-coset root equivalence counts eight roots of x² in xF,
and also in x⁻¹F. The cosets are distinct and supply sixteen roots in K.
Transport by any supplied normalizer involution gives
the same count in the transported coset.

These are local coset counts. Exhaustion of the entire core root fiber and
the involution-orbit selection require additional arguments.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private def displacement (F : Subgroup G) [IsElementaryAbelian 2 F]
    (m : G) (hm : m ∈ normalizer (F : Set G)) : F →* G := by
  let φ : F →* F := {
    toFun := fun g => ⟨m⁻¹ * g * m, (mem_normalizer_iff''.mp hm _).mp g.property⟩
    map_one' := by ext; simp
    map_mul' := by intros; ext; simp only [coe_mul]; group }
  let δ : F →* F := {
    toFun := fun g => φ g * g
    map_one' := by simp
    map_mul' := by intro a b; simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _ }
  exact F.subtype.comp δ

private theorem displacement_apply (F : Subgroup G) [IsElementaryAbelian 2 F]
    (m : G) (hm : m ∈ normalizer (F : Set G)) (g : F) :
    displacement F m hm g = (m⁻¹ * g * m) * g := rfl

private theorem displacement_ker (F : Subgroup G) [IsElementaryAbelian 2 F]
    (m : G) (hm : m ∈ normalizer (F : Set G)) :
    (displacement F m hm).ker.map F.subtype = F ⊓ centralizer ({m} : Set G) := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.property, mem_centralizer_singleton_iff.mpr ?_⟩
    change (m⁻¹ * g * m) * g = 1 at hg
    have hi : (g : G)⁻¹ = g := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (g : G) g.property)
    have he : m⁻¹ * g * m = g := by rwa [mul_eq_one_iff_eq_inv, hi] at hg
    calc
      (g : G) * m = m * (m⁻¹ * g * m) := by group
      _ = m * g := by rw [he]
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    change (m⁻¹ * g * m) * g = 1
    rw [mul_assoc m⁻¹, mem_centralizer_singleton_iff.mp hc, inv_mul_cancel_left]
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) g hg

private theorem displacement_commutator (F : Subgroup G) [IsElementaryAbelian 2 F]
    (m : G) (hm : m ∈ normalizer (F : Set G)) (g : F) :
    displacement F m hm g = Tits.parrottCommutator m g := by
  have hi : (g : G)⁻¹ = g := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (g : G) g.property)
  simp only [displacement_apply, Tits.parrottCommutator, hi]

/-- The centralizer of x in the supplied elementary subgroup has order eight. -/
public theorem ParrottSylowGeneratorData.x_elementary_centralizer_card [Finite G] (f : ParrottSylowGeneratorData n) :
    Nat.card (e.F ⊓ centralizer ({f.x} : Set G) : Subgroup G) = 8 := by
  let _ := e.elementary
  have hxN : f.x ∈ normalizer (e.F : Set G) :=
    map_subtype_le _ f.x_mem_normalizer_core
  let δ := displacement e.F f.x hxN
  let L := zpowers n.t ⊔ zpowers n.v
  have hgF (g : G) (hg : g ∈ ({z, n.t, n.v, f.u, f.a} : Set G)) : g ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure hg
  have hz := hgF z (by simp)
  have ht := hgF n.t (by simp)
  have hv := hgF n.v (by simp)
  have hu := hgF f.u (by simp)
  have ha := hgF f.a (by simp)
  have he (g : G) (hg : g ∈ e.F) : δ ⟨g, hg⟩ = Tits.parrottCommutator f.x g :=
    displacement_commutator e.F f.x hxN ⟨g, hg⟩
  have hδz : δ ⟨z, hz⟩ = 1 := (he z hz).trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_zx.symm)
  have hδt : δ ⟨n.t, ht⟩ = 1 := (he n.t ht).trans f.eq01_xt
  have hδv : δ ⟨n.v, hv⟩ = n.t := (he n.v hv).trans f.eq01_xv
  have hδu : δ ⟨f.u, hu⟩ = n.v := (he f.u hu).trans f.eq01_xu
  have hδa : δ ⟨f.a, ha⟩ = 1 := (he f.a ha).trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr
      ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq16_ax).symm)
  have hδrange : δ.range = L := by
    apply le_antisymm
    · have hF : e.F ≤ (L.comap δ).map e.F.subtype := by
        conv_lhs => rw [← f.elementary_basis]
        apply (closure_le _).mpr
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl
        · exact ⟨⟨_, hz⟩, by change δ _ ∈ L; rw [hδz]; exact L.one_mem, rfl⟩
        · exact ⟨⟨n.t, ht⟩, by change δ _ ∈ L; rw [hδt]; exact L.one_mem, rfl⟩
        · exact ⟨⟨n.v, hv⟩, by change δ _ ∈ L; rw [hδv]; exact mem_sup_left (mem_zpowers _), rfl⟩
        · exact ⟨⟨f.u, hu⟩, by change δ _ ∈ L; rw [hδu]; exact mem_sup_right (mem_zpowers _), rfl⟩
        · exact ⟨⟨f.a, ha⟩, by change δ _ ∈ L; rw [hδa]; exact L.one_mem, rfl⟩
      rintro g ⟨g, rfl⟩
      obtain ⟨b, hb, hbg⟩ := hF g.property
      have hh : b = g := Subtype.ext hbg
      change δ b ∈ L at hb
      rwa [hh] at hb
    · exact sup_le (zpowers_le.mpr ⟨⟨n.v, hv⟩, hδv⟩)
        (zpowers_le.mpr ⟨⟨f.u, hu⟩, hδu⟩)
  have hvout : n.v ∉ zpowers n.t := by
    intro hh
    apply n.v_not_mem_core_center
    rw [n.core_center_eq]
    exact mem_sup_right hh
  have hvnorm : n.v ∈ normalizer (zpowers n.t : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr f.comm_tv.symm.eq
  have hL : Nat.card L = 4 := by
    rw [show L = zpowers n.t ⊔ zpowers n.v from rfl,
      card_sup_zpowers_of_normalizing_involution (zpowers n.t) n.v f.v_sq hvout hvnorm,
      Nat.card_zpowers, n.t_order]
  have hc := δ.ker.card_mul_index
  rw [index_ker, hδrange, hL, e.card] at hc
  have hker : Nat.card δ.ker = 8 := by omega
  rw [← displacement_ker e.F f.x hxN, card_map_of_injective e.F.subtype_injective]
  exact hker
namespace ParrottSylowGeneratorData

/-- Exactly eight elements of xF have square x². -/
public theorem x_coset_square_roots_ncard [Finite G] (f : ParrottSylowGeneratorData n) :
    {g : G | f.x⁻¹ * g ∈ e.F ∧ g ^ 2 = f.x ^ 2}.ncard = 8 := by
  let _ := e.elementary
  rw [ncard_square_coset, f.x_elementary_centralizer_card]

/-- Exactly eight elements of x⁻¹F have square x². -/
public theorem x_inverse_coset_square_roots_ncard [Finite G]
    (f : ParrottSylowGeneratorData n) :
    {g : G | f.x * g ∈ e.F ∧ g ^ 2 = f.x ^ 2}.ncard = 8 := by
  let _ := e.elementary
  rw [ncard_square_inverse_coset e.F f.x f.eq01_x, f.x_elementary_centralizer_card]

/-- The two root cosets xF and x⁻¹F are distinct: x² does not lie in F. -/
public theorem x_sq_not_mem_elementary (f : ParrottSylowGeneratorData n) :
    f.x ^ 2 ∉ e.F := by
  let _ := e.elementary
  intro hx
  have hy : f.y ∈ e.F := by
    have hh := e.F.mul_mem hx (e.F.inv_mem e.z_mem_inf.2)
    rw [f.eq04] at hh
    simpa only [mul_inv_cancel_right] using hh
  have hu : f.u ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have hcomm : Commute f.y f.u :=
    congrArg e.F.subtype (mul_comm (⟨f.y, hy⟩ : e.F) ⟨f.u, hu⟩)
  have hconj : (MulAut.conj f.y⁻¹) f.u = f.u := by
    simp only [MulAut.conj_apply, inv_inv, hcomm.inv_left.eq, mul_assoc,
      inv_mul_cancel, mul_one]
  have ht1 : n.t = 1 := mul_left_cancel
    ((f.y_conjugation.2.1.symm.trans hconj).trans (mul_one f.u).symm)
  have ho := n.t_order
  rw [ht1, orderOf_one] at ho
  norm_num at ho

/-- The two elementary cosets already supply sixteen distinct roots in K.
Only the upper bound or the two-coset exhaustion remains for an exact census. -/
public theorem x_square_roots_in_core_ncard_ge_sixteen [Finite G]
    (f : ParrottSylowGeneratorData n) :
    16 ≤ {g : G | g ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype ∧ g ^ 2 = f.x ^ 2}.ncard := by
  let K := (pCore 2 (normalizer (e.F : Set G))).map
    (normalizer (e.F : Set G)).subtype
  let A : Set G := {g | f.x⁻¹ * g ∈ e.F ∧ g ^ 2 = f.x ^ 2}
  let B : Set G := {g | f.x * g ∈ e.F ∧ g ^ 2 = f.x ^ 2}
  have hAB : Disjoint A B := Set.disjoint_left.mpr (by
    rintro g ⟨hg, _⟩ ⟨hg', _⟩
    apply f.x_sq_not_mem_elementary
    have hh := e.F.mul_mem hg' (e.F.inv_mem hg)
    convert hh using 1
    simp only [pow_two]
    group)
  have hxK : f.x ∈ K := f.x_mem_normalizer_core
  have hFK : e.F ≤ K := n.elementary_le_omega.trans n.omega_le_core
  have hsub : A ∪ B ⊆ {g : G | g ∈ K ∧ g ^ 2 = f.x ^ 2} := by
    rintro g (⟨hg, hg2⟩ | ⟨hg, hg2⟩)
    · exact ⟨by simpa using K.mul_mem hxK (hFK hg), hg2⟩
    · exact ⟨by simpa using K.mul_mem (K.inv_mem hxK) (hFK hg), hg2⟩
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hAB] at hc
  have hA : A.ncard = 8 := f.x_coset_square_roots_ncard
  have hB : B.ncard = 8 := f.x_inverse_coset_square_roots_ncard
  rw [hA, hB] at hc
  exact hc

end ParrottSylowGeneratorData

namespace ParrottNormalizerTransportData

/-- The supplied transport sends the eight-root coset bijectively to an
actual coset of F with the distinguished square wuvtz. -/
public theorem x_conj_coset_square_roots_ncard [Finite G]
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f) :
    {g : G | (k.s⁻¹ * f.x * k.s)⁻¹ * g ∈ e.F ∧
      g ^ 2 = f.w * f.u * n.v * n.t * z}.ncard = 8 := by
  let φ := MulAut.conj k.s⁻¹
  have hF (g : G) : φ g ∈ e.F ↔ g ∈ e.F := by
    simpa only [φ, MulAut.conj_apply, inv_inv] using
      (mem_normalizer_iff''.mp k.mem_normalizer g).symm
  have hc := ncard_square_coset_mulEquiv e.F f.x φ hF
  simp only [φ, MulAut.conj_apply, inv_inv] at hc
  rw [k.x_conj_sq] at hc
  exact hc.trans f.toParrottSylowGeneratorData.x_coset_square_roots_ncard

end ParrottNormalizerTransportData

end Stellmacher.Recognition
