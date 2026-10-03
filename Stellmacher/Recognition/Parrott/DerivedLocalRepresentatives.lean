module

public import Stellmacher.Recognition.Parrott.DerivedConjugacyCensus
public import Stellmacher.Recognition.Parrott.SecondElementary
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Parrott's two local derived-core representatives

For H=C_G(z), J=O₂(H), and E the ambient image of J′, choose representatives
of the two H-classes in E outside ⟨z⟩. Their centralizers have orders 1024
and 512, hence are two-groups. Sylow conjugacy in H moves each centralizer
into the supplied local Sylow, preserving both classes and their orders.
The derived-core center formula then identifies their centers with ⟨z,t⟩
and ⟨z,v⟩. The supplied Sylow subgroup and second elementary subgroup are
retained throughout; only the representatives are conjugated.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, especially the local-centralizer paragraph on p.674.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G]

private theorem position_derived_representative
    (z : G) (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ x : G, x ∈ E → x ∉ zpowers z → ∀ n : ℕ,
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) = 2 ^ n →
      ∃ t : G, t ∈ E ∧ t ∉ zpowers z ∧
        (∃ a : H, (a : G) * x * (a : G)⁻¹ = t) ∧
        H ⊓ centralizer ({t} : Set G) =
          (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) ∧
        Nat.card (H ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ n := by
  intro H J E x hx hxZ n hc
  let D := (commutator J).map J.subtype
  have hDmap : D.map H.subtype = E := map_map _ _ _
  obtain ⟨xH, hxD, rfl⟩ := hDmap.symm ▸ hx
  have hcard (y : H) :
      Nat.card (centralizer ({y} : Set H)) =
        Nat.card (H ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) := by
    rw [← map_subtype_centralizer_singleton H y,
      card_map_of_injective H.subtype_injective]
  have hp : IsPGroup 2 (centralizer ({xH} : Set H)) :=
    IsPGroup.of_card (n := n) ((hcard xH).trans hc)
  obtain ⟨a, ha, hac⟩ := exists_conj_centralizer_le_sylow d.localSylow xH hp
  let tH : H := a * xH * a⁻¹
  let f := MulAut.conj (a : G)
  have hfz : f z = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
  have htE : (tH : G) ∈ E := by
    rw [← hDmap]
    exact mem_map_of_mem H.subtype ((inferInstance : D.Normal).conj_mem xH hxD a)
  have htZ : (tH : G) ∉ zpowers z := by
    intro ht
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ht
    apply hxZ
    refine mem_zpowers_iff.mpr ⟨k, f.injective ?_⟩
    rw [map_zpow, hfz]
    exact hk
  have hCT : H ⊓ centralizer ({(tH : G)} : Set G) ≤ (d.sylow : Subgroup G) := by
    rw [← map_subtype_centralizer_singleton H tH, d.sylow_map]
    exact map_mono ha
  have hTH : (d.sylow : Subgroup G) ≤ H := by
    rw [d.sylow_map]
    exact map_subtype_le _
  refine ⟨tH, htE, htZ, ⟨a, rfl⟩, ?_, ?_⟩
  · exact le_antisymm (le_inf hCT inf_le_right) (inf_le_inf_right _ hTH)
  · exact (hcard tH).symm.trans (hac.trans ((hcard xH).trans hc))

/-- The two local representatives, with their entire H-centralizers in the
supplied Sylow subgroup, the exact orders, centers, and H-conjugacy census. -/
public theorem parrott_derived_local_representatives
    (z : G) (h : ParrottCentralizerHypotheses z) (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let T := (d.sylow : Subgroup G)
    ∃ t v : G, t ∈ E ∧ t ∉ zpowers z ∧ v ∈ E ∧ v ∉ zpowers z ∧
      orderOf t = 2 ∧ Commute z t ∧ orderOf v = 2 ∧ Commute z v ∧
      H ⊓ centralizer ({t} : Set G) = T ⊓ centralizer ({t} : Set G) ∧
      Nat.card (T ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 ∧
      (center (T ⊓ centralizer ({t} : Set G) : Subgroup G)).map
        (T ⊓ centralizer ({t} : Set G)).subtype = closure ({z, t} : Set G) ∧
      H ⊓ centralizer ({v} : Set G) = T ⊓ centralizer ({v} : Set G) ∧
      Nat.card (T ⊓ centralizer ({v} : Set G) : Subgroup G) = 512 ∧
      (center (T ⊓ centralizer ({v} : Set G) : Subgroup G)).map
        (T ⊓ centralizer ({v} : Set G)).subtype = closure ({z, v} : Set G) ∧
      ∀ u : G, u ∈ E → u ∉ zpowers z →
        (∃ a : H, (a : G) * t * (a : G)⁻¹ = u) ∨
        (∃ a : H, (a : G) * v * (a : G)⁻¹ = u) := by
  intro H J E T
  obtain ⟨x, y, hxE, hxZ, hyE, hyZ, hxc, hyc, hcover⟩ :=
    parrott_derived_conjugacy_census z h
  obtain ⟨t, htE, htZ, ⟨a, ha⟩, htlocal, htc⟩ :=
    position_derived_representative z d x hxE hxZ 10 hxc
  obtain ⟨v, hvE, hvZ, ⟨b, hb⟩, hvlocal, hvc⟩ :=
    position_derived_representative z d y hyE hyZ 9 hyc
  obtain ⟨ht2, hzt⟩ := parrott_derived_noncentral_involution z h t htE htZ
  obtain ⟨hv2, hzv⟩ := parrott_derived_noncentral_involution z h v hvE hvZ
  have hcenter (w : G) (hwE : w ∈ E) (hwZ : w ∉ zpowers z) :
      (center (T ⊓ centralizer ({w} : Set G) : Subgroup G)).map
        (T ⊓ centralizer ({w} : Set G)).subtype = closure ({z, w} : Set G) := by
    apply parrott_derived_intermediate_centralizer_center z h w hwE hwZ
    · apply inf_le_inf_right
      change J.map H.subtype ≤ (d.sylow : Subgroup G)
      rw [d.sylow_map]
      exact map_mono (pCore_isPGroup.le_sylow_of_normal d.localSylow)
    · apply inf_le_inf_right
      change (d.sylow : Subgroup G) ≤ H
      rw [d.sylow_map]
      exact map_subtype_le _
  refine ⟨t, v, htE, htZ, hvE, hvZ, ht2, hzt, hv2, hzv, htlocal,
    ?_, hcenter t htE htZ, hvlocal, ?_, hcenter v hvE hvZ, ?_⟩
  · rw [← htlocal]
    exact htc
  · rw [← hvlocal]
    exact hvc
  · intro u huE huZ
    rcases hcover u huE huZ with ⟨c, hc⟩ | ⟨c, hc⟩
    · left
      refine ⟨c * a⁻¹, ?_⟩
      rw [← ha]
      simpa only [coe_mul, coe_inv, mul_inv_rev, inv_inv, mul_assoc,
        inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc
    · right
      refine ⟨c * b⁻¹, ?_⟩
      rw [← hb]
      simpa only [coe_mul, coe_inv, mul_inv_rev, inv_inv, mul_assoc,
        inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc

end Stellmacher.Recognition
