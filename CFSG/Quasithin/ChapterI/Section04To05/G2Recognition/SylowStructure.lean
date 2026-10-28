module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.QuaternionCore
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Fusion
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter
public import Theory.GroupTheory.NormalFourCentralizerSeparation
public import Theory.GroupTheory.CentralizerEmbeddingTransport
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Ambient Sylow subgroups in a G₂(3)-type group

The quaternion subgroup Q₁Q₂ is normal of order 32 in H. Every Sylow
T of H has order 64, so its quotient by that subgroup is cyclic of order
two. Consequently T′ ∩ Z(T) is exactly the original common involution
line. This characteristic description forces the ambient normalizer of
T into H, promoting T to an ambient Sylow subgroup without conjugation.
Thus every ambient Sylow has order 64. The previously proved Z-star
argument now supplies a distinct conjugate of the marked involution in H.

Source: Fong–Wong, Nagoya Math. J. 36 (1969), §2B, printed p.151,
DOI 10.1017/S0027763000013180; Aschbacher–Smith §I.4, printed p.417.
The remaining extension and recognition argument belongs to
`qt-i45-g2-recognition`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

theorem quaternionCore_le_sylow (T : Sylow 2 c.H) : quaternionCore c ≤ T :=
  (IsPGroup.of_card (p := 2) (n := 5) (quaternionCore_card c)).le_sylow_of_normal T

theorem H_sylow_card (T : Sylow 2 c.H) : Nat.card T = 64 := by
  have hd : Nat.card T ∣ 576 := by
    simpa only [H_card c] using (T : Subgroup c.H).card_subgroup_dvd_card
  have hl : 64 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card
    (show 2 ^ 6 ∣ Nat.card c.H by rw [H_card c]; decide)
  have hc : Nat.Coprime (Nat.card T) 9 := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 9).pow_left n
  have hu : Nat.card T ∣ 64 := hc.dvd_of_dvd_mul_right hd
  exact Nat.dvd_antisymm hu hl

theorem H_sylow_derived_center (T : Sylow 2 c.H) :
    (_root_.commutator T ⊓ center T).map (T : Subgroup c.H).subtype = c.H₁ ⊓ c.H₂ := by
  let Q := quaternionCore c
  let D := Q.subgroupOf (T : Subgroup c.H)
  let e : D ≃* Q := subgroupOfEquivOfLe (quaternionCore_le_sylow c T)
  let d := (quaternionCoreData c).map e.symm
  let : IsExtraspecial 2 D := d.extraspecial
  have hDcard : Nat.card D = 32 := (Nat.card_congr e.toEquiv).trans (quaternionCore_card c)
  have hi : D.index = 2 := by
    have h := D.card_mul_index
    rw [hDcard, H_sylow_card c T] at h
    omega
  let : IsCyclic (T ⧸ D) := isCyclic_of_prime_card hi
  have hline := derived_inf_center_eq_of_normal_extraspecial D
  rw [hline]
  apply eq_of_le_of_card_ge
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rw [← quaternionCore_center c]
    have hz' : e z ∈ center Q := (MulEquivClass.apply_mem_center_iff e).mpr hz
    exact mem_map_of_mem Q.subtype hz'
  · rw [card_map_of_injective (T : Subgroup c.H).subtype_injective,
      card_map_of_injective D.subtype_injective, IsExtraspecial.center_order_p 2 D,
      intersection_card c]

theorem exists_marked_involution :
    ∃ z : c.H, orderOf z = 2 ∧ zpowers z = c.H₁ ⊓ c.H₂ ∧
      c.H = centralizer ({(z : G)} : Set G) := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := (c.H₁ ⊓ c.H₂ : Subgroup c.H)) 2 (by rw [intersection_card c])
  have hzH : orderOf (z : c.H) = 2 := (orderOf_coe z).trans hz
  have hgen : zpowers (z : c.H) = c.H₁ ⊓ c.H₂ := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    rw [Nat.card_zpowers, hzH, intersection_card c]
  refine ⟨z, hzH, hgen, ?_⟩
  calc
    c.H = centralizer (((c.H₁ ⊓ c.H₂).map c.H.subtype : Subgroup G) : Set G) := c.centralizer
    _ = centralizer ({((z : c.H) : G)} : Set G) := by
      have he := congrArg (fun K : Subgroup c.H =>
        centralizer ((K.map c.H.subtype : Subgroup G) : Set G)) hgen.symm
      exact he.trans (by rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure]; rfl)

theorem H_sylow_normalizer_le (T : Sylow 2 c.H) :
    normalizer (((T : Subgroup c.H).map c.H.subtype : Subgroup G) : Set G) ≤ c.H := by
  obtain ⟨z, hz, hgen, hH⟩ := exists_marked_involution c
  have hline : (_root_.commutator T ⊓ center T).map (T : Subgroup c.H).subtype = zpowers z :=
    (H_sylow_derived_center c T).trans hgen.symm
  have himage := derived_center_line_map_of_injective (T : Subgroup c.H)
    c.H.subtype c.H.subtype_injective z hline
  exact (normalizer_le_centralizer_of_derived_center_line _ (z : G)
    ((orderOf_coe z).trans hz) himage).trans_eq hH.symm

theorem H_sylow_is_ambient (T : Sylow 2 c.H) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup c.H).map c.H.subtype := by
  let P := (T : Subgroup c.H).map c.H.subtype
  have hlocal : ¬ 2 ∣ P.relIndex c.H := by
    have he : P.subgroupOf c.H = (T : Subgroup c.H) := by
      exact comap_map_eq_self_of_injective c.H.subtype_injective _
    change ¬ 2 ∣ (P.subgroupOf c.H).index
    rw [he]
    exact T.not_dvd_index
  have hp : IsPGroup 2 P := T.isPGroup'.map c.H.subtype
  have hg := not_dvd_relIndex_of_normalizer_inf_le P c.H ⊤ hp le_top hlocal
    (inf_le_left.trans (H_sylow_normalizer_le c T))
  rw [relIndex_top_right] at hg
  exact ⟨hp.toSylow hg, rfl⟩

include c in
theorem ambient_sylow_card (S : Sylow 2 G) : Nat.card S = 64 := by
  let T : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := H_sylow_is_ambient c T
  have he : Nat.card S = Nat.card R := by
    rw [S.card_eq_multiplicity, R.card_eq_multiplicity]
  rw [he]
  change Nat.card (R : Subgroup G) = _
  rw [hR, card_map_of_injective c.H.subtype_injective, H_sylow_card c T]

theorem exists_fusion_in_H :
    ∃ (z : G) (t : G), orderOf z = 2 ∧ orderOf t = 2 ∧
      c.H = centralizer ({z} : Set G) ∧ t ∈ c.H ∧ t ≠ z ∧ IsConj z t := by
  obtain ⟨z, hz, hgen, hH⟩ := exists_marked_involution c
  let T : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨S, hS⟩ := H_sylow_is_ambient c T
  have hzcore : z ∈ quaternionCore c := by
    have hzline : z ∈ c.H₁ ⊓ c.H₂ := hgen ▸ mem_zpowers z
    rw [← quaternionCore_center c] at hzline
    exact map_subtype_le _ hzline
  have hzS : (z : G) ∈ (S : Subgroup G) := by
    rw [hS]
    exact mem_map_of_mem c.H.subtype (quaternionCore_le_sylow c T hzcore)
  have hzG : orderOf (z : G) = 2 := (orderOf_coe z).trans hz
  obtain ⟨g, hgS, hgne⟩ := distinguished_involution_fuses_in_sylow c z hzG hH S hzS
  refine ⟨z, g * z * g⁻¹, hzG, (MulAut.conj g).orderOf_eq z |>.trans hzG,
    hH, ?_, hgne, isConj_iff.mpr ⟨g, rfl⟩⟩
  rw [hS] at hgS
  exact map_subtype_le _ hgS

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
