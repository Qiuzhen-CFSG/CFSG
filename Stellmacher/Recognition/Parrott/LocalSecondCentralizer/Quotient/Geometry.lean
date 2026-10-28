module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.TransferData
public import Stellmacher.Recognition.Parrott.SecondTransferQuotientCentralizers
public import Stellmacher.Recognition.Parrott.SecondTransferCoreCenterControl

/-!
# The central four-group in the literal transfer quotient

The image of Z(O₂(N_G(F))) in L/⟨v⟩ is a four-group centralizing the
specified Sylow image. Its nonidentity elements have centralizers contained
in that Sylow image. Every two-overgroup of this four-group has its normalizer
in the four-group normalizer, by the ambient fusion characterization.

These are applications to the original inclusion of L and its literal quotient
map; no new quotient or subgroup witnesses are chosen.

Source: Parrott (1972), Lemma 8, printed pp.682–683, observation (i).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- The actual central four-group, transported through the inclusion and quotient. -/
@[expose] public noncomputable def quotientCoreCenter : Subgroup t.Quotient :=
  (((center (pCore 2 (normalizer (d.F : Set G)))).map
    ((normalizer (d.F : Set G)).subtype.comp
      (pCore 2 (normalizer (d.F : Set G))).subtype)).comap t.embedding).map
    (QuotientGroup.mk' (zpowers t.v))

/-- The centralizer inside the supplied Sylow image, as a subgroup of L/⟨v⟩. -/
@[expose] public noncomputable def quotientLocalCentralizer (x : t.Quotient) :
    Subgroup t.Quotient :=
  t.quotientSylow ⊓ centralizer ({x} : Set t.Quotient)

public theorem sylow_image_le_omega :
    (t.S : Subgroup t.L).map t.embedding ≤
      (omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2)).map
        ((normalizer (d.F : Set G)).subtype.comp
          (pCore 2 (normalizer (d.F : Set G))).subtype) := by
  change (t.S : Subgroup t.L).map
    ((centralizer ({n.v} : Set G)).subtype.comp
      (t.M.subtype.comp t.L.subtype)) ≤ _
  rw [t.S_image]
  exact inf_le_left

public theorem sylow_image_omega :
    (omega₁ ((t.S : Subgroup t.L).map t.embedding) (p := 2)).map
      ((t.S : Subgroup t.L).map t.embedding).subtype = d.F := by
  have he := congrArg (fun A : Subgroup G => (omega₁ A (p := 2)).map A.subtype)
    t.S_image
  exact he.trans t.Y_omega

public theorem quotientCoreCenter_le_sylow :
    t.quotientCoreCenter ≤ t.quotientSylow := by
  apply map_mono
  intro x hx
  have hxF := n.omega_center_le_inf
    (n.core_center_le_omega_center hx)
  obtain ⟨s, hs, he⟩ := t.elementary_le_sylow_image hxF.2
  exact t.embedding_injective he ▸ hs

public theorem quotientCoreCenter_le_centralizer [Finite G] :
    t.quotientCoreCenter ≤ centralizer (t.quotientSylow : Set t.Quotient) := by
  obtain ⟨_, _, _, hES, _⟩ :=
    n.second_transfer_quotient_core_center_geometry t.embedding t.embedding_injective
      t.embedding_range_le_centralizer t.S t.elementary_le_sylow_image
      t.v t.v_image (QuotientGroup.mk' (zpowers t.v))
      (QuotientGroup.ker_mk' _) t.sylow_image_le_omega
  rintro _ ⟨e, he, rfl⟩ _ ⟨s, hs, rfl⟩
  simpa only [map_mul] using congrArg (QuotientGroup.mk' (zpowers t.v))
    (hES he s hs)

public theorem quotientCoreCenter_card [Finite G] :
    Nat.card t.quotientCoreCenter = 4 := by
  exact (n.second_transfer_quotient_core_center_geometry t.embedding t.embedding_injective
    t.embedding_range_le_centralizer t.S t.elementary_le_sylow_image
    t.v t.v_image (QuotientGroup.mk' (zpowers t.v))
    (QuotientGroup.ker_mk' _) t.sylow_image_le_omega).2.2.2.2

public theorem quotientCoreCenter_orderOf {x : t.Quotient}
    (hx : x ∈ t.quotientCoreCenter) (hx1 : x ≠ 1) : orderOf x = 2 := by
  obtain ⟨a, ha, rfl⟩ := hx
  have haF := n.omega_center_le_inf (n.core_center_le_omega_center ha)
  let : IsElementaryAbelian 2 d.F := d.elementary
  have ha2 : a ^ 2 = 1 := t.embedding_injective (by
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (t.embedding a) haF.2)
  exact orderOf_eq_prime (by rw [← map_pow, ha2, map_one]) hx1

/-- The already proved central-four case, on this exact quotient. -/
public theorem quotientCoreCenter_centralizer_le [Finite G]
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientCoreCenter) (hx1 : x ≠ 1) :
    centralizer ({x} : Set t.Quotient) ≤ t.quotientSylow := by
  obtain ⟨hker, hkp, _, hES, _⟩ :=
    n.second_transfer_quotient_core_center_geometry t.embedding t.embedding_injective
      t.embedding_range_le_centralizer t.S t.elementary_le_sylow_image
      t.v t.v_image (QuotientGroup.mk' (zpowers t.v))
      (QuotientGroup.ker_mk' _) t.sylow_image_le_omega
  exact n.second_transfer_central_four_quotient_centralizer h
    t.embedding t.embedding_injective t.embedding_range_le_centralizer t.S
    (QuotientGroup.mk' (zpowers t.v)) (QuotientGroup.mk'_surjective _)
    hker hkp hES x hx (t.quotientCoreCenter_orderOf hx hx1)

/-- Normalizer control is retained as normalization, without claiming centralization. -/
public theorem quotient_two_overgroup_normalizer [Finite G]
    (h : ParrottCentralizerHypotheses z)
    (R : Subgroup t.Quotient) (hR : IsPGroup 2 R)
    (hER : t.quotientCoreCenter ≤ R) :
    normalizer (R : Set t.Quotient) ≤
      normalizer (t.quotientCoreCenter : Set t.Quotient) := by
  have hker := (n.second_transfer_quotient_core_center_geometry
    t.embedding t.embedding_injective t.embedding_range_le_centralizer t.S
    t.elementary_le_sylow_image t.v t.v_image (QuotientGroup.mk' (zpowers t.v))
    (QuotientGroup.ker_mk' _) t.sylow_image_le_omega).2.1
  exact n.second_transfer_quotient_two_overgroup_normalizer h
    t.embedding t.embedding_injective t.S t.sylow_image_omega
    (QuotientGroup.mk' (zpowers t.v)) (QuotientGroup.mk'_surjective _)
    hker R hR hER

end Stellmacher.Recognition.ParrottSecondTransferData
