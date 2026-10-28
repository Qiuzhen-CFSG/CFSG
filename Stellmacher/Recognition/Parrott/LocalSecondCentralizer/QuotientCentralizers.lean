module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Sylow
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.FixedRoot
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Abelian
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.NormalizerCentralization

/-!
# Centralizer containment in the literal second-transfer quotient

The local centralizer is Sylow in the full quotient centralizer. The elementary
and outside calculations make it abelian of order at most sixteen, and its
normalizer fixes the central four-group pointwise. Transfer and the odd-subgroup
obstruction therefore force every involution centralizer into the quotient Sylow.
The central-four case is supplied by the original centralizer calculation.

The final theorem applies this containment through the original inclusion,
proving C_G(v) ≤ N_G(F) without a global N₂ hypothesis or local callbacks.
The earlier conditional interfaces are retained.

Source: Parrott (1972), Lemma 8, printed p.683.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- Apply the small-abelian transfer theorem to the actual local centralizer.
Sylow status, placement, the central four-group, and the odd obstruction are
all proved; only the two stated local calculations remain. -/
public theorem quotient_centralizer_le_of_local_calculations
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) (hx2 : orderOf x = 2)
    (hxE : x ∉ t.quotientCoreCenter)
    (hab : IsMulCommutative (t.quotientLocalCentralizer x))
    (hcard : Nat.card (t.quotientLocalCentralizer x) ≤ 16)
    (hnorm : centralizer ({x} : Set t.Quotient) ⊓
        normalizer (t.quotientLocalCentralizer x : Set t.Quotient) ≤
      centralizer (t.quotientCoreCenter : Set t.Quotient)) :
    centralizer ({x} : Set t.Quotient) ≤ t.quotientSylow := by
  let C := centralizer ({x} : Set t.Quotient)
  let P := t.quotientCentralizerSylow h hx
  have hP : (P : Subgroup C).map C.subtype = t.quotientLocalCentralizer x :=
    t.quotientCentralizerSylow_image h hx
  have hPsub : (P : Subgroup C) = (t.quotientLocalCentralizer x).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (show t.quotientLocalCentralizer x ≤ C from
      inf_le_right)]
  let : IsMulCommutative (t.quotientLocalCentralizer x) := hab
  have hPc : IsMulCommutative P := by
    rw [hPsub]
    infer_instance
  have hPcard : Nat.card P ≤ 16 := by
    rw [← card_map_of_injective C.subtype_injective, hP]
    exact hcard
  have hEP : t.quotientCoreCenter ≤ (P : Subgroup C).map C.subtype := by
    rw [hP]
    exact t.quotientCoreCenter_le_localCentralizer hx
  have hEN : normalizer (P : Set C) ≤
      centralizer (t.quotientCoreCenter.subgroupOf C : Set C) := by
    intro a ha e he
    apply Subtype.ext
    have haP : (a : t.Quotient) ∈
        normalizer (t.quotientLocalCentralizer x : Set t.Quotient) := by
      rw [← hP]
      exact (P : Subgroup C).le_normalizer_map C.subtype
        (mem_map_of_mem C.subtype ha)
    exact hnorm ⟨a.property, haP⟩ e he
  exact n.second_transfer_small_abelian_quotient_centralizer h
    t.embedding t.embedding_injective t.embedding_range_le_centralizer
    t.S t.elementary_le_sylow_image t.v t.v_image
    (QuotientGroup.mk' (zpowers t.v)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) t.sylow_image_le_omega x hx2 hxE P hPc hPcard
    (by rw [hP]; exact inf_le_left) hEP hEN

/-- Assemble both involution cases, retaining exactly the two unproved local calculations. -/
public theorem quotient_involution_centralizers_of_local_calculations
    (h : ParrottCentralizerHypotheses z)
    (hsmall : ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      IsMulCommutative (t.quotientLocalCentralizer x) ∧
        Nat.card (t.quotientLocalCentralizer x) ≤ 16)
    (hnorm : ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      centralizer ({x} : Set t.Quotient) ⊓
          normalizer (t.quotientLocalCentralizer x : Set t.Quotient) ≤
        centralizer (t.quotientCoreCenter : Set t.Quotient)) :
    ∀ x ∈ t.quotientSylow, orderOf x = 2 →
      centralizer ({x} : Set t.Quotient) ≤ t.quotientSylow := by
  intro x hx hx2
  by_cases hxE : x ∈ t.quotientCoreCenter
  · exact t.quotientCoreCenter_centralizer_le h hxE (by
      intro he
      simp [he] at hx2)
  · obtain ⟨hab, hcard⟩ := hsmall x hx hx2 hxE
    exact t.quotient_centralizer_le_of_local_calculations h hx hx2 hxE hab hcard
      (hnorm x hx hx2 hxE)

/-- The literal ambient application. The two local source calculations must
still be discharged before this is a proof of the source containment theorem. -/
public theorem le_normalizer_of_local_quotient_calculations
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hsmall : ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      IsMulCommutative (t.quotientLocalCentralizer x) ∧
        Nat.card (t.quotientLocalCentralizer x) ≤ 16)
    (hnorm : ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      centralizer ({x} : Set t.Quotient) ⊓
          normalizer (t.quotientLocalCentralizer x : Set t.Quotient) ≤
        centralizer (t.quotientCoreCenter : Set t.Quotient)) :
    centralizer ({n.v} : Set G) ≤ normalizer (d.F : Set G) := by
  exact t.le_normalizer_of_quotient_centralizers h hlocal
    (t.quotient_involution_centralizers_of_local_calculations h hsmall hnorm)

/-- Every involution centralizer in the actual transfer quotient lies in its
specified Sylow subgroup. Both local calculations are discharged. -/
public theorem quotient_involution_centralizers
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    ∀ x ∈ t.quotientSylow, orderOf x = 2 →
      centralizer ({x} : Set t.Quotient) ≤ t.quotientSylow := by
  exact t.quotient_involution_centralizers_of_local_calculations h
    (t.quotientLocalCentralizer_small h hlocal)
    (t.quotient_involution_normalizer_centralization h)

include t in
/-- The two transfers and their quotient calculation put the full ambient
centralizer of the supplied v in the normalizer of the supplied F. -/
public theorem le_normalizer_of_local_inputs
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    centralizer ({n.v} : Set G) ≤ normalizer (d.F : Set G) := by
  exact t.le_normalizer_of_quotient_centralizers h hlocal
    (t.quotient_involution_centralizers h hlocal)

end Stellmacher.Recognition.ParrottSecondTransferData
