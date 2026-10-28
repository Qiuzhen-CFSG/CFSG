module

public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaBounds
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaLocal
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaProper
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaDisplacement

/-!
# Assembly of the chosen omega filtration from the center order

For the supplied second elementary data, assume the center of
`S = C_G(z) ∩ C_G(a)` has order eight. The S₃ normalizer quotient rules out
index one or two for F in Ω₁(S). Properness of omega then forces index two
in S and the orders 256 and 128. The inverter calculation can be made on
square-one generators; it extends to all of omega in the abelianization.

The conditional assembly separates those two local calculations, and the
final theorem discharges both using properness and generator displacement.
Thus the center-order hypothesis alone supplies the full filtration. The
chosen w, F, and Sylow are retained throughout, and S′ is never assumed to
be fixed pointwise.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.676, from “As 3 divides” through the inverter displacement calculation.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Assemble the actual omega filtration once properness and the square-one
displacement calculation have been established. The displacement premise
may use the index supplied by the independent properness argument. -/
public theorem chosen_omega_filtration_of_local_calculations [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V ≠ ⊤ →
    (V.index = 2 → ∀ (w : G) (hw : w ∈ E), w ∉ d.F →
      ∀ v : S, v ^ 2 = 1 → v⁻¹ * S.normalizerMonoidHom
        ⟨w, d.chosen_derived_mem_normalizer h w hw⟩ v ∈ commutator S) →
    V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧
      ∀ (w : G) (_hw : w ∈ E), w ∉ d.F →
        ∃ hwN : w ∈ normalizer (S : Set G),
          ∀ v ∈ V, v⁻¹ * S.normalizerMonoidHom ⟨w, hwN⟩ v ∈ commutator S := by
  intro H E S V hproper hsquares
  obtain ⟨hi, hS, hV, hF, _, _⟩ :=
    chosen_omega_geometry_of_ne_top hns hN d h hself hderived hconj hcenter hproper
  refine ⟨hi, hS, hV, hF, ?_⟩
  intro w hw hwF
  refine ⟨d.chosen_derived_mem_normalizer h w hw, ?_⟩
  exact (d.chosen_omega_displacement_iff_square_one h w hw).mpr
    (hsquares hi w hw hwF)

/-- The center of order eight forces the actual chosen omega filtration and
the displacement inclusion for every supplied derived-core element outside F.
No properness, index, or commutator calculation remains as an extra premise. -/
public theorem chosen_omega_filtration_of_center_card_eight [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧
      ∀ (w : G) (_hw : w ∈ E), w ∉ d.F →
        ∃ hwN : w ∈ normalizer (S : Set G),
          ∀ v ∈ V, v⁻¹ * S.normalizerMonoidHom ⟨w, hwN⟩ v ∈ commutator S := by
  exact chosen_omega_filtration_of_local_calculations hns hN d h hself hderived hconj
    hcenter (chosen_omega_ne_top_of_center_card_eight hns hN d h hself hderived hconj
      hcenter) (chosen_square_one_displacement_of_omega_index_two
        hns hN d h hself hderived hconj hcenter)

end Stellmacher.Recognition.ParrottSecondElementaryData
