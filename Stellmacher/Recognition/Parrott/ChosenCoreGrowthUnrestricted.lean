module

public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaBounds
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaProper
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaDisplacement
public import Stellmacher.Recognition.Parrott.ChosenCoreCenterOrder
public import Stellmacher.Recognition.Parrott.ChosenNormalizerUnrestricted
public import Stellmacher.Recognition.Parrott.CoreOutsideDerivedOddAction
public import Theory.GroupTheory.SymmetricThreeQuotientInverter

/-!
# Unrestricted chosen-core fusion in Parrott's growth argument

The actual order-eight center automizer is S₃ without an ambient N₂
hypothesis. Its factor three excludes a small index of F in the chosen omega;
properness and the proved core geometry then supply the whole omega filtration.
The inverted three-subgroup contradiction excludes fusion of the chosen core
involution under self-normalization. Every subgroup remains the supplied one.

Source: Parrott (1972), Lemma 5, printed p.676.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/- The order and index calculations use the actual unrestricted S₃ automizer. -/
public theorem chosen_omega_normalizer_card_three_dvd_unrestricted
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (_hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    3 ∣ Nat.card (normalizer
      (((omega₁ S (p := 2)).map S.subtype : Subgroup G) : Set G)) := by
  intro S
  let N := normalizer (S : Set G)
  obtain ⟨e⟩ :=
    chosen_centralizer_normalizer_quotient_unrestricted d h hderived hconj hcenter
  have hc : Nat.card (N ⧸ S.subgroupOf N) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdiv : 3 ∣ Nat.card N := by
    have hd : Nat.card (N ⧸ S.subgroupOf N) ∣ Nat.card N :=
      (S.subgroupOf N).index_dvd_card
    rw [hc] at hd
    exact (by decide : 3 ∣ 6).trans hd
  exact hdiv.trans (card_dvd_of_le d.chosen_normalizer_le_omega_normalizer)

/- The order and index calculations use the actual unrestricted S₃ automizer. -/
public theorem chosen_omega_fixed_join_relIndex_ge_four_unrestricted
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let U := (omega₁ S (p := 2)).map S.subtype
    4 ≤ d.F.relIndex U ∧ 128 ≤ Nat.card (omega₁ S (p := 2)) := by
  intro S U
  have hFU : d.F ≤ U := d.fixed_join_le_chosen_omega
  have hUS : U ≤ S := map_subtype_le _
  have hneone : d.F.relIndex U ≠ 1 := by
    intro hi
    have heq : U = d.F := le_antisymm (relIndex_eq_one.mp hi) hFU
    apply d.chosen_centralizer_normalizer_not_le_fixed_join_normalizer h hself hconj
    have hh := d.chosen_normalizer_le_omega_normalizer
    change normalizer (S : Set G) ≤ normalizer (U : Set G) at hh
    rwa [heq] at hh
  have hnetwo : d.F.relIndex U ≠ 2 := by
    apply relIndex_ne_two_of_three_dvd_normalizer d.F U d.elementary hFU
      d.centralizer_eq.le
    · rw [hself]
      exact d.sylow.isPGroup'
    · exact chosen_omega_normalizer_card_three_dvd_unrestricted d h hself hderived hconj hcenter
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) d.F U bot_le hFU
  rw [relIndex_bot_left, relIndex_bot_left, d.card] at hc
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hd : Nat.card U ∣ 2048 := by
    have hh := card_dvd_of_le (hUS.trans (d.chosen_centralizer_le_sylow h))
    rwa [d.sylow_card h] at hh
  have hnethree : d.F.relIndex U ≠ 3 := by
    intro hi
    have hu : Nat.card U = 96 := by omega
    rw [hu] at hd
    norm_num at hd
  have hge : 4 ≤ d.F.relIndex U := by omega
  refine ⟨hge, ?_⟩
  have hmap : Nat.card U = Nat.card (omega₁ S (p := 2)) :=
    card_map_of_injective S.subtype_injective
  omega

/- The order and index calculations use the actual unrestricted S₃ automizer. -/
public theorem chosen_omega_geometry_of_ne_top_unrestricted
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V ≠ ⊤ → V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧ K.relIndex S = 4 ∧
      Nat.card (K ⊓ S : Subgroup G) = 64 := by
  intro H K S V hproper
  have hlarge := (chosen_omega_fixed_join_relIndex_ge_four_unrestricted
    d h hself hderived hconj hcenter).2
  change 128 ≤ Nat.card V at hlarge
  have hsmall := (d.chosen_centralizer_card_bounds h).2
  change Nat.card S ≤ 256 at hsmall
  have hc := V.card_mul_index
  have hneone : V.index ≠ 1 := fun hi => hproper (index_eq_one.mp hi)
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hi : 2 ≤ V.index := by
    have hnezero : V.index ≠ 0 := by intro hh; rw [hh, mul_zero] at hc; omega
    omega
  have htwice : Nat.card V * 2 ≤ Nat.card S :=
    (Nat.mul_le_mul_left (Nat.card V) hi).trans_eq hc
  have hV : Nat.card V = 128 := by omega
  have hS : Nat.card S = 256 := by omega
  have hindex : V.index = 2 := by rw [hV, hS] at hc; omega
  have hFU : d.F ≤ V.map S.subtype := d.fixed_join_le_chosen_omega
  have hFindex : d.F.relIndex (V.map S.subtype) = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) d.F (V.map S.subtype) bot_le hFU
    rw [relIndex_bot_left, relIndex_bot_left, d.card,
      card_map_of_injective S.subtype_injective, hV] at hh
    omega
  have hKindex : K.relIndex S = 4 := by
    rcases d.chosen_core_relIndex_cases h with ht | ht
    · have hh := (d.chosen_card_of_core_relIndex_two h ht).2
      change Nat.card S = 128 at hh
      omega
    · exact ht
  have hKcard : Nat.card (K ⊓ S : Subgroup G) = 64 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ S) S bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, hKindex, hS] at hh
    omega
  exact ⟨hindex, hS, hV, hFindex, hKindex, hKcard⟩

/-- The chosen omega filtration uses only the literal normalizer equality and
local derived weak closure; no ambient N₂ or solvability premise is needed. -/
public theorem chosen_omega_filtration_unrestricted
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G)) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧
      ∀ (w : G) (_hw : w ∈ E), w ∉ d.F →
        ∃ hwN : w ∈ normalizer (S : Set G),
          ∀ v ∈ V, v⁻¹ * S.normalizerMonoidHom ⟨w, hwN⟩ v ∈ commutator S := by
  let H := centralizer ({z} : Set G)
  let K := (pCore 2 H).map H.subtype
  let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  let V := omega₁ S (p := 2)
  have hcenter := d.chosen_center_card_eight h hconj hderived
  have hproper := d.chosen_omega_ne_top_of_core_involutions h hconj hderived
    (d.chosen_core_centralizer_involutions_mem_fixed_join_of_relIndex_two h)
  obtain ⟨hi, hS, hV, hF, hKindex, hKcard⟩ :=
    d.chosen_omega_geometry_of_ne_top_unrestricted h hself hderived hconj hcenter hproper
  refine ⟨hi, hS, hV, hF, ?_⟩
  intro w hw _hwF
  refine ⟨d.chosen_derived_mem_normalizer h w hw, ?_⟩
  exact (d.chosen_omega_displacement_iff_square_one h w hw).mpr
    (d.chosen_square_one_displacement_of_core_geometry h hKcard hKindex w hw)

end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition

/-- Derived weak closure and self-normalization exclude fusion of the supplied
core involution, using the unrestricted chosen-center action. -/
public theorem parrott_not_isConj_second_involution_of_normalizer_eq_unrestricted
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    ¬ IsConj z (d.a : G) := by
  intro hconj
  let H := centralizer ({z} : Set G)
  let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  let N := normalizer (S : Set G)
  let V := omega₁ S (p := 2)
  let : V.Characteristic := omega₁_characteristic S
  have hzS : z ∈ S := d.le_chosen_centralizer d.z_mem_inf.2
  have hS : IsPGroup 2 S := d.chosen_centralizer_isPGroup h
  have hequiv : Nonempty ((N ⧸ S.subgroupOf N) ≃* Equiv.Perm (Fin 3)) :=
    d.chosen_centralizer_normalizer_quotient_unrestricted h hderived hconj
      (d.chosen_center_card_eight h hconj hderived)
  obtain ⟨hindex, _, _, _, hdisplacement⟩ :=
    d.chosen_omega_filtration_unrestricted h hself hderived hconj
  obtain ⟨w, hwE, hwF, hw2, _, _⟩ :=
    d.chosen_centralizer_exists_center_moving_involution h
  obtain ⟨hwN, hwdisplacement⟩ := hdisplacement w hwE hwF
  let wN : N := ⟨w, hwN⟩
  have hwN2 : orderOf wN = 2 :=
    (orderOf_injective N.subtype N.subtype_injective wN).symm.trans hw2
  have hwNS : wN ∉ S.subgroupOf N := by
    intro hwS
    have hwEF : w ∈ E ⊓ d.F := d.inf_eq.symm ▸ ⟨hwE, hwS.2⟩
    exact hwF hwEF.2
  obtain ⟨Q, hQcard, hinverts⟩ :=
    exists_inverted_three_of_symmetric_three_quotient (S.subgroupOf N)
      hS.comap_subtype hequiv wN hwN2 hwNS
  have hQcardG : Nat.card (Q.map N.subtype) = 3 :=
    (card_map_of_injective N.subtype_injective).trans hQcard
  apply parrott_no_inverted_three_filtration z h S (Q.map N.subtype) hzS hS
    V hindex (map_subtype_le Q) hQcardG wN ?_ hwdisplacement
  rintro q ⟨q, hq, rfl⟩
  exact congrArg N.subtype (hinverts q hq)

end Stellmacher.Recognition
