module

public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterTransport
public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterSelection
public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterCardBound
public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterOmegaExclusion

/-!
# Assembly of the fixed-join witness for the second centralizer

The selection module constructs an involution in P outside omega which
inverts the supplied three-subgroup. Its original-core fixed join is
contained in its V-centralizer and has order 32. A centralizer upper bound
therefore identifies the two subgroups. The final assembly discharges this
bound and the omega-center exclusion using the original-core centralizer
calculation and the lower bound for centralizers in the compatible omega
subgroup. The conditional assembly remains available as a separate interface.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678 and §4, p.682.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A centralizer upper bound identifies the compatible fixed join, retaining
its chosen involution, conjugator, and proper normalizer position. -/
public theorem normalizer_fixed_join_of_centralizer_card_le
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    ∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ 32 →
      ∃ e : ParrottSecondElementaryData z, (e.a : G) = w ∧
        e.F = V ⊓ centralizer ({w} : Set G) ∧
        (∃ a : H, d.F.map (MulAut.conj (a : G)).toMonoidHom = e.F) ∧
        v ∈ E ⊓ e.F ∧ (e.sylow : Subgroup G) < normalizer (e.F : Set G) := by
  intro N K W V P H E w hw hw2 hwW hcard
  obtain ⟨e, hea, hconj, heV, hvE, heproper⟩ :=
    d.normalizer_fixed_outside_omega_fixed_join h hN hproper Q v hv hfix w hw hw2 hwW
  have hwF : w ∈ e.F := by
    rw [← hea, e.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  have hle : e.F ≤ V ⊓ centralizer ({w} : Set G) := by
    let : IsElementaryAbelian 2 e.F := e.elementary
    intro x hx
    exact ⟨heV hx, mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx hwF)⟩
  have heq : e.F = V ⊓ centralizer ({w} : Set G) :=
    eq_of_le_of_card_ge hle (e.card.symm ▸ hcard)
  exact ⟨e, hea, heq, hconj, hvE, heproper⟩

/-- The selected inverter and the two local centralizer calculations give
the exact fixed-join witness needed by the outer-geometry assembly. -/
public theorem normalizer_fixed_join_witness_of_local_calculations
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let A := (Q : Subgroup N).map N.subtype
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    (∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      (∀ a ∈ A, w * a * w⁻¹ = a⁻¹) →
      Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ 32) →
    (∀ (w : G) (e : ParrottSecondElementaryData z),
      w ∈ P → orderOf w = 2 → w ∉ W →
      (∀ a ∈ A, w * a * w⁻¹ = a⁻¹) →
      (e.a : G) = w → e.F = V ⊓ centralizer ({w} : Set G) →
      v ∈ E ⊓ e.F → (e.sylow : Subgroup G) < normalizer (e.F : Set G) →
      let M := normalizer (e.F : Set G)
      let Kₑ := pCore 2 M
      let Uₑ := omega₁ Kₑ (p := 2)
      v ∉ (center Uₑ).map ((M.subtype.comp Kₑ.subtype).comp Uₑ.subtype)) →
    ∃ (w : G) (e : ParrottSecondElementaryData z),
      w ∈ P ∧ orderOf w = 2 ∧ w ∉ W ∧
      e.F = V ⊓ centralizer ({w} : Set G) ∧
      let M := normalizer (e.F : Set G)
      let Kₑ := pCore 2 M
      let Uₑ := omega₁ Kₑ (p := 2)
      v ∉ (center Uₑ).map ((M.subtype.comp Kₑ.subtype).comp Uₑ.subtype) := by
  intro N K W A V P H E hcard hexclude
  obtain ⟨w, hw, hw2, hwW, hinv⟩ :=
    d.exists_normalizer_fixed_outer_involution_inverting_three h hN hproper Q v hv hfix
  obtain ⟨e, hea, heF, _, hve, heproper⟩ :=
    d.normalizer_fixed_join_of_centralizer_card_le h hN hproper Q v hv hfix
      w hw hw2 hwW (hcard w hw hw2 hwW hinv)
  exact ⟨w, e, hw, hw2, hwW, heF,
    hexclude w e hw hw2 hwW hinv hea heF hve heproper⟩

/-- There is an involution outside omega whose centralizer in V is a
compatible fixed join, with the prescribed fixed point outside that join's
omega center. This supplies the witness for the outer-geometry assembly. -/
public theorem normalizer_fixed_join_witness
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    ∃ (w : G) (e : ParrottSecondElementaryData z),
      w ∈ P ∧ orderOf w = 2 ∧ w ∉ W ∧
      e.F = V ⊓ centralizer ({w} : Set G) ∧
      let M := normalizer (e.F : Set G)
      let Kₑ := pCore 2 M
      let Uₑ := omega₁ Kₑ (p := 2)
      v ∉ (center Uₑ).map ((M.subtype.comp Kₑ.subtype).comp Uₑ.subtype) := by
  apply d.normalizer_fixed_join_witness_of_local_calculations h hN hproper Q v hv hfix
  · exact d.normalizer_fixed_inverter_centralizer_card_le h hN hproper Q v hv hfix
  · intro w e _ _ _ _ hea heF _ heproper
    exact d.normalizer_fixed_join_outside_omega_center h hN hproper Q v hv hfix
      w e hea heF heproper

end Stellmacher.Recognition.ParrottSecondElementaryData
