module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Geometry
public import Theory.GroupTheory.NormalizerControlledCentralizerSylow

/-!
# Sylow centralizers in the literal second-transfer quotient

For x in the supplied quotient Sylow, its local centralizer contains the
central four-group. Every nonidentity element of that four-group has full
centralizer inside the supplied Sylow. Together with normalizer control,
this promotes the local centralizer to Sylow in the full centralizer of x.

This promotion uses neither the small abelian calculation nor pointwise
centralization by the normalizer. It supplies the actual Sylow and its
placement needed by the subsequent transfer argument.

Source: Parrott (1972), Lemma 8, printed p.683, observations (i)–(ii).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

omit [Finite G] in
public theorem quotientLocalCentralizer_isTwoGroup (x : t.Quotient) :
    IsPGroup 2 (t.quotientLocalCentralizer x) := by
  have hp := t.S.isPGroup'.map (QuotientGroup.mk' (zpowers t.v))
  exact hp.of_injective
    (inclusion (show t.quotientLocalCentralizer x ≤ t.quotientSylow from inf_le_left))
    (inclusion_injective _)

public theorem quotientCoreCenter_le_localCentralizer {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) :
    t.quotientCoreCenter ≤ t.quotientLocalCentralizer x := by
  intro e he
  exact ⟨t.quotientCoreCenter_le_sylow he, mem_centralizer_singleton_iff.mpr
    ((t.quotientCoreCenter_le_centralizer he) x hx).symm⟩

/-- The local centralizer is the image of a Sylow of the full centralizer. -/
public theorem exists_quotientCentralizerSylow
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) :
    ∃ P : Sylow 2 (centralizer ({x} : Set t.Quotient)),
      (P : Subgroup (centralizer ({x} : Set t.Quotient))).map
        (centralizer ({x} : Set t.Quotient)).subtype =
          t.quotientLocalCentralizer x := by
  have hEP := t.quotientCoreCenter_le_localCentralizer hx
  have hE : t.quotientCoreCenter ≠ ⊥ := by
    intro he
    have hc := t.quotientCoreCenter_card
    rw [he, card_bot] at hc
    omega
  apply exists_sylow_of_normalizer_control_and_centralizers
    (centralizer ({x} : Set t.Quotient)) (t.quotientLocalCentralizer x)
    t.quotientCoreCenter (t.quotientLocalCentralizer_isTwoGroup x)
    inf_le_right hEP hE
    (t.quotient_two_overgroup_normalizer h _
      (t.quotientLocalCentralizer_isTwoGroup x) hEP)
  intro e he he1 a ha
  exact ⟨t.quotientCoreCenter_centralizer_le h he he1 ha.2, ha.1⟩

/-- The Sylow used in the quotient transfer argument; its image is specified below. -/
public noncomputable def quotientCentralizerSylow
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) : Sylow 2 (centralizer ({x} : Set t.Quotient)) :=
  (t.exists_quotientCentralizerSylow h hx).choose

public theorem quotientCentralizerSylow_image
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) :
    (t.quotientCentralizerSylow h hx : Subgroup (centralizer ({x} : Set t.Quotient))).map
      (centralizer ({x} : Set t.Quotient)).subtype = t.quotientLocalCentralizer x :=
  (t.exists_quotientCentralizerSylow h hx).choose_spec

end Stellmacher.Recognition.ParrottSecondTransferData
