module

public import Stellmacher.Recognition.Parrott.DerivedVHyperplane
public import Stellmacher.Recognition.Parrott.DerivedVDisplacement
public import Stellmacher.Recognition.Parrott.DerivedVNoninvariance
public import Theory.GroupAction.FiveFourSquareFixed
public import Theory.GroupAction.SubgroupQuotientOrbitIndex

/-!
# Assembling the derived quotient-line calculation

The image U of C_J(v) in J/J′ is a binary hyperplane. Once the image
of V′ is identified with its square displacement under an order-four
element of H/J, noninvariance of U gives a line. The faithful five-four
action excludes orbit size five for its nonidentity element; the
conjugation action then gives the literal centralizer-index conclusion.

The first theorem isolates this assembly from the two group-theoretic
inputs: noninvariance and identification of the derived image. The final
theorem supplies both inputs for the actual local centralizer, using only
its order and the position of v in the derived core.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the first paragraph of p.677.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- Transport the square-displacement line to the actual derived subgroup
and the centralizer index in H/J′. -/
public theorem parrott_derived_quotient_line_of_square_displacement
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    ∀ v : G, v ∈ E → v ∉ zpowers z →
      ∀ V : Subgroup G,
      let D := (commutator V).map V.subtype
      let K := D.comap i
      let DH := (commutator J).map J.subtype
      let q := QuotientGroup.mk' (commutator J)
      let U := ((centralizer ({v} : Set G)).comap i).map q
      ∀ f : (H ⧸ J) →* MulAut (J ⧸ commutator J), Function.Injective f →
        (∀ (a : H) (b b' : J), (b' : H) = a * (b : H) * a⁻¹ →
          f (QuotientGroup.mk' J a) (q b) = q b') →
        ∀ g : H ⧸ J, orderOf g = 4 →
          (∀ u ∈ U, f g (f g u) ∈ U) →
          (∃ u ∈ U, f g u ∉ U) →
          (∀ s : (J ⧸ commutator J) →* (J ⧸ commutator J),
            (∀ w, s w = f g (f g w) * w) → K.map q = U.map s) →
          Nat.card (K.map q) = 2 ∧
            ∀ b : J, i b ∈ D → b ∉ commutator J →
              (centralizer ({QuotientGroup.mk' DH (b : H)} : Set (H ⧸ DH))).index ≠ 5 := by
  intro H J i E v hv hvz V D K DH q U f hf heval g hg hU2 hUnot hderived
  obtain ⟨hElem, hW⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 (J ⧸ commutator J) := hElem
  have hU : Nat.card U = 8 :=
    (parrott_derived_core_centralizer_hyperplane z h v hv hvz).2.2
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let fM := f.comp e.symm.toMonoidHom
  have hfM : Function.Injective fM := hf.comp e.symm.injective
  have hgM : orderOf (e g) = 4 :=
    (orderOf_injective e.toMonoidHom e.injective g).trans hg
  have hevalM (w : J ⧸ commutator J) : fM (e g) w = f g w := by
    change f (e.symm (e g)) w = f g w
    rw [e.symm_apply_apply]
  obtain ⟨s, hs, hline, horbit⟩ := Theory.GroupAction.five_four_square_displacement_line
    hW φ hφ fM hfM (e g) hgM U hU
    (by simpa only [hevalM] using hU2) (by simpa only [hevalM] using hUnot)
  have himage : K.map q = U.map s := hderived s (by simpa only [hevalM] using hs)
  refine ⟨himage.symm ▸ hline, ?_⟩
  intro b hb hbD
  have hqb : q b ∈ U.map s := himage ▸ mem_map_of_mem q hb
  have hqbne : q b ≠ 1 := fun hh => hbD ((QuotientGroup.eq_one_iff b).mp hh)
  have hnot := horbit (q b) hqb hqbne
  have hrange : Set.range (fun k => fM k (q b)) = Set.range (fun k => f k (q b)) := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e.symm k, rfl⟩
    · rintro ⟨k, rfl⟩
      refine ⟨e k, ?_⟩
      change f (e.symm (e k)) (q b) = _
      rw [e.symm_apply_apply]
  rw [hrange] at hnot
  rw [centralizer_index_eq_subgroup_quotient_orbit_card J (commutator J) f heval b]
  exact hnot

/-- The actual derived subgroup of the order-512 local centralizer has a
quotient image of order two, and its nonidentity coset has centralizer index
different from five. No additional Sylow or center geometry is required. -/
public theorem parrott_derived_quotient_line
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    ∀ v : G, v ∈ E → v ∉ zpowers z →
      ∀ V : Subgroup G, H ⊓ centralizer ({v} : Set G) = V →
        Nat.card V = 512 →
        let D := (commutator V).map V.subtype
        let K := D.comap i
        let DH := (commutator J).map J.subtype
        Nat.card (K.map (QuotientGroup.mk' (commutator J))) = 2 ∧
          ∀ b : J, i b ∈ D → b ∉ commutator J →
            (centralizer ({QuotientGroup.mk' DH (b : H)} : Set (H ⧸ DH))).index ≠ 5 := by
  intro H J i E v hv hvz V hV hcard D K DH
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨g, hg, hstable, hderived⟩ :=
    parrott_derived_image_eq_square_displacement z h v hv hvz V hV hcard f hf heval
  have hnoninv := parrott_derived_core_centralizer_hyperplane_noninvariant
    z h v hv hvz V hV hcard f hf heval g hg
  exact parrott_derived_quotient_line_of_square_displacement
    z h v hv hvz V f hf heval g hg hstable hnoninv hderived

end Stellmacher.Recognition
