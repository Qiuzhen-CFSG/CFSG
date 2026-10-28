module

public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Theory.GroupTheory.FrattiniInvolutionObstruction
public import Theory.GroupAction.SubgroupQuotientOrbitIndex
public import Theory.GroupAction.FiveFourSixteenOrbits

/-!
# Parrott's five-coset involution selection

For an involution a outside D = J′, its orbit in the literal quotient
J/D consists of cosets with involutory lifts. This orbit cannot contain
four generating vectors together with their products with the first
vector. The obstruction follows from D = Φ(J) = Z₂(J) and the elementary
structure of D, by working modulo the center and using Frattini generation.

The finite orbit alternative then forces the orbit to have five elements.
The compatible conjugation action identifies this cardinality with the
centralizer index of aDH in H/DH, where DH is the image of D in H.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 4, printed p.675, and the quotient action on pp.673–674.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The faithful action on the actual core quotient has no generating
four-vector configuration inside an involution orbit with all off-diagonal
products with the first vector in that same orbit. -/
public theorem parrott_core_involution_orbit_obstruction
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    ∀ a : J, a ^ 2 = 1 → a ∉ D →
      ∃ f : (H ⧸ J) →* MulAut (J ⧸ D), Function.Injective f ∧
        (∀ (g : H) (b b' : J), (b' : H) = g * (b : H) * g⁻¹ →
          f (QuotientGroup.mk' J g) (QuotientGroup.mk' D b) = QuotientGroup.mk' D b') ∧
        ∀ v : Fin 4 → J ⧸ D, closure (Set.range v) = ⊤ →
          (∀ i, ∃ g, f g (QuotientGroup.mk' D a) = v i) →
          ∃ j, j ≠ 0 ∧ ¬ ∃ g, f g (QuotientGroup.mk' D a) = v 0 * v j := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  dsimp only
  intro a ha haD
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  refine ⟨f, hf, heval, ?_⟩
  intro v hgen hv
  have hlift (w : J ⧸ D) (hw : ∃ g, f g (QuotientGroup.mk' D a) = w) :
      ∃ b : J, b ^ 2 = 1 ∧ QuotientGroup.mk' D b = w := by
    obtain ⟨g, rfl⟩ := hw
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective J g
    let b : J := ⟨g * (a : H) * g⁻¹, (inferInstance : J.Normal).conj_mem a a.property g⟩
    refine ⟨b, ?_, (heval g a b rfl).symm⟩
    apply Subtype.ext
    change (g * (a : H) * g⁻¹) ^ 2 = 1
    have haH := congrArg (fun x : J => (x : H)) ha
    change (a : H) ^ 2 = 1 at haH
    simp only [pow_two] at haH ⊢
    calc
      _ = g * ((a : H) * a) * g⁻¹ := by group
      _ = 1 := by rw [haH]; group
  have hv0 : v 0 ≠ 1 := by
    obtain ⟨g, hg⟩ := hv 0
    rw [← hg]
    intro heq
    apply haD
    apply (QuotientGroup.eq_one_iff (N := D) a).mp
    exact (f g).injective (heq.trans (map_one (f g)).symm)
  obtain ⟨_, _, _, hPhi, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  obtain ⟨j, hj⟩ := exists_product_without_involutory_lift D hPhi hUpper v hgen
    (fun i => hlift (v i) (hv i)) 0 hv0
  refine ⟨j, ?_, fun hmem => hj (hlift _ hmem)⟩
  intro heq
  subst j
  obtain ⟨b, hb, hqb⟩ := hlift (v 0) (hv 0)
  apply hj
  refine ⟨1, one_pow 2, ?_⟩
  rw [map_one, ← hqb, ← map_mul, ← pow_two, hb, map_one]

/-- Parrott's fourth lemma: every involution in the core outside its
derived subgroup selects a coset with centralizer index five. -/
public theorem parrott_core_involution_coset_centralizer_index
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    ∀ a : H, a ∈ J → orderOf a = 2 → a ∉ DH →
      (centralizer ({QuotientGroup.mk' DH a} : Set (H ⧸ DH))).index = 5 := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  dsimp only
  intro a haJ ha2 haDH
  let b : J := ⟨a, haJ⟩
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    change a ^ 2 = 1
    rw [← ha2]
    exact pow_orderOf_eq_one a
  have hbD : b ∉ D := fun hb => haDH (mem_map_of_mem J.subtype hb)
  obtain ⟨f, hf, heval, hobstruction⟩ :=
    parrott_core_involution_orbit_obstruction z h b hb2 hbD
  obtain ⟨hElem, hcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 (J ⧸ D) := hElem
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let fM := f.comp e.symm.toMonoidHom
  have hfM : Function.Injective fM := hf.comp e.symm.injective
  have hbne : QuotientGroup.mk' D b ≠ 1 := fun hh =>
    hbD ((QuotientGroup.eq_one_iff (N := D) b).mp hh)
  have horbit : (Set.range (fun g => fM g (QuotientGroup.mk' D b))).ncard = 5 := by
    rcases Theory.GroupAction.five_four_sixteen_orbit_eq_five_or_generating_configuration
      hcard φ hφ fM hfM (QuotientGroup.mk' D b) hbne with hfive | ⟨v, hv, hmem, hprod⟩
    · exact hfive
    · obtain ⟨j, hj, hnot⟩ := hobstruction v hv (fun i => by
        obtain ⟨g, hg⟩ := hmem i
        exact ⟨e.symm g, hg⟩)
      obtain ⟨g, hg⟩ := hprod j hj
      exact False.elim (hnot ⟨e.symm g, hg⟩)
  have hrange : Set.range (fun g => fM g (QuotientGroup.mk' D b)) =
      Set.range (fun g => f g (QuotientGroup.mk' D b)) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e.symm g, rfl⟩
    · rintro ⟨g, rfl⟩
      refine ⟨e g, ?_⟩
      change f (e.symm (e g)) (QuotientGroup.mk' D b) = _
      rw [e.symm_apply_apply]
  rw [hrange] at horbit
  exact (centralizer_index_eq_subgroup_quotient_orbit_card J D f heval b).trans horbit

end Stellmacher.Recognition
