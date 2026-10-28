module

public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
public import Theory.GroupTheory.TwoLocalCharacteristicControl

/-!
# The source seed commutator and its fixed line

The natural invariant pairing identifies fixation of V₁ with displacement
inside V₃, and displacement inside V₁ with fixation of V₃. Thus [V,O₂(H)]
is an L₁T-invariant subgroup between V₁ and V₃. F.9 irreducibility and the
earlier noncentrality of V₃ rule out V₁ and force equality with V₃. The
same irreducibility gives C_V₃(O₂(H))=V₁, and the central commutator bound
gives both [V₃,O₂(H)]=V₁ and [U_H,O₂(H)]=V₁.

The common Sylow subgroup transports the original13.5.4(5) noncentrality
from O₂(G₁) to O₂(H). Full source F.9 applicability and that earlier
noncentrality remain with the Section13.5 assembly; no desired commutator
or fixed-space conclusion is assumed. Source: Aschbacher–Smith13.7.3(6),p.936.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
open NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

include d

private theorem commutator_image (A : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (a : A) (v : V) :
    ∃ c : V, c.val = ⁅a.val, v.val⁆ ∧
      (d.coordinate c).toAdd = naturalRepresentation (Fin 6)
        (permutation d ⟨a.val, hA a.property⟩) (d.coordinate v).toAdd - (d.coordinate v).toAdd := by
  let c := V.normalizerMonoidHom ⟨a.val, d.normalizes_V (hA a.property)⟩ v * v⁻¹
  refine ⟨c, rfl, ?_⟩
  change (d.coordinate (V.normalizerMonoidHom _ v * v⁻¹)).toAdd = _
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg,
    NaturalAction.conjugation d ⟨a.val, hA a.property⟩ v]

/-- Centralizing the actual point puts every displacement in the actual seed. -/
theorem commutator_le_seed_of_centralizes_line (A : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hc : A ≤ centralizer (V₁ : Set G)) :
    ⁅V, A⁆ ≤ V₃ := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha v hv
  let g : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨a, hA ha⟩
  have hf : ∀ x ∈ image d V₁, naturalRepresentation (Fin 6) (permutation d g) x = x := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_image d V₁ x).mp hx
    rw [← NaturalAction.conjugation d g u]
    apply congrArg (fun b : V => (d.coordinate b).toAdd)
    apply Subtype.ext
    change a * u.val * a⁻¹ = u.val
    rw [← mem_centralizer_iff.mp (hc ha) u.val hu, mul_inv_cancel_right]
  obtain ⟨c, he, hcoord⟩ := commutator_image d A hA ⟨a, ha⟩ ⟨v, hv⟩
  have hh := (fixes_iff_displacement (permutation d g) (image d V₁)).mp hf
    (d.coordinate ⟨v, hv⟩).toAdd
  rw [← seed_perpendicular d, ← hcoord] at hh
  obtain ⟨u, hu, hu'⟩ := (mem_image d V₃ _).mp hh
  have huc : u = c := d.coordinate.injective hu'
  have hc3 : c.val ∈ V₃ := huc ▸ hu
  rwa [he] at hc3

/-- Displacement in the actual point forces fixation of its perpendicular seed. -/
theorem centralizes_seed_of_commutator_le_line (A : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hc : ⁅V, A⁆ ≤ V₁) :
    A ≤ centralizer (V₃ : Set G) := by
  rw [commutator_comm] at hc
  intro a ha
  let g : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨a, hA ha⟩
  have hd : ∀ w, naturalRepresentation (Fin 6) (permutation d g) w - w ∈
      form.orthogonal (image d V₃) := by
    intro w
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have hv' : (d.coordinate v).toAdd = w := hv
    obtain ⟨c, he, hcoord⟩ := commutator_image d A hA ⟨a, ha⟩ v
    rw [seed_perpendicular d, LinearMap.BilinForm.orthogonal_orthogonal
      form_nondegenerate form_alt.isRefl]
    apply (mem_image d V₁ _).mpr
    refine ⟨c, ?_, ?_⟩
    · rw [he]
      exact hc (commutator_mem_commutator ha v.property)
    · simpa only [hv'] using hcoord
  have hf := (fixes_iff_displacement (permutation d g) (image d V₃)).mpr hd
  apply mem_centralizer_iff.mpr
  intro v hv
  let vV : V := ⟨v, d.seed_le hv⟩
  have hh := hf (d.coordinate vV).toAdd ((mem_image d V₃ _).mpr ⟨vV, hv, rfl⟩)
  rw [← NaturalAction.conjugation d g vV] at hh
  have he := congrArg Subtype.val (d.coordinate.injective hh)
  change a * v * a⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

variable {H : Subgroup G}

/-- The exact seed equality in13.7.3(6), forced by the natural pairing,
F9 irreducibility and the earlier noncentrality of V₃ on O₂(H). -/
theorem commutator_V_QH_eq_seed
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hne : ⁅V₃, Section08.Source.QH H⁆ ≠ ⊥) :
    ⁅V, Section08.Source.QH H⁆ = V₃ := by
  let D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hQX : D.QH ≤ L ⊔ (T : Subgroup G) := h.QH_le_T.trans le_sup_right
  have hW : ⁅V, D.QH⁆ ≤ V₃ := commutator_le_seed_of_centralizes_line d D.QH hQX
    ((pCoreIn_le 2 H).trans h.H_centralizes)
  have hcseed : ⁅V₃, D.QH⁆ ≤ V₁ :=
    (commutator_mono (le_conjugateSpanBy V₃ H) le_rfl).trans h.commutator_UH_QH_le_point
  have hEq : ⁅V₃, D.QH⁆ = V₁ := by
    have hd : Nat.card (⁅V₃, D.QH⁆ : Subgroup G) ∣ 2 := d.line_card ▸ card_dvd_of_le hcseed
    have hs : Nat.card (⁅V₃, D.QH⁆ : Subgroup G) = 2 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with ho | ho
      · exact (hne (eq_bot_of_card_eq _ ho)).elim
      · exact ho
    exact eq_of_le_of_card_ge hcseed (by rw [d.line_card, hs])
  have hpW : V₁ ≤ ⁅V, D.QH⁆ := hEq.symm.le.trans (commutator_mono d.seed_le le_rfl)
  have hstable : D.L₁ ⊔ (T : Subgroup G) ≤ normalizer (⁅V, D.QH⁆ : Subgroup G) := by
    intro x hx
    have hv : x ∈ normalizer (V : Set G) :=
      (sup_le ((map_subtype_le _).trans (inf_le_left.trans le_sup_left)) le_sup_right).trans
        d.normalizes_V hx
    have hq : x ∈ normalizer (D.QH : Set G) :=
      ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (h.local_le hx)
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp hv, mem_normalizer_iff_map_conj_eq.mp hq]
  rcases h.irreducible ⁅V, D.QH⁆ hpW hW hstable with he | he
  · have hf := centralizes_seed_of_commutator_le_line d D.QH hQX he.le
    exact (hne (commutator_comm V₃ D.QH ▸ commutator_eq_bot_iff_le_centralizer.mpr hf)).elim
  · exact he

/-- The actual fixed subgroup of the seed under O₂(H) is precisely V₁. -/
theorem seed_centralizer_eq_line
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hne : ⁅V₃, Section08.Source.QH H⁆ ≠ ⊥) :
    V₃ ⊓ centralizer (Section08.Source.QH H : Set G) = V₁ := by
  let D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hp : V₁ ≤ V₃ ⊓ centralizer (D.QH : Set G) := by
    refine le_inf (d.line_le_plane.trans d.plane_le_seed) ?_
    exact le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes)
  have hn : D.L₁ ⊔ (T : Subgroup G) ≤ normalizer
      (V₃ ⊓ centralizer (D.QH : Set G) : Set G) :=
    (le_inf h.local_normalizes ((h.local_le.trans
      (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D))).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  rcases h.irreducible _ hp inf_le_left hn with he | he
  · exact he
  · have hc : V₃ ≤ centralizer (D.QH : Set G) := he.symm.le.trans inf_le_right
    exact (hne (commutator_eq_bot_iff_le_centralizer.mpr hc)).elim

/-- The source noncentrality makes both seed and span commutators equal to V₁. -/
theorem seed_and_span_commutator_eq_line
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hne : ⁅V₃, Section08.Source.QH H⁆ ≠ ⊥) :
    ⁅V₃, Section08.Source.QH H⁆ = V₁ ∧ ⁅Section08.Source.UH H V₃, Section08.Source.QH H⁆ = V₁ := by
  have hc : ⁅V₃, Section08.Source.QH H⁆ ≤ V₁ :=
    (commutator_mono (le_conjugateSpanBy V₃ H) le_rfl).trans h.commutator_UH_QH_le_point
  have hd : Nat.card (⁅V₃, Section08.Source.QH H⁆ : Subgroup G) ∣ 2 :=
    d.line_card ▸ card_dvd_of_le hc
  have hs : Nat.card (⁅V₃, Section08.Source.QH H⁆ : Subgroup G) = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with ho | ho
    · exact (hne (eq_bot_of_card_eq _ ho)).elim
    · exact ho
  have he := eq_of_le_of_card_ge hc (by rw [d.line_card, hs])
  exact ⟨he, le_antisymm h.commutator_UH_QH_le_point
    (he.symm.le.trans (commutator_mono (le_conjugateSpanBy V₃ H) le_rfl))⟩

omit d in
/--13.5.4(5) passes from the full point normalizer to every original H∈H_z. -/
theorem seed_noncentral_on_local_core
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hHG : H ≤ G₁) (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    ⁅V₃, Section08.Source.QH H⁆ ≠ ⊥ := by
  intro he
  apply hne
  apply eq_bot_iff.mpr
  exact (commutator_mono le_rfl (pCoreIn_le_pCoreIn_of_sylow T h.T_le_H hHG)).trans he.le

end CFSG.Quasithin.Chapter13.Section07
