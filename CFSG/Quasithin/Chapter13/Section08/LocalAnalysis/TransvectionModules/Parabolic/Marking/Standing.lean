module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Action

/-!
# Standing flag and representation applicability for 13.8.6

The flag is specified by its literal subgroup chain, orders and Sylow
invariance. After 13.7.6 supplies the ordinary A₆ quotient, the earlier
natural-representation implication supplies coordinates on V itself.
Taking images constructs all three subspaces required by the local-core
argument; their dimensions follow from the original subgroup orders.
The image of V₃ in U_H/V₁ has dimension two by the exact quotient index.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, pp.876–877; 13.5.2(3) and Remark 13.5.3, pp.915–916;
13.8.6, p.948. This constructor takes an explicit universal representation
implication. `standing_natural_earlier` in `StandingAction` discharges it from
the original natural action before the final assembly uses this module.
-/

public section
open Subgroup Module BinaryPermutation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
open TransvectionRecognition EarlierCore
variable {G : Type*} [Group G]

/-- The flag from Notation 13.2.1 and Remark 13.5.3, before any quotient
recognition, coordinate choice or local-generation conclusion. -/
structure StandingFlag (T : Sylow 2 G) (L V V₁ V₂ V₃ : Subgroup G) : Prop where
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  line_le_plane : V₁ ≤ V₂
  plane_le_seed : V₂ ≤ V₃
  seed_le : V₃ ≤ V
  orders : Nat.card V₁ = 2 ∧ Nat.card V₂ = 4 ∧ Nat.card V₃ = 8
  line_stable : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  plane_stable : (T : Subgroup G) ≤ normalizer (V₂ : Set G)
  seed_stable : (T : Subgroup G) ≤ normalizer (V₃ : Set G)

/-- The ordinary alternating cases of the earlier natural-representation
result, at the fixed genuine standing pair (L,V). Both degrees five and six
are retained. The A₆ quotient is an antecedent to be proved, not an assumed
standing witness. The existential marking permits the automorphism of A₆
needed to express the given natural action; an arbitrary quotient marking
need not have this property. Global source applicability belongs to the
supplier of this earlier implication. -/
@[expose] def EarlierNatural (L V : Subgroup G) (hLV : L ≤ normalizer (V : Set G)) : Prop :=
  ∀ n : ℕ, n = 5 ∨ n = 6 → Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin n)) →
    ∃ (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin n))
      (eV : V ≃* Multiplicative (natural (Fin n))),
      ∀ (l : L) (v : V),
        (eV (V.normalizerMonoidHom ⟨l.val, hLV l.property⟩ v)).toAdd =
          alternatingNaturalRepresentation (Fin n) (eL (QuotientGroup.mk' (pCore 2 L) l))
            (eV v).toAdd

private def flagImage {V : Subgroup G} (e : V ≃* Multiplicative Natural)
    (X : Subgroup G) : Submodule (ZMod 2) Natural :=
  AddSubgroup.toZModSubmodule 2 ((X.subgroupOf V).map e.toMonoidHom).toAddSubgroup'

private theorem flagPreimage_image {V X : Subgroup G} (e : V ≃* Multiplicative Natural)
    (hX : X ≤ V) : flagPreimage e (flagImage e X) = X := by
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    change e v ∈ (X.subgroupOf V).map e.toMonoidHom at hv
    obtain ⟨w, hw, he⟩ := hv
    exact e.injective he ▸ hw
  · intro x hx
    exact ⟨⟨x, hX hx⟩, ⟨⟨x, hX hx⟩, hx, rfl⟩, rfl⟩

private theorem flagImage_dim {V X : Subgroup G} (e : V ≃* Multiplicative Natural)
    (hX : X ≤ V) {n : ℕ} (hc : Nat.card X = 2 ^ n) :
    finrank (ZMod 2) (flagImage e X) = n := by
  have h := flagPreimage_card e (flagImage e X)
  rw [flagPreimage_image e hX, hc] at h
  exact ((Nat.pow_right_injective (by decide : 1 < 2)) h).symm

/-- Apply the earlier representation result only after obtaining the ordinary
quotient, and construct the actual flag subspaces rather than assuming them. -/
noncomputable def StandingFlag.componentSetup {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (s : StandingFlag T L V V₁ V₂ V₃)
    (earlier : EarlierNatural L V (le_sup_left.trans s.normalizes_V))
    (hL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) :
    ComponentSetup T L V V₁ V₂ V₃ := by
  classical
  let h := earlier 6 (Or.inr rfl) hL
  let eL := h.choose
  let eV := h.choose_spec.choose
  have he := h.choose_spec.choose_spec
  have h₃ := s.seed_le
  have h₂ := s.plane_le_seed.trans h₃
  have h₁ := s.line_le_plane.trans h₂
  exact {
    model := eL
    normalizes_L := s.normalizes_L
    normalizes_V := s.normalizes_V
    coordinate := eV
    conjugation := he
    point := flagImage eV V₁
    plane := flagImage eV V₂
    hyperplane := flagImage eV V₃
    point_dim := flagImage_dim eV h₁ s.orders.1
    plane_dim := flagImage_dim eV h₂ s.orders.2.1
    hyperplane_dim := flagImage_dim eV h₃ s.orders.2.2
    point_le_plane := by
      intro x hx
      exact (map_mono (show V₁.subgroupOf V ≤ V₂.subgroupOf V from fun _ h => s.line_le_plane h)) hx
    plane_le_hyperplane := by
      intro x hx
      exact (map_mono (show V₂.subgroupOf V ≤ V₃.subgroupOf V from fun _ h => s.plane_le_seed h)) hx
    line_eq := (flagPreimage_image eV h₁).symm
    plane_eq := (flagPreimage_image eV h₂).symm
    seed_eq := (flagPreimage_image eV h₃).symm
    line_stable := s.line_stable
    plane_stable := s.plane_stable
    seed_stable := s.seed_stable }

variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The literal section image V₃/V₁ has order four and dimension two. -/
theorem sectionImage_seed_finrank [Finite G] (h13 : V₁ ≤ V₃)
    (h1 : Nat.card V₁ = 2) (h3 : Nat.card V₃ = 8) :
    finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2 := by
  have hcard := (V₁.subgroupOf V₃).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h13).toEquiv, h1, h3] at hcard
  have hi : V₁.relIndex V₃ = 4 := by change 2 * V₁.relIndex V₃ = 8 at hcard; omega
  rw [← relIndex_subgroupOf (le_conjugateSpanBy V₃ H)] at hi
  have hi' : Nat.card (sectionImage H V₃ V₁ V₃) = 4 := by
    let e : sectionImage H V₃ V₁ V₃ ≃
        (V₃.subgroupOf (Source.UH H V₃)).map
          (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))) := {
      toFun := fun x => ⟨x.val.toMul, x.property⟩
      invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e, ← relIndex_ker (V₃.subgroupOf (Source.UH H V₃))
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))), QuotientGroup.ker_mk']
    exact hi
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := sectionImage H V₃ V₁ V₃)
  rw [Nat.card_zmod, hi'] at hd
  exact ((Nat.pow_right_injective (by decide : 1 < 2)) hd.symm)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
