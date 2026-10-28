module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.Action
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.Geometry
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# Transport from the actual block action to the permutation model

An equivariant identification of U with the natural module identifies every
literal centralizer C_U(B) with the fixed space of the image of B. Counting
these spaces transports the fixed codimensions and the absence of strong
offenders from the odd-degree model.

If the image of B is a conjugate of D, the explicit model conjugator lifts
through the image of L to an element of L itself. This produces the two
actual conjugate subgroups and their dimension equality. In particular the
whole acting image is S₅; surjectivity is a conclusion rather than a premise.
The intrinsic Thompson-subgroup identity permits B = J(R) inside H.

All results here retain the action model as an explicit hypothesis. Its
construction, and the actual Thompson-image identification, are the separate
inputs declared in `Action`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3),
printed p.155; B.2.18(c),(d) and B.3.2(1),(4), pp.80 and 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive
open Subgroup BinaryPermutation Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] {H L : Subgroup G}

private theorem action_eq_iff_commute (m : NaturalActionModel H L) (x : H) (v : U L) :
    naturalRepresentation (Fin 5) (m.quotient x) (Multiplicative.toAdd (m.moduleEquiv v)) =
        Multiplicative.toAdd (m.moduleEquiv v) ↔
      (x : G) * (v : G) = (v : G) * (x : G) := by
  have he := m.intertwining x v
  constructor
  · intro hf
    have hf' : Multiplicative.ofAdd
        (naturalRepresentation (Fin 5) (m.quotient x) (Multiplicative.toAdd (m.moduleEquiv v))) =
          m.moduleEquiv v := congrArg Multiplicative.ofAdd hf
    have he' := congrArg (fun w => (m.moduleEquiv.symm w : G)) hf'
    simp only [m.moduleEquiv.symm_apply_apply] at he'
    exact mul_inv_eq_iff_eq_mul.mp (he.symm.trans he')
  · intro hc
    have he' : m.moduleEquiv.symm (Multiplicative.ofAdd
        (naturalRepresentation (Fin 5) (m.quotient x) (Multiplicative.toAdd (m.moduleEquiv v)))) =
          v := Subtype.ext (he.trans (by rw [hc, mul_inv_cancel_right]))
    have hf := congrArg (fun w => Multiplicative.toAdd (m.moduleEquiv w)) he'
    simpa only [m.moduleEquiv.apply_symm_apply, toAdd_ofAdd] using hf

/-- The literal centralizer in U is the fixed space of the modeled image. -/
noncomputable def fixedEquiv (m : NaturalActionModel H L) (B : Subgroup H) :
    ↥(U L ⊓ centralizer (B.map H.subtype : Set G)) ≃
      fixedSpace (naturalRepresentation (Fin 5)) (B.map m.quotient) where
  toFun v := ⟨Multiplicative.toAdd (m.moduleEquiv ⟨v, v.property.1⟩), by
    apply (mem_fixedSpace_iff _ _ _).mpr
    rintro a ⟨x, hx, rfl⟩
    exact (action_eq_iff_commute m x ⟨v, v.property.1⟩).mpr
      (mem_centralizer_iff.mp v.property.2 x (mem_map_of_mem _ hx))⟩
  invFun w := ⟨m.moduleEquiv.symm (Multiplicative.ofAdd w.val),
    (m.moduleEquiv.symm (Multiplicative.ofAdd w.val)).property, by
    apply mem_centralizer_iff.mpr
    rintro x ⟨x, hx, rfl⟩
    apply (action_eq_iff_commute m x (m.moduleEquiv.symm (Multiplicative.ofAdd w.val))).mp
    simpa only [m.moduleEquiv.apply_symm_apply, toAdd_ofAdd] using
      (mem_fixedSpace_iff _ _ _).mp w.property (m.quotient x) (mem_map_of_mem _ hx)⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

/-- Fixed-subgroup cardinalities are powers of the model fixed-space dimensions. -/
theorem fixed_card (m : NaturalActionModel H L) (B : Subgroup H) :
    Nat.card (U L ⊓ centralizer (B.map H.subtype : Set G) : Subgroup G) =
      2 ^ Module.finrank (ZMod 2)
        (fixedSpace (naturalRepresentation (Fin 5)) (B.map m.quotient)) := by
  rw [Nat.card_congr (fixedEquiv m B), Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod]

/-- The full natural-action model identifies U itself as a group of order sixteen. -/
theorem module_card (m : NaturalActionModel H L) : Nat.card (U L) = 2 ^ 4 := by
  rw [Nat.card_congr m.moduleEquiv.toEquiv]
  change Nat.card (natural (Fin 5)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_natural_odd (Fin 5) (by decide)]
  rfl

/-- The source binary centralizer codimension agrees with the linear model. -/
theorem fixed_codimension (m : NaturalActionModel H L) (B : Subgroup H) :
    Nat.log 2 (Nat.card (U L)) -
        Nat.log 2 (Nat.card (U L ⊓ centralizer (B.map H.subtype : Set G) : Subgroup G)) =
      fixedCodim (naturalRepresentation (Fin 5)) (B.map m.quotient) := by
  have he := fixedCodim_add_finrank (naturalRepresentation (Fin 5)) (B.map m.quotient)
  rw [finrank_natural_odd (Fin 5) (by decide)] at he
  simp only [Fintype.card_fin] at he
  rw [module_card m, fixed_card m B]
  simp only [Nat.log_pow (by decide : 1 < 2)]
  omega

/-- The full alternating action has fixed codimension four on the actual U. -/
theorem block_fixed_codimension (m : NaturalActionModel H L) (hLH : L ≤ H) :
    Nat.log 2 (Nat.card (U L)) -
        Nat.log 2 (Nat.card (U L ⊓ centralizer (L : Set G) : Subgroup G)) = 4 := by
  have he := fixed_codimension m (L.subgroupOf H)
  rw [map_subgroupOf_eq_of_le hLH, m.block_image, fixedCodim_alternating] at he
  exact he

/-- Absence of strong offenders transported to the actual centralizer indices. -/
theorem image_rank_le_fixed_codimension (m : NaturalActionModel H L) (B : Subgroup H)
    (hB : IsElementaryTwo (B.map m.quotient)) :
    rank (B.map m.quotient) ≤ Nat.log 2 (Nat.card (U L)) -
      Nat.log 2 (Nat.card (U L ⊓ centralizer (B.map H.subtype : Set G) : Subgroup G)) := by
  rw [fixed_codimension m B]
  exact le_of_not_gt fun hlt =>
    ChapterB.Offenders.Odd.not_isStrongOffender_natural (Or.inl rfl) _ ⟨hB, hlt⟩

/-- Lift the concrete two-conjugate construction through the actual image of L. -/
theorem exists_local_conjugate_pair (m : NaturalActionModel H L) (B : Subgroup H)
    (hB : ChapterB.Offenders.IsConjugateTo (B.map m.quotient) (ChapterB.Offenders.D 5)) :
    ∃ g : H, g ∈ L.subgroupOf H ∧
      (B ⊔ B.map (MulAut.conj g).toMonoidHom).map m.quotient = ⊤ ∧
      (Nat.log 2 (Nat.card (U L)) -
        Nat.log 2 (Nat.card (U L ⊓ centralizer (B.map H.subtype : Set G) : Subgroup G))) +
      (Nat.log 2 (Nat.card (U L)) -
        Nat.log 2 (Nat.card (U L ⊓ centralizer
          ((B.map (MulAut.conj g).toMonoidHom).map H.subtype : Set G) : Subgroup G))) = 4 := by
  obtain ⟨g, hg, hgen, hdim⟩ := exists_model_conjugate_pair hB
  rw [← m.block_image] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  have he : (B.map (MulAut.conj x).toMonoidHom).map m.quotient =
      (B.map m.quotient).map (MulAut.conj (m.quotient x)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Subgroup.map_sup, he]
    exact hgen
  · rw [fixed_codimension, fixed_codimension, he]
    exact hdim.trans fixedCodim_alternating

/-- A disjoint-transposition image forces the whole modeled action to be S₅. -/
theorem quotient_surjective_of_image (m : NaturalActionModel H L) (B : Subgroup H)
    (hB : ChapterB.Offenders.IsConjugateTo (B.map m.quotient) (ChapterB.Offenders.D 5)) :
    Function.Surjective m.quotient := by
  obtain ⟨g, _, hgen, _⟩ := exists_local_conjugate_pair m B hB
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  exact map_le_range _ _

/-- Thompson formation commutes with viewing R inside its actual overgroup H. -/
theorem intrinsic_thompson {R : Subgroup G} (hRH : R ≤ H) :
    Stellmacher.elementaryAbelianMaxJ (R.subgroupOf H) =
      (Stellmacher.elementaryAbelianMaxJ R).subgroupOf H := by
  have hJR : Stellmacher.elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hE => hE.1
  apply map_injective H.subtype_injective
  rw [← Stellmacher.elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hRH,
    map_subgroupOf_eq_of_le (hJR.trans hRH)]

/-- The common-normal exclusion makes the modeled Thompson action nontrivial. -/
theorem thompson_image_ne_bot [Finite G] {K : GroupClass.{u}} {A R : Subgroup G}
    (h : Configuration K A H R L) (m : NaturalActionModel H L) :
    ((Stellmacher.elementaryAbelianMaxJ R).subgroupOf H).map m.quotient ≠ ⊥ := by
  intro hbot
  have hker := (Subgroup.map_eq_bot_iff _).mp hbot
  rw [m.kernel] at hker
  apply thompson_not_le_HCore h
  intro x hx
  have hJH : Stellmacher.elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hE => hE.1).trans (h.join_eq ▸ le_sup_right)
  exact mem_map.mpr ⟨⟨x, hJH hx⟩, hker hx, rfl⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive

end
