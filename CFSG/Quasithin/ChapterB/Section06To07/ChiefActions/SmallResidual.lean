module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.ResidualElementary
public import Theory.Representation.BinaryOffender.ProductSplitting
public import Theory.SpecificGroups.SymmetricTwoResidual
/-!
# Small natural chief offenders survive modulo the two-residual

On a five-point natural module every offender contains an odd permutation,
whereas the two-residual is alternating. For the paired natural action,
product splitting supplies a nontrivial coordinate offender, and each
projection of the two-residual is alternating. The marked source pair
preserves every fixed codimension, so the same exclusion holds for the
original offender before taking its fixed-space quotient. Its residual is
the actual embedded residual of the ambient minimal parabolic.

The solvable small natural actors have elementary cubic residual; hence no
nontrivial elementary two-subgroup lies in it. Combining the three branches
retains the original subgroup A in the literal chief-action image. This is
the residual obstruction used to compare a small essential chief action with
a putative larger-field chief action, without requiring module isomorphism.
No additional sharpness or quadratic-action premise is needed.

Source: Aschbacher–Smith B.3.2(4), B.6.9 and3.1.9(5), printed pp.83,
115–116 and578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction BinaryPermutation

/-- Any five-point natural offender has a nontrivial image modulo the two-residual. -/
theorem five_offender_not_le_twoResidual
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (e : ActionEquiv ρ (naturalRepresentation (Fin 5)))
    {A : Subgroup D} (hA : IsOffender ρ A) : ¬ A ≤ pResidual 2 D := by
  intro hAR
  have hB := hA.map_equivariant _ _ e.groupEquiv.toMonoidHom e.groupEquiv.injective
    e.linearEquiv e.intertwines
  obtain ⟨B,hBA,hB⟩ := hB.exists_bestOffender (naturalRepresentation (Fin 5))
  apply ((Offenders.Odd.isBestOffender_natural_iff_caseAFamily (Or.inl rfl) B).mp hB).not_le_alternating
  exact hBA.trans ((map_mono hAR).trans ((map_pResidual_le 2 e.groupEquiv.toMonoidHom).trans_eq
    (Equiv.Perm.twoResidual_eq_alternating (Fin 5))))

/-- Product splitting leaves a nontrivial natural coordinate offender, which
cannot lie in the alternating projection of the two-residual. -/
theorem five_pair_offender_not_le_twoResidual
    {A : Subgroup (FiveCentralExtension.Sym × FiveCentralExtension.Sym)}
    (hA : IsOffender FivePair.action A) :
    ¬ A ≤ pResidual 2 (FiveCentralExtension.Sym × FiveCentralExtension.Sym) := by
  intro hAR
  obtain ⟨hprod,h₁,h₂⟩ := offender_product_of_not_strong
    (coreRepresentation (Fin 5)) (coreRepresentation (Fin 5))
    (fun ⟨B,hB⟩ => Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) B hB)
    (fun ⟨B,hB⟩ => Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) B hB) hA
  have hp₁ : A.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5) :=
    (map_mono hAR).trans ((map_pResidual_le 2 (MonoidHom.fst FiveCentralExtension.Sym FiveCentralExtension.Sym)).trans_eq
      (Equiv.Perm.twoResidual_eq_alternating (Fin 5)))
  have hp₂ : A.map (MonoidHom.snd _ _) ≤ alternatingGroup (Fin 5) :=
    (map_mono hAR).trans ((map_pResidual_le 2 (MonoidHom.snd FiveCentralExtension.Sym FiveCentralExtension.Sym)).trans_eq
      (Equiv.Perm.twoResidual_eq_alternating (Fin 5)))
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact hA.1.1 (by rw [hprod,h₁,h₂,bot_prod_bot])
    · exact Offenders.core_offender_not_le_alternating (Or.inl rfl) h₂ hp₂
  · exact Offenders.core_offender_not_le_alternating (Or.inl rfl) h₁ hp₁

/-- The small solvable natural actors have cubic residual, so a nontrivial
elementary two-actor cannot lie in it. -/
theorem SmallNaturalWreathAction.offender_not_le_twoResidual
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (h : SmallNaturalWreathAction ρ)
    {A : Subgroup D} (hA : IsOffender ρ A) : ¬ A ≤ pResidual 2 D := by
  intro hAR
  let := hA.1.2
  let := h.residual_elementary
  apply hA.1.1
  apply le_bot_iff.mp
  intro a ha
  have h₂ : a^2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have h₃ : a^3 = 1 := elemPow_eq_one_of_isElementaryAbelian a (hAR ha)
  have he : a = 1 := by
    have hh : a^3 = a := by rw [pow_succ, h₂, one_mul]
    exact hh.symm.trans h₃
  exact mem_bot.mpr he

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- On the actual paired-five source, restriction and the marked codimension
identity preserve the original offender and its residual membership. -/
theorem source_pair_five_offender_not_le_twoResidual
    (ρ : Representation (ZMod 2) D W)
    (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤) (hcore : pCore 2 D = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    {A : Subgroup D} (hA : IsOffender ρ A) : ¬ A ≤ pResidual 2 D := by
  intro hAR
  let Y := offenderSubgroup ρ
  have hff : IsFFModule ρ := ⟨A,hA⟩
  have hAY : A ≤ Y := hAR.trans (offender_generation T hP ρ hff hcore).1
  let B := A.subgroupOf Y
  have hB : IsOffender (ρ.comp Y.subtype) B := hA.subgroupOf ρ hAY
  let C := B.map c.action.groupEquiv.toMonoidHom
  have hC : IsOffender FivePair.action C := by
    let := hB.1.2
    refine ⟨⟨fun hz => hB.1.1
      ((map_eq_bot_iff_of_injective B c.action.groupEquiv.injective).mp hz),
      IsElementaryAbelian.map _⟩, ?_⟩
    rw [rank_map_injective _ c.action.groupEquiv.injective, ← c.symmetric_fixedCodim]
    exact hB.2
  apply five_pair_offender_not_le_twoResidual hC
  have hBR : B ≤ pResidual 2 Y := by
    apply (map_le_map_iff_of_injective Y.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hAY, offender_residual_eq T hP ρ hff hcore]
    exact hAR
  exact (map_mono hBR).trans (map_pResidual_le 2 c.action.groupEquiv.toMonoidHom)

/-- Every small source branch separates each actual offender from the
ambient two-residual. The conclusion needs no additional quadratic premise. -/
theorem small_natural_offender_not_le_twoResidual
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hcore : pCore 2 D = ⊥)
    (hsmall : SmallNaturalWreathAction ρ ∨ ChiefFiveMarkedSection ρ ∨
      ∃ d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5))))
    {A : Subgroup D} (hA : IsOffender ρ A) : ¬ A ≤ pResidual 2 D := by
  rcases hsmall with hs | ⟨hqs,c,⟨e⟩⟩ | ⟨d,⟨c⟩⟩
  · exact hs.offender_not_le_twoResidual hA
  · let := hi
    obtain ⟨⟨e'⟩,_⟩ := source_quasisimple_five_whole_action ρ hf T hP ⟨A,hA⟩ hcore hqs c e
    exact five_offender_not_le_twoResidual ρ e' hA
  · exact source_pair_five_offender_not_le_twoResidual ρ T hP hcore d c hA

/-- The literal image of the original chief offender cannot lie in the
two-residual in any small source branch. This retains the original subgroup A
for common-kernel transfer between chief representations. -/
theorem minimalParabolic_small_chief_offender_not_le_twoResidual
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (A : Subgroup D)
    (hA : IsOffender (imageRepresentation ρ) (actionSubgroup ρ A))
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ∃ d : SourceTwoFactorCase ((imageRepresentation ρ).comp
        (offenderSubgroup (imageRepresentation ρ)).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5)))) :
    ¬ actionSubgroup ρ A ≤ pResidual 2 (actionImage ρ) := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  exact small_natural_offender_not_le_twoResidual _ (imageRepresentation_injective ρ)
    (imageRepresentation_irreducible ρ inferInstance) (S.mapSurjective hq)
    (minimalParabolic_reduced_image S hS q hq hc hn).2 hc hsmall hA

end CFSG.Quasithin.ChapterB
