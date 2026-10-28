module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Moving

/-!
# The upper central attachment of a natural commutator module

The connecting cohomology map has kernel exactly C_V(G) + [V,G]. Its induced
injection bounds the dimension above that sum by H¹(G,[V,G]). For a marked
natural commutator module, the checked binary H¹ calculation gives dimension
at most one. Thus this branch splits over the fixed space or has precisely
one upper dimension. No indecomposability or fixed-space splitting is assumed.

Source: Aschbacher–Smith B.4.8(1),(3),(4), B.5.1(5), printed pp.91,99–103;
Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open AbelianCore.QuotientRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL V)

private theorem fixed_eq_fixedSpace : fixed ρ = fixedSpace ρ ⊤ := by
  ext v
  constructor
  · intro h g
    exact h g.val
  · intro h g
    exact h ⟨g, Subgroup.mem_top g⟩

/-- The quotient by the actual commutator module has trivial action. -/
theorem moving_hasTrivialQuotient : HasTrivialQuotient (moving ρ) :=
  fun g v => Coinvariants.sub_mem_ker g v

/-- The extension-class map detects exactly the sum C + D. -/
theorem extensionClass_kernel :
    (extensionClass (moving ρ) (moving_hasTrivialQuotient ρ)).ker = centralSum ρ := by
  rw [ker_extensionClass, fixed_eq_fixedSpace, sup_comm]

variable [FiniteDimensional (ZMod 2) V]

/-- The upper attachment embeds in H¹(G,D); central direct summands have been
removed by taking the literal quotient by C + D. -/
theorem upper_finrank_le_h1 :
    Module.finrank (ZMod 2) (V ⧸ centralSum ρ) ≤
      Module.finrank (ZMod 2) (H1 (moving ρ).toRepresentation) := by
  let f := extensionClass (moving ρ) (moving_hasTrivialQuotient ρ)
  rw [← extensionClass_kernel ρ, f.quotKerEquivRange.finrank_eq]
  exact f.range.finrank_le

omit [FiniteDimensional (ZMod 2) V] in
/-- One marked natural copy has the checked one-dimensional first cohomology. -/
theorem Copies.finrank_h1 (e : Copies ρ 1) :
    Module.finrank (ZMod 2) (H1 ρ) = 1 := by
  let E := e.equiv.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → ZMod 2))
  have he : ∀ g v, E (ρ g v) = specialLinearNatural 3 (e.marking g) (E v) := by
    intro g v
    exact e.equivariant g v 0
  exact (H1Congr ρ (specialLinearNatural 3) e.marking E he).finrank_eq.trans
    SLHigherNatural.finrank_H1_sl3_two

/-- A natural commutator module has at most one dimension of upper attachment.
No splitting of fixed vectors or indecomposability hypothesis is used. -/
theorem upper_finrank_le_one (e : Copies (moving ρ).toRepresentation 1) :
    Module.finrank (ZMod 2) (V ⧸ centralSum ρ) ≤ 1 :=
  (upper_finrank_le_h1 ρ).trans_eq (e.finrank_h1 _)

/-- Vanishing H¹ of the commutator module excludes all upper attachments. -/
theorem centralSum_eq_top_of_h1_zero
    (hh : Module.finrank (ZMod 2) (H1 (moving ρ).toRepresentation) = 0) :
    centralSum ρ = ⊤ := by
  have hz := upper_finrank_le_h1 ρ
  rw [hh] at hz
  have hd := (centralSum ρ).finrank_quotient_add_finrank
  apply Submodule.eq_top_of_finrank_eq
  omega

/-- The one-copy case is either an actual direct sum or has upper dimension one. -/
theorem natural_upper_dichotomy (e : Copies (moving ρ).toRepresentation 1) :
    IsCompl (fixedSpace ρ ⊤) (moving ρ).toSubmodule ∨
      (Disjoint (fixedSpace ρ ⊤) (moving ρ).toSubmodule ∧
        Module.finrank (ZMod 2) (V ⧸ centralSum ρ) = 1) := by
  have hdis := (disjoint_iff_fixedMoving_eq_bot ρ).mpr e.fixed_eq_bot
  have hb := upper_finrank_le_one ρ e
  by_cases hz : Module.finrank (ZMod 2) (V ⧸ centralSum ρ) = 0
  · have ht : centralSum ρ = ⊤ := by
      have hd := (centralSum ρ).finrank_quotient_add_finrank
      apply Submodule.eq_top_of_finrank_eq
      omega
    exact Or.inl ⟨hdis, codisjoint_iff.mpr ht⟩
  · exact Or.inr ⟨hdis, by omega⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
