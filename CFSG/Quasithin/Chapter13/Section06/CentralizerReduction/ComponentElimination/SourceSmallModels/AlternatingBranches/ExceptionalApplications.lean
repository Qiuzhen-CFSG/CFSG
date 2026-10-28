module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.BlockQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.ExceptionalSeven

/-!
# Exceptional A₇ applications of the constructed quotient action

The actual exceptional-block predicate now supplies the faithful binary
four-space and its conjugation quotient model. A marked single three-cycle
therefore proves both the ambient and checked centralizer comparisons and
feeds the B.2.14/13.6.17 contradiction with no extra representation premise.

The remaining actor classification must also handle actors whose cubic
elements are products of disjoint three-cycles. These conditional consumers
do not assert that every source actor has the marking used here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.22,
printed pp.932–933.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches
variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G} {v : G}

/-- The actual exceptional block predicate supplies the representation; only the actor marking remains. -/
theorem exceptionalSeven_centralizer_eq_of_quotient_cycle
    (h : IsExceptionalA7Block K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (hLK : Lv L v ≤ K)
    (hcycle : ∃ d : Lv L v,
      Equiv.Perm.IsThreeCycle
        (e (QuotientGroup.mk' (pCore 2 K) ⟨d, hLK d.property⟩) : Equiv.Perm (Fin 7))) :
    (blockU K).map K.subtype ⊓ centralizer (Lv L v : Set G) =
      (blockU K).map K.subtype ⊓ centralizer (K : Set G) := by
  let := h.1.module_elementary
  obtain ⟨ρ, hρ, hdim, m, hactor⟩ := exceptionalSeven_quotientModel K h e
  apply exceptionalSeven_centralizer_eq_of_threeCycle (V := Additive (BlockModule K)) ρ hρ hdim m hLK
  obtain ⟨d, hd⟩ := hcycle
  exact ⟨d, by simpa only [hactor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hd⟩

/-- The same constructed model supplies the literal checked centralizer comparison. -/
theorem exceptionalSeven_checked_eq_of_quotient_cycle
    (h : IsExceptionalA7Block K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (hLK : Lv L v ≤ K)
    (hv : v ^ 2 = 1)
    (hcycle : ∃ d : Lv L v,
      Equiv.Perm.IsThreeCycle
        (e (QuotientGroup.mk' (pCore 2 K) ⟨d, hLK d.property⟩) : Equiv.Perm (Fin 7))) :
    checkedImage v ((blockU K).map K.subtype) ⊓
      centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
    checkedImage v ((blockU K).map K.subtype) ⊓
      centralizer (checkedImage v K : Set (Gcheck v)) :=
  checked_centralizer_eq_of_ambient L K ((blockU K).map K.subtype) v hLK hv
    (exceptionalSeven_centralizer_eq_of_quotient_cycle h e hLK hcycle)

/-- The source endgame using the constructed action, with B.2.14 and 13.6.17 explicit. -/
theorem exceptionalSeven_excluded_of_quotient_cycle
    (h : IsExceptionalA7Block K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hK : K ≤ Gv v) (hLK : Lv L v ≤ K) (hv : v ^ 2 = 1)
    (hcycle : ∃ d : Lv L v,
      Equiv.Perm.IsThreeCycle
        (e (QuotientGroup.mk' (pCore 2 K) ⟨d, hLK d.property⟩) : Equiv.Perm (Fin 7)))
    (a : Gv v) (F : Subgroup (Gcheck v)) [IsMulCommutative F]
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v ((blockU K).map K.subtype) ⊔
      (F ⊓ centralizer (checkedImage v K : Set (Gcheck v))))
    (hnot : ¬ K ≤ Gv (a : G)) : False := by
  apply hnot
  exact Source.centralizes_of_checked_fixed_space_comparison L K ((blockU K).map K.subtype)
    v a F hK h.1.twoPerfect hv hLK ha haF hsplit
    (exceptionalSeven_checked_eq_of_quotient_cycle h e hLK hv hcycle)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches
