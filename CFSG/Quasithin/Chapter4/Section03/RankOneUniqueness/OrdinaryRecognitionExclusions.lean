module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionAction
public import Theory.SpecificGroups.PSL3.LocalResidualFixer
public import Theory.SpecificGroups.Triality.CentralLocalFixer

/-!
# Two marked ordinary-row exclusions using the source fixed radical

The nontrivial R₀ action rules out PSL₃ whenever the original L-image
contains the model unipotent Sylow; in particular it rules out both marked
parabolic residuals, including q = 4 and all perfect central covers.
It also rules out the marked central-node local residual of genuine triality.
The proofs transport the actual source involution through K/Z(K), then use
pointwise rigidity of the displayed model local subgroup.

These theorems retain the original L and quotient map. Their local-placement
premises still belong to the C.3.1 recognition argument constructing
OrdinarySymplecticMarking; neither a model-family tag nor the rank-one quotient
alone supplies them. The other local rows and full module marking remain separate.
Source: Aschbacher--Smith C.3.1, pp.149--151, and 4.3.6, printed p.614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace SourceConfiguration

/-- The original ordinary configuration cannot have a projective degree-three
marking whose original local contains the model unipotent Sylow. This retains
all central covers and includes the field of order four. -/
theorem ordinary_no_pslThree_of_unipotent_placement (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : (c.K ⧸ center c.K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hU : Matrix.PSL3.LinearThree.unipotent F ≤
      c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))) : False := by
  let q := QuotientGroup.mk' (center c.K)
  let A := c.ordinaryLocal.map (e.toMonoidHom.comp q)
  have hA : ¬ Group.IsSolvable A := by
    intro hsol
    let := hsol
    let f : (c.ordinaryLocal.map q) →* A :=
      (e.toMonoidHom.comp (c.ordinaryLocal.map q).subtype).codRestrict A (by
        rintro ⟨x,⟨l,hl,rfl⟩⟩
        exact ⟨l,hl,rfl⟩)
    exact c.ordinary_quotient_local_nonsolvable ho
      (Group.isSolvable_of_isSolvable_injective (f := f) (by
        intro x y h
        exact Subtype.ext (e.injective (congrArg Subtype.val h))))
  obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
  have ha := Matrix.PSL3.LinearThree.eq_one_of_fixes_nonsolvable_unipotent_overgroup
    hn hF A hU hA a hfix
  simp only [ha,orderOf_one] at hao
  omega

/-- Literal C.3.1 linear-row application: either original parabolic-residual
marking contradicts the source R₀ action, without any larger-field assumption. -/
theorem ordinary_no_pslThree_parabolic_marking (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : (c.K ⧸ center c.K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hlocal : c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
        Matrix.PSL3.LinearThree.pointLocal F ∨
      c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
        Matrix.PSL3.LinearThree.lineLocal F) : False := by
  apply c.ordinary_no_pslThree_of_unipotent_placement D ho hn hF e
  rcases hlocal with hlocal | hlocal
  · rw [hlocal]
    exact Matrix.PSL3.LinearThree.unipotent_le_pointLocal F
  · rw [hlocal]
    exact Matrix.PSL3.LinearThree.unipotent_le_lineLocal F

/-- Literal application of the central-node triality rigidity theorem to the
same source component and its actual original L. The local marking is still
an input to this exclusion and is not a consequence of a family tag. -/
theorem ordinary_no_triality_central_marking (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    (n : ℕ) (hn : 0 < n)
    (e : (c.K ⧸ center c.K) ≃* Triality.Standard.BinaryCarrier n hn)
    (hlocal : c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
      Triality.Standard.Parabolics.localFactor
        (Triality.Standard.binaryParameters n hn) .central) : False := by
  obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
  have ha2 : a ^ 2 = 1 := hao ▸ pow_orderOf_eq_one a
  rw [hlocal] at hfix
  have ha := Triality.Standard.Parabolics.central_local_involutory_fixer_eq_one n hn a ha2 hfix
  simp only [ha,orderOf_one] at hao
  omega

end SourceConfiguration
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
