module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Control
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.NormalizerImage.Transfer
public import Theory.GroupAction.SixteenOddComplements.Five
public import Theory.GroupAction.SixteenOddComplements.Nine

/-!
# The two finite normalizer calculations for the middle sixteen

The literal quotient N_G(A)/A contains the self-normalizing elementary
four T/A. Burnside transfer supplies a normal odd complement. If the
quotient had order sixty, that complement would contain a characteristic
five-subgroup, contradicting the faithful sixteen-element action. At order
thirty-six the complement is an elementary nine, and its faithful
four-group action identifies the quotient with S3 × S3.

`normalizer_results` supplies exactly the finite-normalizer premise of
`middle_of_local_producers`. The missing-involution theorem applies the
first calculation to the existing fusion-count consumer. Construction of
the explicit MiddleLocalData remains with the separate source assembly.

Source: M. Aschbacher, “A 2-local characterization of M12”, Lemma 3.1,
Illinois J. Math. 47 (2003), printed pp.36–37. Recognition at order
thirty-six uses the normal-nine action rather than an asserted order for
its full normalizer in GL4(2).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace MiddleLocalData
variable (m : MiddleLocalData z)

theorem normalizer_quotient_card_ne_sixty (h : Hypotheses z) :
    Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) ≠ 60 := by
  intro hcard
  obtain ⟨J, hJ, _, hcount, _⟩ := m.exists_normalizer_odd_complement h
  let : J.Normal := hJ
  have hJcard : Nat.card J = 15 := by rw [hcard] at hcount; omega
  let : IsElementaryAbelian 2 m.normalizerFour := m.normalizerFour_elementary
  let ρ := m.A.normalizerMonoidHom.range.subtype.comp m.normalizerActionQuotient.toMonoidHom
  have hρ : Function.Injective ρ :=
    m.A.normalizerMonoidHom.range.subtype_injective.comp m.normalizerActionQuotient.injective
  exact SixteenOddComplements.no_four_of_normal_fifteen ρ hρ m.card
    J hJcard m.normalizerFour (m.normalizerFour_card h)

theorem normalizer_quotient_equiv_of_card_thirtysix (h : Hypotheses z)
    (hcard : Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) = 36) : Nonempty
      ((normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨J, hJ, hc, hcount, _⟩ := m.exists_normalizer_odd_complement h
  let : J.Normal := hJ
  have hJcard : Nat.card J = 9 := by rw [hcard] at hcount; omega
  let : IsElementaryAbelian 2 m.A := m.elementary
  let : IsElementaryAbelian 2 m.normalizerFour := m.normalizerFour_elementary
  let e := m.normalizerActionQuotient
  let H := m.A.normalizerMonoidHom.range
  let J' := J.map e.toMonoidHom
  let P' := m.normalizerFour.map e.toMonoidHom
  let : J'.Normal := hJ.map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 P' := IsElementaryAbelian.map e.toMonoidHom
  have hJ' : Nat.card J' = 9 := (card_map_of_injective e.injective).trans hJcard
  have hP' : Nat.card P' = 4 := (card_map_of_injective e.injective).trans
    (m.normalizerFour_card h)
  have hc' : J'.IsComplement' P' := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [hJ', hP', ← Nat.card_congr e.toEquiv, hcard]
    · exact disjoint_map e.injective hc.disjoint
  obtain ⟨emodel⟩ := SixteenOddComplements.equiv_of_normal_nine_four m.card H J' hJ' P' hP' hc'
  exact ⟨e.trans emodel⟩

/-- The two finite-normalizer clauses consumed by middle_of_local_producers. -/
theorem normalizer_results (h : Hypotheses z) :
    (Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) ≠ 60) ∧
    (Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) = 36 → Nonempty
      ((normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :=
  ⟨m.normalizer_quotient_card_ne_sixty h, m.normalizer_quotient_equiv_of_card_thirtysix h⟩

/-- The order-sixty obstruction supplies the missing involution in the
literal local sixteen, as required by the fusion-union argument. -/
theorem exists_missing_involution (h : Hypotheses z) :
    ∃ a ∈ m.A, a ≠ 1 ∧ ¬ IsConj z a :=
  m.missing_of_quotient_card_ne_sixty h (m.normalizer_quotient_card_ne_sixty h)

end MiddleLocalData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
end
