module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.Definitions
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Faithful
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The residual escape in original 15.1.22(!)

The specified S₃ or S₃ wr C₂ quotient makes P a {2,3}-group, so
O²(P)=O^{3′}(P). Relative normality in P N_S(L) makes S∩P Sylow
in P, and the residual and this intersection generate P. Consequently
an escaping P placed in M forces the literal O^{3′}(M∩L) to escape M_L.
No assumption that P contains S_L, or that S normalizes L, is needed.

Source: Aschbacher--Smith, original 15.1.22(!), printed p.1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem twoThree_of_small_quotient (X : Type*) [Group X] [Finite X]
    (he : Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    IsPiGroup twoThreePrimes X := by
  have hcard : Nat.card (X ⧸ pCore 2 X) = 6 ∨
      Nat.card (X ⧸ pCore 2 X) = 72 := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      left
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    · obtain ⟨e⟩ := he
      right
      rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, Nat.card_perm, Nat.card_fin]
      norm_num [Nat.card_eq_fintype_card]
  apply IsPiGroup.of_normal_subgroup_and_quotient (pCore 2 X)
  · intro q hq
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    change q.val = 2 ∨ q.val = 3
    left
    exact (Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
      (q.property.dvd_of_dvd_pow (hn ▸ hq))
  · apply (IsPiGroup_iff _ _).mpr
    intro q hq
    change q.val = 2 ∨ q.val = 3
    rcases hcard with hcard | hcard
    · rw [hcard, show 6 = 2*3 from rfl] at hq
      rcases q.property.dvd_mul.mp hq with hq | hq
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp hq)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_three).mp hq)
    · rw [hcard, show 72 = 2^3*3^2 from rfl] at hq
      rcases q.property.dvd_mul.mp hq with hq | hq
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
          (q.property.dvd_of_dvd_pow hq))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_three).mp
          (q.property.dvd_of_dvd_pow hq))

theorem IsSourceParabolic.twoThree {d : CaseIComponentData T M Mc V}
    {P : Subgroup G} (hP : d.IsSourceParabolic P) : IsPiGroup twoThreePrimes P :=
  (twoThree_of_small_quotient (P ⊔ d.sylowNormalizer : Subgroup G) hP.quotient).of_injective
    (inclusion le_sup_left) (inclusion_injective le_sup_left)

/-- The literal Sylow intersection supplements the prime-to-three residual. -/
theorem IsSourceParabolic.residual_sup_sylow_intersection
    {d : CaseIComponentData T M Mc V} {P : Subgroup G}
    (hP : d.IsSourceParabolic P) (hL : d.L ∈ Chapter1.L G d.S) :
    (primeToResidual 3 P).map P.subtype ⊔ (d.S ⊓ P) = P := by
  have hR := Chapter1.Section02.Adequate.local_normalizer_isSylow hL
  have hRP : Chapter1.IsSylowIn 2 d.sylowNormalizer (P ⊔ d.sylowNormalizer) :=
    hR.restrict le_sup_right (sup_le (hP.le_component.trans le_sup_left) le_sup_right)
  have hn : (P.subgroupOf (P ⊔ d.sylowNormalizer)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hP.normalized)
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hRP le_sup_left hn.isSubnormal
  have he : d.sylowNormalizer ⊓ P = d.S ⊓ P := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro x hx
    exact ⟨⟨hx.1,d.L.le_normalizer (hP.le_component hx.2)⟩,hx.2⟩
  have hh := congrArg (Subgroup.map P.subtype) (pResidual_sup_sylow_eq_top U)
  rw [Subgroup.map_sup, hU, he, ←MonoidHom.range_eq_map, range_subtype,
    twoResidual_eq_primeToResidual_three hP.twoThree] at hh
  exact hh

/-- The family conclusion's residual escape is forced by an escaping
member once (*) places it in the first local subgroup. -/
theorem IsSourceParabolic.localThreeResidual_escape
    {d : CaseIComponentData T M Mc V} {P : Subgroup G}
    (hP : d.IsSourceParabolic P) (hL : d.L ∈ Chapter1.L G d.S)
    (hSL : d.SL ≤ d.ML) (hPM : P ≤ M) (hout : ¬ P ≤ d.ML) :
    ¬ d.localThreeResidual ≤ d.ML := by
  intro hr
  apply hout
  rw [←hP.residual_sup_sylow_intersection hL]
  exact sup_le ((embedded_primeToResidual_mono 3 (le_inf hPM hP.le_component)).trans hr)
    ((inf_le_inf_left _ hP.le_component).trans hSL)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
