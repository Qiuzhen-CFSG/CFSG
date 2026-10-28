module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure.Models
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.PResidual.PrimeToQuotientLift
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure

/-!
# The residual extension of the actual PSL₃(4) component

After component uniqueness and F(H/O₂(H)) = 1 are supplied, conjugation
faithfully embeds H/O₂(H) into Aut(PSL₃(4)). The component image maps onto
the literal inner automorphism subgroup. The proved automorphism calculation
therefore identifies O^{3′} with either the inner subgroup or the actual
inner-diagonal subgroup, which is PGL₃(4). In the first case a coprime-index
argument lifts the equality to K = O^{3′}(H).

This gives a direct route for the fixed PSL₃(4) model without the universal
A.3.18 parameter classification. It uses H/O₂(H) throughout and makes no
identification with A.3.18's different quotient H/O₃′(H). The preceding
three-core and other-component exclusions do not use uniqueness, so they
can feed the independent Suzuki argument before this result is applied.
Uniqueness and trivial Fitting remain obligations of the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 13.6.27,
printed pp.934–935; GLS3, Theorem 2.5.12 and §2.7, for the imported concrete
automorphism calculation.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure

variable {H : Type*} [Group H] [Finite H] {K : Subgroup H}

/-- The two possible residuals, using the actual component quotient equivalence. -/
theorem linear_residual_dichotomy_of_unique_component (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥) :
    K = primeToResidual 3 H ∨
      Nonempty (primeToResidual 3 (H ⧸ pCore 2 H) ≃* PGL3Four) := by
  let _ := pCore_isNilpotent (p := 2) (G := H)
  let _ := hK.normal_of_unique hu
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  have hB : B.IsCComponent := hK.map_quotient _
  have huB : ∀ D : Subgroup (H ⧸ pCore 2 H), D.IsCComponent → D = B :=
    fun _ hD => hK.unique_map_quotient hu _ hD
  let _ := hB.normal_of_unique huB
  let d : B ≃* L3Four := (cComponentTwoCoreQuotientEquiv hK).symm.trans e
  let a : (H ⧸ pCore 2 H) →* MulAut L3Four :=
    (MulAut.congr d).toMonoidHom.comp MulAut.conjNormal
  have ha : Function.Injective a := (MulAut.congr d).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot B
      (hB.centralizer_bot_of_unique_of_fitting_bot huB hf))
  have hBa : B.map a = MulAut.innerSubgroup L3Four := by
    have hconj : B.map (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut B) =
        MulAut.innerSubgroup B := by
      ext f
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, MulAut.conjNormal_val⟩
    change B.map ((MulAut.congr d).toMonoidHom.comp
      (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut B)) = _
    rw [← map_map, hconj, MulAut.map_innerSubgroup_congr]
  let A := a.range
  have hA : MulAut.innerSubgroup L3Four ≤ A := by
    rw [← hBa]
    exact map_le_range a B
  have hr : (primeToResidual 3 (H ⧸ pCore 2 H)).map a =
      (primeToResidual 3 A).map A.subtype := by
    rw [← map_primeToResidual_of_surjective 3 a.rangeRestrict a.rangeRestrict_surjective,
      map_map]
    rfl
  rcases Matrix.PSL3Four.OuterThreeStructure.embedded_primeToResidual_eq_inner_or_diagonal
    A hA with hi | hd
  · left
    have he : K.map q = primeToResidual 3 (H ⧸ pCore 2 H) :=
      (map_injective ha) (hBa.trans (hi.symm.trans hr.symm))
    have hz : center (K ⧸ pCore 2 K) = ⊥ := by
      let _ : IsSimpleGroup (K ⧸ pCore 2 K) :=
        let _ : IsSimpleGroup L3Four := Atlas.psl_simple_high_rank 3 (by decide)
        e.isSimpleGroup
      let _ := hK.perfect
      rcases (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K)
          (center_eq_top_iff.mp ht)).elim
    let _ := hK.perfect
    let _ : IsSimpleGroup L3Four := Atlas.psl_simple_high_rank 3 (by decide)
    let _ : IsQuasisimple (K ⧸ pCore 2 K) := {
      simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        (QuotientGroup.quotientBot.trans e)).isSimpleGroup }
    apply eq_primeToResidual_of_coprime_quotient_image 3 (pCore 2 H) K _ (hK.le_primeToResidual_three hz _) he
    · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
      rw [hn]
      exact (show Nat.Coprime 3 2 by decide).pow_right n
    · rw [primeRank_congr 3 e]
      exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two
  · right
    let ea : (H ⧸ pCore 2 H) ≃* A := MonoidHom.ofInjective ha
    exact ⟨(primeToResidualEquiv 3 ea).trans
      (Matrix.PSL3Four.OuterThreeStructure.residualEquivPGL A hd)⟩


end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure
