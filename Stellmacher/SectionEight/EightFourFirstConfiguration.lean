module
public import Stellmacher.SectionEight.EightFourNoncentralFour
public import Stellmacher.SectionEight.EightFourFixedClosureControl
public import Stellmacher.SectionFiveToSeven.Result7_8.InvolutionConfiguration

/-!
# The first terminal-edge configuration in Stellmacher (8.4)

For a noncommuting critical pair whose first-step center is central, choose
a four-element initial-center factor that fails to centralize the opposite
center. At the terminal/penultimate edge, this gives source (5)'s actual
conjugator and generated subgroup. The theorem retains the stronger proved
(7.8) coatom, quotient, swapping-involution, generation, and residual
commutator assertions for the same selected subgroup and conjugator.
The repository's `conjugateBy A x` uses left conjugation; the matching
transported penultimate vertex is therefore `Γ.act x⁻¹ last`.

Centrality excludes length one. Critical minimality puts the initial center
in the penultimate core. On the other hand, (7.4)'s Sylow-centralizer equality
shows the terminal core centralizes the terminal center, so the selected
factor is outside that core. The factor is elementary as a subgroup of the
initial center; its Frattini subgroup is therefore trivial. Apply the proved
exponent-two-actor specialization of (7.8) to these exact edge data. Its
involutions are actual group elements, not merely quotient involutions.

This result is one configuration in the remaining normality argument, not
that argument's final contradiction. Source: Stellmacher, Journal of Algebra
190 (1997), (8.4), printed p.39 (5), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- Source (5), with the selected four-element actor and the full actual-involution configuration. -/
public theorem eight_four_first_configuration
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    let last := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      IsElementaryAbelian 2 A ∧ ¬ A ≤ QAt ctx.Γ ctx.criticalPath.a' ∧
      A ≤ QAt ctx.Γ last ∧
      ∃ x : H, ∃ A₀ L : Subgroup H, L ≤ GAt ctx.Γ ctx.criticalPath.a' ∧
        x ∈ GAt ctx.Γ ctx.criticalPath.a' ∧ A₀ ≤ A ∧
        L = A ⊔ conjugateBy A x ∧
        Nat.card A = 2 * Nat.card A₀ ∧
        x ∈ L ∧ x ^ 2 ∈ QAt ctx.Γ ctx.criticalPath.a' ∧
        A₀ = A ⊓ twoCoreIn L ∧
        L ⊔ (GAt ctx.Γ last ⊓ GAt ctx.Γ ctx.criticalPath.a') =
          GAt ctx.Γ ctx.criticalPath.a' ∧
        Nonempty (QuotientDihedralProduct L (QAt ctx.Γ ctx.criticalPath.a') A₀) ∧
        (∀ Z₁ Z₂ : Subgroup H,
          Z₁ ∈ conjugateSubgroupOrbit (ZAt ctx.Γ last) L →
          Z₂ ∈ conjugateSubgroupOrbit (ZAt ctx.Γ last) L →
          ∃ t : L, _root_.IsInvolution (t : H) ∧
            Z₁.conjBy (t : H) = Z₂ ∧ Z₂.conjBy (t : H) = Z₁) ∧
        (∀ b : H, b ∈ A → b ∉ A₀ →
          L = Subgroup.closure ({b} : Set H) ⊔ conjugateBy A x) ∧
        twoResidualIn L ≤ ⁅twoResidualIn L, QAt ctx.Γ last⁆ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hlen := eight_four_centered_length_gt_one ctx hcenter
  change 1 < cp.length at hlen
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := Fin.ext (by simp; omega)
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast : last ∈ neighborhood Γ cp.a' :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  obtain ⟨A, hA, hcard, hcomm⟩ := eight_four_noncentral_four ctx
  have hpow : ∀ a : H, a ∈ A → a ^ 2 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (A := z Γ cp.a) a (hA ha)
  have helem : IsElementaryAbelian 2 A := by
    refine {
      toIsMulCommutative := ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      exponent_dvd_p := ?_ }
    · exact congrArg (fun z : z Γ cp.a => (z : H))
        ((IsMulCommutative.is_comm (M := z Γ cp.a)).comm
          ⟨x, hA x.property⟩ ⟨y, hA y.property⟩)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      exact Subtype.ext (hpow x x.property)
  let := helem
  let : Fact (IsPGroup 2 A) := ⟨IsElementaryAbelian.isPGroup 2 A⟩
  have hPhi : frattiniAmbient A ≤ q Γ cp.a' := by
    rw [frattiniAmbient, frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
    exact bot_le
  have hnot : ¬ A ≤ q Γ cp.a' := by
    intro hAQ
    apply hcomm
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    apply hAQ.trans
    rw [← ((lemma_seven_four h Γ cp).commutator_case ctx.commutator_ne).1 default]
    exact inf_le_right
  have hZaLast : z Γ cp.a ≤ q Γ last := by
    apply SevenSix.critical_minimality Γ cp
    have hd := SevenSix.path_distance_le Γ cp 0 (cp.length - 1) (by omega) (by omega)
    have hbound : Γ.distance cp.a last ≤ cp.length - 1 := by
      simpa [last, cp.path_start] using hd
    omega
  exact ⟨A, hA, hcard, helem, hnot, hA.trans hZaLast,
    sevenEight_involution_configuration_of_actor_exponent_two h Γ cp.a' last hlast
      A (hA.trans hZaLast) hnot hPhi hpow⟩

end Stellmacher.SectionEight
