module
public import Stellmacher.SectionEight.EightFourControlledNoncentralFour
public import Stellmacher.SectionEight.EightFourFirstConfiguration
/-!
# The controlled first extraction for source (9)

Select a genuine four-element canonical support using the original quotient
witness, retaining its control of arbitrary initial-stabilizer subgroups
centralizing the opposite center. The actual exponent-two specialization of
(7.8) then supplies the same support's terminal-edge conjugator and generated
subgroup. Its core noncontainment and predecessor-core containment are kept.

The selected support is elementary as a subgroup of the initial center;
critical minimality puts it in the predecessor core, and noncentrality puts
it outside the terminal core. Thus the existing actual-involution extraction
applies without a new factor choice. The older first-configuration API is
unchanged; this theorem explicitly retains the additional source-(9) control.
Source: Stellmacher (8.4)(5),(9), Journal of Algebra 190 (1997), pp.39--40.

The local theorem uses only the stated Section Eight local hypotheses and
preserves all selected witnesses. The original canonical API is an exact
wrapper through the same graph.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_controlled_first_configuration_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let last := ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      ¬ A ≤ QAt ctx.Γ ctx.criticalPath.a' ∧ A ≤ QAt ctx.Γ last ∧
      (∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
        ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ → ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') ∧
      ∃ x : H, ∃ L0 : Subgroup H, L0 ≤ GAt ctx.Γ ctx.criticalPath.a' ∧
        L0 = A ⊔ A.conjBy x ∧ x ∈ L0 ∧
        L0 ⊔ (GAt ctx.Γ last ⊓ GAt ctx.Γ ctx.criticalPath.a') = GAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hlen := eight_four_centered_length_gt_one_local ctx hcenter
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
  obtain ⟨A, hA, hcard, hcomm, _hfixed,hcontrol⟩ := eight_four_centralizer_controlled_noncentral_four_local ctx w
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
  obtain ⟨x,A0,L0,hLP,hxP,hA0,hgen,hcardA,hx,hxsq,hA0eq,hfull,hrest⟩ :=
    sevenEight_involution_configuration_of_actor_exponent_two h Γ cp.a' last hlast
      A (hA.trans hZaLast) hnot hPhi hpow
  exact ⟨A,hA,hcard,hnot,hA.trans hZaLast,hcontrol,x,L0,hLP,hgen,hx,hfull⟩

/-- Canonical specialization through the same graph and quotient witness. -/
public theorem eight_four_controlled_first_configuration
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let last := ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      ¬ A ≤ QAt ctx.Γ ctx.criticalPath.a' ∧ A ≤ QAt ctx.Γ last ∧
      (∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
        ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ → ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') ∧
      ∃ x : H, ∃ L0 : Subgroup H, L0 ≤ GAt ctx.Γ ctx.criticalPath.a' ∧
        L0 = A ⊔ A.conjBy x ∧ x ∈ L0 ∧
        L0 ⊔ (GAt ctx.Γ last ⊓ GAt ctx.Γ ctx.criticalPath.a') = GAt ctx.Γ ctx.criticalPath.a' := by
  exact eight_four_controlled_first_configuration_local ctx.toLocalContext hcenter w

end Stellmacher.SectionEight
