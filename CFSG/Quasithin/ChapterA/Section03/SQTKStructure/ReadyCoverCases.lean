module

public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupTheory.CoveringComparisonKernelCard
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.Mathieu.M22.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits

/-!
# Actual odd-center cover cases in A.3.6 and A.3.8

The known orders of PSL₃(4) and M₂₂ have three-part nine and squarefree
remaining odd part. Cyclic-Sylow transfer and the order-nine kernel bound
therefore leave at most a central group of order three when the source
component has trivial two-core. J₁ has squarefree odd part throughout,
so its source covering is injective.

For PSL₃(4), compare the constructed universal cover with the actual scalar
projection SL₃(4) → PSL₃(4). Its kernel of order three absorbs the odd part;
the remaining comparison kernel is a two-group. The existing descent theorem
then constructs SL₃(4) → L with the original commuting projection triangle.
In the nontrivial-center case this map is an isomorphism. No exceptional
two-primary multiplier or realization of a full universal kernel is used.

The component theorems conclude every clause of `A36Conclusion` for these
actual quotient models. The J₁ model deduction also supplies its exact
branch of A.3.8. All other models, the source C-component reduction and
the orbit arguments remain with the full A.3.6–A.3.9 source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.6 and A.3.8, printed pp.43–46; I.1.1–I.1.2, printed p.407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterA.SQTKStructure.ReadyCoverCases
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u v

private def quotientCover {L S : Type*} [Group L] [Group S] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* S) : PerfectCentralCovering.Cover L S where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

private theorem quotientCover_ker {L S : Type*} [Group L] [Group S] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* S) : (quotientCover e).toMonoidHom.ker = center L := by
  exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)

private def equivOfCenterCardOne {L S : Type*} [Group L] [Group S]
    (e : L ⧸ center L ≃* S) (hc : Nat.card (center L) = 1) : L ≃* S :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((eq_bot_iff_card _).mpr hc).symm).trans e)

/-- The common A.3.6 clauses for an even-order quasisimple group whose
center has order one or three. This is shared by the actual source cover cases. -/
theorem common_of_quasisimple {L : Type*} [Group L] [Finite L]
    [IsQuasisimple L] (heven : 2 ∣ Nat.card L)
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3) : A36Common L := by
  have hF : fittingSubgroup L = center L := le_antisymm
    ((le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center)
    (le_sSup ⟨inferInstance, inferInstance⟩)
  have hR : solvableRadical L = center L := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance inferInstance)
  have hO : pPrimeCore 2 L = center L := by
    apply le_antisymm
    · rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 L) with h | h
      · exact h
      · have hh := pPrimeCore_coprime_card (p := 2) (G := L)
        rw [h, card_top] at hh
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hh heven).elim
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      rcases hc with hc | hc <;> rw [hc] <;> norm_num
  have hcomm : ⁅solvableRadical L, solvableRadical L⁆ = ⊥ := by
    rw [hR]
    exact commutator_center_left _
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hq : IsQuasisimple (L ⧸ center L) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (L ⧸ center L) := hq
  have hFq : IsQuasisimple (L ⧸ fittingSubgroup L) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hF).symm
  refine ⟨hF.trans hO.symm, hFq,
    Or.inr ⟨hF, hF.trans hR.symm, by simpa only [hF] using hc⟩,
    ?_, ?_⟩
  · rw [hcomm, hF, commutator_center_left]
  · exact IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hcomm).trans QuotientGroup.quotientBot).symm

private theorem even_of_even_quotient {L S : Type*} [Group L] [Group S]
    (e : L ⧸ center L ≃* S) (hS : 2 ∣ Nat.card S) : 2 ∣ Nat.card L := by
  have h : 2 ∣ Nat.card (L ⧸ center L) := (Nat.card_congr e.toEquiv).symm ▸ hS
  exact h.trans (card_quotient_dvd_card _)

private theorem psl3_four_card (F : Type v) [Field F] [Finite F]
    (hF : Nat.card F = 4) : Nat.card PSL(3, F) = 20160 := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let eF : Matrix.PSL3Four.F ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Matrix.PSL3Four.card_F] using hF.symm)
  exact (Nat.card_congr (Atlas.fieldEquivPSL 3 eF).toEquiv).symm.trans
    Matrix.PSL3Four.card_PSL

private theorem square_not_dvd_20160 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 20160 := by
  intro hd
  have hpd : p ∣ 20160 := (show p ∣ p ^ 2 by
    simpa only [pow_one] using pow_dvd_pow p (by decide : 1 ≤ 2)).trans hd
  change p ∣ 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 at hpd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)] at hpd
  have h : p = 5 ∨ p = 7 := by omega
  rcases h with rfl | rfl <;> norm_num at hd

private theorem square_not_dvd_m22 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ Nat.card Sporadic.Mathieu.M22 := by
  intro hd
  let : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ Nat.card Sporadic.Mathieu.M22 := (show p ∣ p ^ 2 by
    simpa only [pow_one] using pow_dvd_pow p (by decide : 1 ≤ 2)).trans hd
  have h := (Sporadic.Mathieu.m22_prime_dvd_order_iff p).mp hpd
  have h' : p = 5 ∨ p = 7 ∨ p = 11 := by omega
  rw [Sporadic.Mathieu.m22_order] at hd
  rcases h' with rfl | rfl | rfl <;> norm_num at hd

private theorem square_not_dvd_janko (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ Nat.card Janko1.Model := by
  rw [Janko1.card_model]
  intro hd
  have hpd : p ∣ 175560 := (show p ∣ p ^ 2 by
    simpa only [pow_one] using pow_dvd_pow p (by decide : 1 ≤ 2)).trans hd
  change p ∣ 2 * 2 * 2 * 3 * 5 * 7 * 11 * 19 at hpd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)] at hpd
  have h : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd

/-- The source covering of J₁ is the actual quotient map, and is injective
already from the component's own trivial two-core. -/
theorem janko_quotient_injective {L : Type u} [Group L] [Finite L]
    [IsQuasisimple L] (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Janko1.Model) :
    Function.Injective (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) :=
  (quotientCover e).injective_of_squarefree_odd_part_of_pCore_eq_bot
    hcore square_not_dvd_janko

/-- The actual SL₃ scalar-cover map onto the original source group,
commuting with its specified central-quotient identification. -/
theorem exists_psl3_four_scalar_cover {L : Type u} [Group L] [Finite L]
    [IsQuasisimple L] (hcore : pCore 2 L = ⊥)
    (F : Type v) [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : L ⧸ center L ≃* PSL(3, F)) :
    ∃ k : SL(3, F) →* L, Function.Surjective k ∧
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp k =
        Matrix.PSL3.projection F := by
  let c := universalQuasisimpleCover PSL(3, F)
  let f := Matrix.PSL3.projectionCovering F
  have hcH : Covering.IsUniversal.{v,v,v} c := universalQuasisimpleCover_isUniversal _
  let a := hcH.lift f
  have ha := hcH.lift_fac f
  obtain ⟨n, hn⟩ := (PerfectCentralCovering.ofCovering c).kernel_card_dvd_two_pow_mul_three
    (by rw [psl3_four_card F hF]; norm_num)
    (by simpa only [psl3_four_card F hF] using square_not_dvd_20160)
  change Nat.card c.toMonoidHom.ker ∣ 2 ^ n * 3 at hn
  have hscalar : Nat.card f.toMonoidHom.ker = 3 := by
    change Nat.card (Matrix.PSL3.projection F).ker = 3
    rw [Matrix.PSL3.card_projectionKernel, hF]
    norm_num
  let g : Covering L PSL(3, F) := (quotientCover e).toCovering
  have hcL : Covering.IsUniversal.{v,v,u} c := universalQuasisimpleCover_isUniversal _
  obtain ⟨k, hk⟩ := hcL.exists_covering_of_kernel_card_dvd (p := 2) (r := n)
    a f ha (by simpa only [hscalar] using hn) g hcore
  exact ⟨k.toMonoidHom, k.surjective, congrArg Covering.toMonoidHom hk⟩

/-- The complete A.3.6 conclusion for an ordinary component whose actual
central quotient is PSL₃ over a four-element field. -/
theorem a36_psl3_four {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : L ⧸ center L ≃* PSL(3, F)) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hc : Nat.card (center L) ∣ 3 := by
    simpa only [quotientCover_ker] using
      (quotientCover e).kernel_card_dvd_three_of_pCore_eq_bot hcore
        (by rw [psl3_four_card F hF]; norm_num)
        (by simpa only [psl3_four_card F hF] using square_not_dvd_20160)
  have hcases := Nat.prime_three.eq_one_or_self_of_dvd _ hc
  refine ⟨?_, common_of_quasisimple
    (even_of_even_quotient e (by rw [psl3_four_card F hF]; norm_num)) hcases⟩
  rcases hcases with hc1 | hc3
  · let j := equivOfCenterCardOne e hc1
    let : IsSimpleGroup PSL(3, F) := e.symm.isSimpleGroup
    exact .simple hL j.isSimpleGroup
      (.rank_two (.linear 2 (by decide) ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩))
  · obtain ⟨k, hks, hk⟩ := exists_psl3_four_scalar_cover hcore F hF e
    have hcount := kernel_card_eq_mul_of_surjective_factor
      (Matrix.PSL3.projection F) (quotientCover e).toMonoidHom k
      (quotientCover e).surjective hks hk
    have hker : Nat.card k.ker = 1 := by
      rw [Matrix.PSL3.card_projectionKernel, hF, quotientCover_ker, hc3] at hcount
      change 3 = Nat.card k.ker * 3 at hcount
      omega
    let j : SL(3, F) ≃* L := MulEquiv.ofBijective k
      ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker), hks⟩
    have hz : Nonempty (center L ≃* Multiplicative (ZMod 3)) :=
      ⟨mulEquivOfPrimeCardEq hc3 (by simp)⟩
    exact .cover hL hz (.classical false 4
      (Or.inl ⟨2, by decide, by decide, by decide⟩)
      ⟨F, inferInstance, inferInstance, hF, ⟨j.symm⟩⟩)

/-- The complete A.3.6 conclusion for an ordinary component with actual
M₂₂ central quotient. A nontrivial center is precisely the source triple-cover predicate. -/
theorem a36_m22 {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Sporadic.Mathieu.M22) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hc : Nat.card (center L) ∣ 3 := by
    simpa only [quotientCover_ker] using
      (quotientCover e).kernel_card_dvd_three_of_pCore_eq_bot hcore
        (by rw [Sporadic.Mathieu.m22_order]; norm_num) square_not_dvd_m22
  have hcases := Nat.prime_three.eq_one_or_self_of_dvd _ hc
  refine ⟨?_, common_of_quasisimple
    (even_of_even_quotient e (by rw [Sporadic.Mathieu.m22_order]; norm_num)) hcases⟩
  rcases hcases with hc1 | hc3
  · let j := equivOfCenterCardOne e hc1
    let : IsSimpleGroup Sporadic.Mathieu.M22 := e.symm.isSimpleGroup
    exact .simple hL j.isSimpleGroup (.sporadic .m22 (by intro h; cases h) ⟨j⟩)
  · have hz : Nonempty (center L ≃* Multiplicative (ZMod 3)) :=
      ⟨mulEquivOfPrimeCardEq hc3 (by simp)⟩
    exact .cover hL hz (.mathieu ⟨inferInstance, hz, ⟨e⟩⟩)

/-- The complete A.3.6 conclusion for an ordinary component with actual
J₁ central quotient. No additional ambient two-core assumption is required. -/
theorem a36_janko {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Janko1.Model) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hi := janko_quotient_injective hcore e
  have hz : center L = ⊥ := by
    rw [← quotientCover_ker e]
    exact (quotientCover e).toMonoidHom.ker_eq_bot_iff.mpr hi
  have hc : Nat.card (center L) = 1 := by rw [hz]; simp
  let j := equivOfCenterCardOne e hc
  let : IsSimpleGroup Janko1.Model := e.symm.isSimpleGroup
  exact ⟨.simple hL j.isSimpleGroup (.janko_one ⟨j⟩),
    common_of_quasisimple
      (even_of_even_quotient e (by rw [Janko1.card_model]; norm_num)) (Or.inl hc)⟩

/-- The J₁ multiplier deduction used in A.3.8: the actual component, rather
than only its central quotient, lies in the source's four-model list. -/
theorem a38_janko_model {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Janko1.Model) :
    NonnormalCComponentModel L := by
  let : IsQuasisimple L := hL.2
  let f := quotientCover e
  exact .janko ⟨MulEquiv.ofBijective f.toMonoidHom
    ⟨janko_quotient_injective hcore e, f.surjective⟩⟩

end CFSG.Quasithin.ChapterA.SQTKStructure.ReadyCoverCases
