module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims.Algebra
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims.Marking
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Separation of the J₂ and HS modified residual rows

The literal centralizer tables and the covering bound |Z(L)| ≤ 2 remain
explicit earlier inputs. Odd fixed-group index proves the central marks.
For J₂ the central model residual has order greater than 120, whereas the
covered noncentral inner residual has order at most 120. Prime seven
separates the outer row. For HS the central model residual has order at
least 3840; the covered inner product and outer elementary residuals have
orders at most 720 and 1920. Prime seven separates the symmetric outer row.

The central residuals and their full covers are proved perfect, so the
exceptional three-residual operation in Notation 16.5.5 fixes them. The
other modified residual can only be smaller. Thus the results apply to
the actual modified residuals without a family-disjointness premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.2(2),
16.1.5(8),(10), and 16.5.5–6(4), printed pp.1170,1172,1197. The proofs
require only projected order two; ambient involutivity is unnecessary.
The nonsplit extensions, their actual actions, and each component's own
covering kernel are retained. No additional ambient geometry is assumed.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open SylowSymmetry.ReverseDelta.Comparison.OtherFamilies

private theorem j2_core_index (a : MulAut Sporadic.LeechRelated.J2.Carrier)
    (hc : IsJ2CoreExtension a.fixedSubgroup) : a.fixedSubgroup.index = 315 := by
  have he := a.fixedSubgroup.card_mul_index
  rw [j2_core_card hc,
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at he
  omega

private theorem j2_product_index (a : MulAut Sporadic.LeechRelated.J2.Carrier)
    (e : a.fixedSubgroup ≃* E4 × A5) : a.fixedSubgroup.index = 2520 := by
  have he := a.fixedSubgroup.card_mul_index
  rw [Nat.card_congr e.toEquiv, j2_product_card,
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at he
  omega

private theorem hs_core_index (a : MulAut Sporadic.LeechRelated.HS.Carrier)
    (hc : IsHSCoreExtension a.fixedSubgroup) : a.fixedSubgroup.index = 5775 := by
  have he := a.fixedSubgroup.card_mul_index
  rw [HSInner.coreExtension_card hc, Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at he
  omega

private theorem hs_product_index (a : MulAut Sporadic.LeechRelated.HS.Carrier)
    (e : a.fixedSubgroup ≃* C2 × MulAut A6) : a.fixedSubgroup.index = 15400 := by
  have he := a.fixedSubgroup.card_mul_index
  rw [Nat.card_congr e.toEquiv, HSInner.ClassCoverage.product_card,
    Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at he
  omega

private theorem seven_dvd_aut_l3two : 7 ∣ Nat.card (MulAut L3Two) := by
  have hc : center Matrix.PSL3Two.PSL = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h := (centerCongr Matrix.PSL3Two.equiv).symm ⟨x, hx⟩ |>.property
    change Matrix.PSL3Two.equiv.symm x ∈ center Matrix.PSL3Two.SL at h
    have he : Matrix.PSL3Two.equiv.symm x = 1 :=
      mem_bot.mp (Matrix.PSL3Two.center_eq_bot.le h)
    exact mem_bot.mpr (Matrix.PSL3Two.equiv.symm.map_eq_one_iff.mp he)
  have hd := card_dvd_of_injective (MulAut.conj : Matrix.PSL3Two.PSL →* _)
    (conj_injective_of_center_eq_bot hc)
  rw [Matrix.PSL3Two.card_PSL] at hd
  exact dvd_trans (by norm_num : 7 ∣ 168) hd

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} [IsQuasisimple L]

/-- The odd-index marking selects the quaternion-dihedral extension in the J₂ table. -/
theorem j2_twoCentral_core
    (rows : ∀ a : MulAut Sporadic.LeechRelated.J2.Carrier,
      orderOf a = 2 → J2InvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier)
    (u : normalizer (L : Set G))
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u)) :
    IsJ2CoreExtension (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup := by
  let a := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans ((action_order u).trans hu.1)
  obtain ⟨hi, ho⟩ := (action_twoCentral_iff_model_index e u hu.1).mp hu
  rcases rows a ha with ⟨_, hc | ⟨ep⟩⟩ | ⟨hn, _⟩
  · exact hc
  · obtain ⟨ep⟩ := ep
    change Odd a.fixedSubgroup.index at ho
    rw [j2_product_index a ep] at ho
    norm_num at ho
  · exact (hn hi).elim

/-- The odd-index marking selects the quaternion-square-cyclic extension in the HS table. -/
theorem hs_twoCentral_core
    (rows : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → HSInvolutionAlternative a)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier)
    (u : normalizer (L : Set G))
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u)) :
    IsHSCoreExtension (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup := by
  let a := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans ((action_order u).trans hu.1)
  obtain ⟨hi, ho⟩ := (action_twoCentral_iff_model_index e u hu.1).mp hu
  rcases rows a ha with ⟨_, hc | ⟨ep⟩⟩ | ⟨hn, _⟩
  · exact hc
  · obtain ⟨ep⟩ := ep
    change Odd a.fixedSubgroup.index at ho
    rw [hs_product_index a ep] at ho
    norm_num at ho
  · exact (hn hi).elim

/-- Central and noncentral J₂ actions have nonisomorphic full modified residuals. The only earlier inputs are the literal universal table and the covering bound. -/
theorem j2_no_equiv
    (rows : ∀ a : MulAut Sporadic.LeechRelated.J2.Carrier,
      orderOf a = 2 → J2InvolutionAlternative a)
    (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier)
    (hZ : Nat.card (center L) ≤ 2) (u v : normalizer (L : Set G))
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  let a := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  let b := MulAut.centralQuotientAction e (L.normalizerMonoidHom v)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans ((action_order u).trans hu.1)
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans ((action_order v).trans hv2)
  have hc : IsJ2CoreExtension a.fixedSubgroup := j2_twoCentral_core rows e u hu
  have hi := ((action_twoCentral_iff_model_index e u hu.1).mp hu).1
  let : Group.IsPerfect (pResidual 2 a.fixedSubgroup) := j2_core_residual_perfect hc
  let : Group.IsPerfect (involutionTwoResidual L u.val) := full_residual_perfect hodd e u
  rcases rows b hb with ⟨hbi, hbc | ⟨ep⟩⟩ | ⟨_, ⟨eo⟩⟩
  · apply (hv ((action_twoCentral_iff_model_index e v hv2).mpr ⟨hbi, ?_⟩)).elim
    change Odd b.fixedSubgroup.index
    rw [j2_core_index b hbc]
    decide
  · obtain ⟨ep⟩ := ep
    apply no_equiv_of_perfect_size_gap hodd e u v
    have hlarge := j2_inner_core_residual_large a ha hi hc
    have hsmall := j2_product_residual_card ep
    change Nat.card (center L) * Nat.card (pResidual 2 b.fixedSubgroup) <
      Nat.card (pResidual 2 a.fixedSubgroup)
    rw [hsmall]
    have he := Nat.mul_le_mul_right 60 hZ
    omega
  · intro ⟨f⟩
    apply no_equiv_of_fixed_prime hodd e v u (by norm_num : Nat.Prime 7)
      (by norm_num : 7 ≠ 2) (by norm_num : 7 ≠ 3) ?_ ?_ ⟨f.symm⟩
    · change 7 ∣ Nat.card b.fixedSubgroup
      rw [Nat.card_congr eo.toEquiv]
      exact seven_dvd_aut_l3two
    · change ¬ 7 ∣ Nat.card a.fixedSubgroup
      rw [j2_core_card hc]
      norm_num

/-- Central and noncentral HS actions have nonisomorphic full modified residuals, including both outer rows and all covering kernels. -/
theorem hs_no_equiv
    (rows : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf a = 2 → HSInvolutionAlternative a)
    (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center L) ≤ 2) (u v : normalizer (L : Set G))
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier :=
    (MulEquiv.isSimpleGroup_congr e).mp IsQuasisimple.simple
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let a := MulAut.centralQuotientAction e (L.normalizerMonoidHom u)
  let b := MulAut.centralQuotientAction e (L.normalizerMonoidHom v)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans ((action_order u).trans hu.1)
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans ((action_order v).trans hv2)
  have hc : IsHSCoreExtension a.fixedSubgroup := hs_twoCentral_core rows e u hu
  have hi := ((action_twoCentral_iff_model_index e u hu.1).mp hu).1
  let : Group.IsPerfect (pResidual 2 a.fixedSubgroup) := hs_core_residual_perfect hc
  let : Group.IsPerfect (involutionTwoResidual L u.val) := full_residual_perfect hodd e u
  have hlarge := hs_core_residual_large a ha hi hc
  rcases rows b hb with ⟨hbi, hbc | ⟨ep⟩⟩ | ⟨_, ⟨eo⟩ | he⟩
  · apply (hv ((action_twoCentral_iff_model_index e v hv2).mpr ⟨hbi, ?_⟩)).elim
    change Odd b.fixedSubgroup.index
    rw [hs_core_index b hbc]
    decide
  · obtain ⟨ep⟩ := ep
    apply no_equiv_of_perfect_size_gap hodd e u v
    have hsmall : Nat.card (pResidual 2 b.fixedSubgroup) = 360 :=
      (Nat.card_congr (hsProductResidualEquiv ep).toEquiv).trans
        AlternatingSix.ShadowLocal.card_A6
    change Nat.card (center L) * Nat.card (pResidual 2 b.fixedSubgroup) <
      Nat.card (pResidual 2 a.fixedSubgroup)
    rw [hsmall]
    have he := Nat.mul_le_mul_right 360 hZ
    omega
  · intro ⟨f⟩
    apply no_equiv_of_fixed_prime hodd e v u (by norm_num : Nat.Prime 7)
      (by norm_num : 7 ≠ 2) (by norm_num : 7 ≠ 3) ?_ ?_ ⟨f.symm⟩
    · obtain ⟨eo⟩ := eo
      change 7 ∣ Nat.card b.fixedSubgroup
      rw [Nat.card_congr eo.toEquiv]
      norm_num [S8, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    · change ¬ 7 ∣ Nat.card a.fixedSubgroup
      rw [HSInner.coreExtension_card hc]
      norm_num
  · apply no_equiv_of_perfect_size_gap hodd e u v
    have hsmall := Nat.le_of_dvd (by decide : 0 < 960) (hs_elementary_residual_card_dvd he)
    have hbound := Nat.mul_le_mul hZ hsmall
    change Nat.card (center L) * Nat.card (pResidual 2 b.fixedSubgroup) <
      Nat.card (pResidual 2 a.fixedSubgroup)
    omega

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
