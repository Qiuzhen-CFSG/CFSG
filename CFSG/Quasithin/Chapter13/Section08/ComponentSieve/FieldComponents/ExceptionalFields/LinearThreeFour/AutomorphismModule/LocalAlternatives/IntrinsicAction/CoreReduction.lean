module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.MarkedBorel
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupAction.OddCommutatorImage

/-!
# Removing the two-cores from the marked SL₃(4) factors

A two-perfect marked factor lying in Z(SL)S lies in Z(SL), because its
image modulo the center is a two-group. Its order-three core quotient
then forces equality with the center. Relative normality in N(S), rather
than ambient normality in SL, puts each factor's two-core inside S.

Once the inverted factor is central, the actual cyclic action commutator
lies in Z(SL)S and contains Z(SL). Once the fixed factor is central, the
Borel fixed subgroup has these same bounds: in the other factor, a fixed
coset is both inverted and of order dividing three, so is trivial.
Taking the two-residual removes the two-part in both cases. The actor's
order is unrestricted, and the full fixed subgroup is not declared central.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004. The matrix classification that makes
one of the marked factors central is a separate obligation.
-/

public section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction

/-- The literal special linear center has order three. -/
theorem card_center : Nat.card (center SL) = 3 := by
  rw [Atlas.ExceptionalSupport.card_sl_center, sl3Field_card]
  decide

/-- The odd center has no nontrivial two-group quotient. -/
theorem center_isPPerfect : IsPPerfect 2 (center SL) := by
  apply (pResidual_eq_top_iff 2 _).mp
  apply top_unique
  intro x _
  apply mem_pResidual_of_orderOf_coprime
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (by simpa only [card_center] using (_root_.orderOf_dvd_natCard x))

/-- The embedded two-core of the order-three center is trivial. -/
theorem center_pCoreIn : (center SL).pCoreIn 2 = ⊥ := by
  have hd : Disjoint ((center SL).pCoreIn 2) (center SL) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := (isPGroup_pCoreIn 2 (center SL)).exists_card_eq
    rw [hk, card_center]
    exact (by decide : Nat.Coprime 2 3).pow_left k
  exact disjoint_self.mp (hd.mono_right (pCoreIn_le 2 _))

/-- Two-perfectness removes the Sylow two-part; the quotient order forces equality. -/
theorem factor_eq_center (A : Subgroup SL) (S : Sylow 2 SL)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (h : A ≤ center SL ⊔ (S : Subgroup SL)) : A = center SL := by
  have hle := le_normal_of_isPPerfect_of_le_sup_pGroup A (center SL) S hp S.isPGroup' h
  apply eq_of_le_of_card_ge hle
  calc
    Nat.card (center SL) = Nat.card (A ⧸ pCore 2 A) := card_center.trans hc.symm
    _ ≤ Nat.card A := Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (pCore 2 A))

/-- Relative normality in the Borel places the intrinsic factor core in its Sylow. -/
theorem factor_core_le_sylow (A : Subgroup SL) (S : Sylow 2 SL)
    (hle : A ≤ normalizer (S : Set SL))
    (hn : (A.subgroupOf (normalizer (S : Set SL))).Normal) :
    A.pCoreIn 2 ≤ (S : Subgroup SL) := by
  have hSA : (S : Subgroup SL) ≤ normalizer (A : Set SL) :=
    S.toSubgroup.le_normalizer.trans ((normal_subgroupOf_iff_le_normalizer hle).mp hn)
  have hSQ : (S : Subgroup SL) ≤ normalizer (A.pCoreIn 2 : Set SL) :=
    hSA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  exact sup_eq_right.mp (S.is_maximal'
    ((isPGroup_pCoreIn 2 A).to_sup_of_normal_left' S.isPGroup' hSQ) le_sup_right)

/-- Each factor's actual two-core is exactly its intersection with the specified Sylow. -/
theorem factor_core_eq_inf (A : Subgroup SL) (S : Sylow 2 SL)
    (hle : A ≤ normalizer (S : Set SL))
    (hn : (A.subgroupOf (normalizer (S : Set SL))).Normal) :
    A.pCoreIn 2 = A ⊓ (S : Subgroup SL) := by
  apply le_antisymm (le_inf (pCoreIn_le 2 A) (factor_core_le_sylow A S hle hn))
  apply le_pCoreIn_of_normalizes (S.isPGroup'.to_le inf_le_right) inf_le_left
  exact (le_inf A.le_normalizer hle).trans inf_normalizer_le_normalizer_inf

/-- Every subgroup between the center and its Sylow supplement has residual the center. -/
theorem residual_eq_center (D : Subgroup SL) (S : Sylow 2 SL)
    (hlo : center SL ≤ D) (hhi : D ≤ center SL ⊔ (S : Subgroup SL)) :
    (pResidual 2 D).map D.subtype = center SL := by
  have hres : (pResidual 2 (center SL)).map (center SL).subtype = center SL := by
    rw [(pResidual_eq_top_iff 2 _).mpr center_isPPerfect,
      ← MonoidHom.range_eq_map, range_subtype]
  apply le_antisymm
  · have h := embedded_pResidual_mono 2 hhi
    rwa [embedded_pResidual_join_pGroup (center SL) S center_isPPerfect S.isPGroup'
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)] at h
  · rw [← hres]
    exact embedded_pResidual_mono 2 hlo

private theorem cyclic_commutator_le_of_displacement {G : Type*} [Group G]
    (B N : Subgroup G) (α : MulAut G) (hB : B.map α.toMonoidHom = B)
    (hd : ∀ x ∈ B, x⁻¹ * α x ∈ N) : commutatorSubgroup (zpowers α) G B ≤ N := by
  have hs : B.map α.symm.toMonoidHom = B := (map_symm_eq_iff_map_eq B).mpr hB
  have hi (x : G) (hx : x ∈ B) : x⁻¹ * α.symm x ∈ N := by
    have h := N.inv_mem (hd (α.symm x) (hs.le (mem_map_of_mem _ hx)))
    simpa only [MulEquiv.apply_symm_apply, mul_inv_rev, inv_inv] using h
  rw [commutatorSubgroup, closure_le]
  rintro x ⟨β, b, hb, rfl⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp β.property
  have hp : ∀ y ∈ B, y⁻¹ * (α ^ n) y ∈ N := by
    apply zpow_induction_right (P := fun γ : MulAut G => ∀ y ∈ B, y⁻¹ * γ y ∈ N)
    · intro y _
      simpa only [MulAut.one_apply, inv_mul_cancel] using N.one_mem
    · intro γ hγ y hy
      have h := N.mul_mem (hd y hy) (hγ (α y) (hB.le (mem_map_of_mem _ hy)))
      simpa only [MulAut.mul_apply, mul_assoc, mul_inv_cancel_left] using h
    · intro γ hγ y hy
      have h := N.mul_mem (hi y hy) (hγ (α.symm y) (hs.le (mem_map_of_mem _ hy)))
      simpa only [MulAut.mul_apply, MulAut.inv_apply, mul_assoc, mul_inv_cancel_left] using h
  change b⁻¹ * β.val b ∈ N
  simpa only [hn] using hp b hb

variable {α : MulAut SL} (d : MarkedBorelFactors α)

/-- Stabilizing the specified Sylow stabilizes its full normalizer. -/
theorem borel_stable :
    (normalizer (d.sylow : Set SL)).map α.toMonoidHom = normalizer (d.sylow : Set SL) := by
  exact (map_equiv_normalizer_eq (d.sylow : Subgroup SL) α).trans
    (congrArg (fun U : Subgroup SL => normalizer (U : Set SL)) d.sylow_stable)

/-- If the inverted marked factor is central, all cyclic action commutators lie in ZS. -/
theorem graph_commutator_le (hz : d.plusFactor = center SL) :
    commutatorSubgroup (zpowers α) SL (normalizer (d.sylow : Set SL)) ≤
      center SL ⊔ (d.sylow : Subgroup SL) := by
  apply cyclic_commutator_le_of_displacement _ _ α (borel_stable d)
  intro b hb
  rw [← d.generate, hz] at hb
  obtain ⟨x, hx, z, hz, rfl⟩ := mem_sup_of_normal_right.mp hb
  have hx' := (d.zeroFactor.pCoreIn 2).inv_mem
    (d.fix_zero x⁻¹ (d.zeroFactor.inv_mem hx))
  have hδ : x⁻¹ * α x ∈ d.zeroFactor.pCoreIn 2 := by
    simpa only [map_inv, inv_inv, mul_inv_rev] using hx'
  have hδS := factor_core_le_sylow d.zeroFactor d.sylow d.zero_le d.zero_normal hδ
  have hαz : α z ∈ center SL := MulEquivClass.apply_mem_center α hz
  have hZ : center SL ≤ center SL ⊔ (d.sylow : Subgroup SL) := le_sup_left
  have hS : (d.sylow : Subgroup SL) ≤ center SL ⊔ (d.sylow : Subgroup SL) := le_sup_right
  have h := (center SL ⊔ (d.sylow : Subgroup SL)).mul_mem
    ((center SL ⊔ (d.sylow : Subgroup SL)).mul_mem
      (hZ ((center SL).inv_mem hz)) (hS hδS)) (hZ hαz)
  simpa only [map_mul, mul_inv_rev, mul_assoc] using h

/-- Inversion on the cubic center puts that actual center in the cyclic action commutator. -/
theorem graph_center_le_commutator (hz : d.plusFactor = center SL) :
    center SL ≤ commutatorSubgroup (zpowers α) SL (normalizer (d.sylow : Set SL)) := by
  intro z hzmem
  have h := d.invert_plus z (hz.symm ▸ hzmem)
  rw [hz, center_pCoreIn, mem_bot] at h
  have ha : α z = z⁻¹ := eq_inv_of_mul_eq_one_left h
  have hc : z ^ 3 = 1 := by
    have hc := pow_card_eq_one' (x := (⟨z, hzmem⟩ : center SL))
    rw [card_center] at hc
    exact congrArg Subtype.val hc
  have he : z⁻¹ * α z = z := by
    rw [ha, ← mul_inv_rev]
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hc
  rw [← he]
  exact Theory.GroupAction.OddCommutatorImage.generator_displacement_mem _ α
    ⟨z, center_le_normalizer _ hzmem⟩

/-- The graph branch has central two-residual of the actual cyclic action commutator. -/
theorem graph_residual (hz : d.plusFactor = center SL) :
    let C := commutatorSubgroup (zpowers α) SL (normalizer (d.sylow : Set SL))
    (pResidual 2 C).map C.subtype = center SL :=
  residual_eq_center _ d.sylow (graph_center_le_commutator d hz) (graph_commutator_le d hz)

/-- If the fixed marked factor is central, the actor fixes the entire center. -/
theorem graphField_center_fixed (hz : d.zeroFactor = center SL) :
    center SL ≤ α.fixedSubgroup := by
  intro z hzmem
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  have h := d.fix_zero z (hz.symm ▸ hzmem)
  rw [hz, center_pCoreIn, mem_bot] at h
  exact mul_inv_eq_one.mp h

/-- The fixed Borel retains only the central quotient line and a possible two-part. -/
theorem graphField_fixed_le (hz : d.zeroFactor = center SL) :
    normalizer (d.sylow : Set SL) ⊓ α.fixedSubgroup ≤
      center SL ⊔ (d.sylow : Subgroup SL) := by
  rintro b ⟨hb, hfix⟩
  rw [← d.generate, hz] at hb
  obtain ⟨z, hzmem, x, hx, rfl⟩ := mem_sup_of_normal_left.mp hb
  have hzfix := (MulAut.mem_fixedSubgroup _ _).mp (graphField_center_fixed d hz hzmem)
  have hxfix : α x = x := by
    have he := (MulAut.mem_fixedSubgroup _ _).mp hfix
    rw [map_mul, hzfix] at he
    exact mul_left_cancel he
  have h2 := d.invert_plus x hx
  rw [hxfix] at h2
  let q := QuotientGroup.mk' (pCore 2 d.plusFactor)
  let a : d.plusFactor := ⟨x, hx⟩
  have hqa2 : q a ^ 2 = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (a ^ 2)).mpr
    obtain ⟨y, hy, he⟩ := h2
    have hya : y = a ^ 2 := Subtype.ext (by simpa only [subtype_apply, pow_two, coe_mul, a] using he)
    exact hya ▸ hy
  have hqa3 : q a ^ 3 = 1 := by
    have he := pow_card_eq_one' (x := q a)
    rwa [d.plus_quotient_card] at he
  have hqa : q a = 1 := by
    calc
      q a = q a ^ 2 * q a := by rw [hqa2, one_mul]
      _ = q a ^ 3 := (pow_succ _ 2).symm
      _ = 1 := hqa3
  have hxcore : x ∈ d.plusFactor.pCoreIn 2 :=
    mem_map.mpr ⟨a, (QuotientGroup.eq_one_iff a).mp hqa, rfl⟩
  exact mul_mem_sup hzmem
    (factor_core_le_sylow d.plusFactor d.sylow d.plus_le d.plus_normal hxcore)

/-- The graph-field branch has central fixed-subgroup two-residual. -/
theorem graphField_residual (hz : d.zeroFactor = center SL) :
    let C := normalizer (d.sylow : Set SL) ⊓ α.fixedSubgroup
    (pResidual 2 C).map C.subtype = center SL :=
  residual_eq_center _ d.sylow (le_inf (center_le_normalizer _) (graphField_center_fixed d hz))
    (graphField_fixed_le d hz)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction
