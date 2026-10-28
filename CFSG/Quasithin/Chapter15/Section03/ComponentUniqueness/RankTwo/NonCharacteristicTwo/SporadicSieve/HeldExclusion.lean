module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ShadowRestrictions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.InnerReduction

/-!
# Reduction of the Held exclusion to concrete local quotient calculations

In the actual quotient I/C_I(L), the given normalizer equality makes the
specified Y⁺ normal in the whole local subgroup M_I⁺. The exponent-three
condition on Y/O₂(Y) passes to Y⁺/O₂(Y⁺) through the two-group kernel.
Consequently the full rank-two shadow forces nine to divide the order of
O₃(M_I⁺/O₂(M_I⁺)), and excludes |M_I⁺/O₂(M_I⁺)| = 72.

The Held model inspection remains to be supplied: every eligible local
subgroup in He, or in a proper almost-simple extension, must violate one
of these restrictions. The source's two-locality and maximality subject
to F*=O₂ remain in ComponentSetup. No catalogue or unconditional Held
exclusion is asserted by this module. The final conditional deduction
records exactly what the remaining model calculation must contradict.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41--42,
printed p.1138, and 1.1.5(3f), printed p.502; GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion

private theorem exponent_coreQuotient_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∀ x : A ⧸ pCore 2 A, x ^ 3 = 1) :
    ∀ x : B ⧸ pCore 2 B, x ^ 3 = 1 := by
  let a := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  intro x
  obtain ⟨y, rfl⟩ := a.surjective x
  rw [← map_pow, h, map_one]

variable {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
variable [(L.subgroupOf I).Normal]

/-- The exponent condition passes through the actual component-action quotient. -/
theorem componentY_exponent (d : ComponentSetup I L M Y S) :
    ∀ x : (componentImage I L Y) ⧸ pCore 2 (componentImage I L Y), x ^ 3 = 1 := by
  let q := centralizerQuotientMap (L.subgroupOf I)
  have hYI : Y ≤ I := d.yplus_le.trans d.component_le
  have hY : ∀ x : (Y.subgroupOf I) ⧸ pCore 2 (Y.subgroupOf I), x ^ 3 = 1 :=
    exponent_coreQuotient_of_equiv (subgroupOfEquivOfLe hYI).symm d.yplus_exponent
  obtain ⟨P, hP⟩ := d.sylow
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hZ : IsPGroup 2 (center L) := d.center_eq ▸ pCore_isPGroup
  have hk : IsPGroup 2 q.ker := component_kernel_isTwoGroup d.component_le d.join_eq hS hZ
  have hkY : IsPGroup 2 (q.subgroupMap (Y.subgroupOf I)).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (q.subgroupMap (Y.subgroupOf I)).pCoreQuotientEquiv
    (q.subgroupMap_surjective _) hkY
  change ∀ x : ((Y.subgroupOf I).map q) ⧸ pCore 2 ((Y.subgroupOf I).map q), x ^ 3 = 1
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_pow, hY, map_one]

omit [Finite G] in
/-- The normalizer equality makes Y⁺ normal in the full local subgroup. -/
theorem componentY_normal (d : ComponentSetup I L M Y S) :
    ((componentImage I L Y).subgroupOf (componentImage I L M)).Normal := by
  have hY := d.quotient_local.yplus_le.trans inf_le_left
  apply (normal_subgroupOf_iff_le_normalizer hY).mpr
  rw [componentImage_normalizer I L M Y d.component_le d.yplus_le d.theta_eq d.normalizer_eq]

/-- Necessary numerical restrictions on the actual local subgroup M_I⁺. -/
theorem componentLocal_restrictions (d : ComponentSetup I L M Y S) :
    9 ∣ Nat.card (pCore 3 ((componentImage I L M) ⧸ pCore 2 (componentImage I L M))) ∧
      Nat.card ((componentImage I L M) ⧸ pCore 2 (componentImage I L M)) ≠ 72 := by
  let N := componentImage I L M
  let X := componentImage I L Y
  let T := componentImage I L S
  have hXN : X ≤ N := d.quotient_local.yplus_le.trans inf_le_left
  have hTN : T ≤ N := d.quotient_local.sylow_le
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  let Q : Sylow 2 N := P.subtype (hP.symm ▸ hTN)
  have hQ : (Q : Subgroup N) = T.subgroupOf N := by
    change (P : Subgroup (ComponentQuotient I L)).subgroupOf N = _
    rw [hP]
  have hshadow : RankTwoShadow (X.subgroupOf N) (Q : Subgroup N) := by
    rw [hQ]
    exact rankTwoShadow_subgroupOf hXN hTN d.quotient_local.shadow
  let hn : (X.subgroupOf N).Normal := componentY_normal d
  have hexp : ∀ x : (X.subgroupOf N) ⧸ pCore 2 (X.subgroupOf N), x ^ 3 = 1 :=
    exponent_coreQuotient_of_equiv (subgroupOfEquivOfLe hXN).symm (componentY_exponent d)
  exact ⟨shadow_nine_dvd_threeCore Q (X.subgroupOf N) hshadow hexp,
    no_shadow_of_core_index_72 Q (X.subgroupOf N) hshadow⟩

omit [Finite G] in
/-- The simple component and the specified Sylow subgroup generate I/C_I(L). -/
theorem componentImage_join (d : ComponentSetup I L M Y S) :
    componentImage I L L ⊔ componentImage I L S = ⊤ := by
  let q := centralizerQuotientMap (L.subgroupOf I)
  have hS : S ≤ I := d.join_eq ▸ le_sup_right
  have hj : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
    rw [← subgroupOf_sup d.component_le hS, ← d.join_eq, subgroupOf_self]
  change (L.subgroupOf I).map q ⊔ (S.subgroupOf I).map q = ⊤
  rw [← Subgroup.map_sup, hj, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]

/-- Conditional completion from the concrete local quotient calculation.
The model-specific disjunction remains to be proved for Held and its
allowed outer extensions; this is not the unconditional Held exclusion. -/
theorem exclude_of_local_profile (d : ComponentSetup I L M Y S)
    (hprofile :
      (¬ 9 ∣ Nat.card (pCore 3 ((componentImage I L M) ⧸ pCore 2 (componentImage I L M)))) ∨
      Nat.card ((componentImage I L M) ⧸ pCore 2 (componentImage I L M)) = 72) : False := by
  obtain ⟨h9, h72⟩ := componentLocal_restrictions d
  exact hprofile.elim (fun h => h h9) h72

omit [Finite G] in
/-- Perfectness is inherited from the original quasisimple component. -/
theorem componentImage_perfect (d : ComponentSetup I L M Y S) :
    Group.IsPerfect (componentImage I L L) := by
  let : IsQuasisimple L := d.component_quasisimple
  let : Group.IsPerfect (L.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe d.component_le).symm.toMonoidHom)
      (subgroupOfEquivOfLe d.component_le).symm.surjective
  exact Group.IsPerfect.map (centralizerQuotientMap (L.subgroupOf I))

omit [Finite G] in
/-- An actual Held marking supplies both model properties from the source input. -/
theorem held_model_properties (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Held.He) : IsSimpleGroup Held.He ∧ Group.IsPerfect Held.He := by
  let : IsSimpleGroup (componentImage I L L) := d.simple_image
  let : IsQuasisimple L := d.component_quasisimple
  exact ⟨(componentModel d e).symm.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective⟩

/-- The inner Held branch assembled from the genuine catalogue and candidate
calculations. Those two model inputs remain explicit until their owners finish. -/
theorem exclude_inner_of_cover (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Held.He) (htop : componentImage I L L = ⊤)
    (heven : IsEvenCharacteristic Held.He)
    (hcover : ∃ T : Sylow 2 Held.He, ∀ N : Subgroup Held.He,
      IsMaximalTwoLocal N → (T : Subgroup Held.He) ≤ N →
      ∃ (i : Fin 3) (g : Held.He),
        N = (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (hcores : ∀ i : Fin 3, ¬ 9 ∣ Nat.card (pCore 3
      (Held.TwoLocalCandidates.subgroup i ⧸ pCore 2 (Held.TwoLocalCandidates.subgroup i)))) :
    False := by
  let a : ComponentQuotient I L ≃* componentImage I L L :=
    topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  exact (inner_local_profile_of_cover (a.trans (componentModel d e)) _ _ _ _
    d.quotient_local heven hcover hcores) (componentLocal_restrictions d).1

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion
