module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.Reduction
public import Theory.GroupTheory.AlternatingBySixteen
public import Theory.Quasithin.EvenCharacteristic

/-!
# Transporting the fixed-hexad subgroup to a component

We retain the pullback of the entire hexad stabilizer and its join with S.
The actual component Sylow lies in this pullback. The normalizer of L in S
fixes its projected involution; invariance under automorphisms fixing that
involution therefore gives invariance of the transported hexad subgroup.
No assertion that S normalizes L is made.

Source: Aschbacher–Smith 1.1.5(3)(f) and 2.3.9(7)(f), printed pp.502 and
525–526 (combined manuscript of 1 March 2004).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

/-- The whole fixed-hexad stabilizer, transported into the component. -/
noncomputable def mathieuTwentyTwoHexadSubgroup {L : Subgroup G}
    (e : L ≃* M22) (t : L) : Subgroup L :=
  (MulAction.stabilizer M22 (m22FixedPoints (e t))).comap e.toMonoidHom

/-- The same subgroup viewed in the original ambient group. -/
noncomputable def mathieuTwentyTwoHexadGroup {L : Subgroup G}
    (e : L ≃* M22) (t : L) : Subgroup G :=
  (mathieuTwentyTwoHexadSubgroup e t).map L.subtype

/-- The candidate local overgroup contains the whole supplied S. -/
noncomputable def mathieuTwentyTwoHexadOvergroup {L : Subgroup G}
    (S : Subgroup G) (e : L ≃* M22) (t : L) : Subgroup G :=
  mathieuTwentyTwoHexadGroup e t ⊔ S

/-- The intrinsic pullback is genuinely isomorphic to the model stabilizer. -/
noncomputable def mathieuTwentyTwoHexadSubgroupEquiv {L : Subgroup G}
    (e : L ≃* M22) (t : L) : mathieuTwentyTwoHexadSubgroup e t ≃*
      MulAction.stabilizer M22 (m22FixedPoints (e t)) :=
  (MulEquiv.subgroupCongr (comap_equiv_eq_map_symm' e _)).trans
    (e.symm.subgroupMap _).symm

/-- The ambient embedding also retains the full stabilizer. -/
noncomputable def mathieuTwentyTwoHexadGroupEquiv {L : Subgroup G}
    (e : L ≃* M22) (t : L) : mathieuTwentyTwoHexadGroup e t ≃*
      MulAction.stabilizer M22 (m22FixedPoints (e t)) :=
  ((mathieuTwentyTwoHexadSubgroup e t).equivMapOfInjective
    L.subtype L.subtype_injective).symm.trans (mathieuTwentyTwoHexadSubgroupEquiv e t)

/-- Joining with S keeps the candidate inside the required generated group. -/
theorem mathieuTwentyTwoHexadOvergroup_le {L : Subgroup G}
    (S : Subgroup G) (e : L ≃* M22) (t : L) :
    mathieuTwentyTwoHexadOvergroup S e t ≤ L ⊔ S :=
  sup_le_sup (map_subtype_le _) le_rfl

/-- Containment of the supplied nonidentity involution makes the two-core
nontrivial once its self-centralizing property is proved. -/
theorem mathieuTwentyTwoHexadOvergroup_mem_HeOver
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) (t : L)
    (he : mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t ∈
      Chapter1.He G) :
    mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t ∈
      Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  have hSX : (S : Subgroup H).map H.subtype ≤
      mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t :=
    le_sup_right
  refine ⟨he, ?_, hSX⟩
  change (mathieuTwentyTwoHexadOvergroup
    ((S : Subgroup H).map H.subtype) e t).pCoreIn 2 ≠ ⊥
  intro hb
  change _ ⊓ centralizer _ ≤ _ at he
  rw [hb] at he
  have hz := hSX h.mem_sylow
  have hz1 : z = 1 := he ⟨hz, by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]⟩
  simpa [hz1] using h.involution

/-- The actual component Sylow is contained in the transported hexad subgroup. -/
theorem mathieuTwentyTwo_componentSylow_le_hexad
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ((S : Subgroup H).map H.subtype).subgroupOf L ≤
      mathieuTwentyTwoHexadSubgroup e t := by
  obtain ⟨_, R, hR, _, _, hRP⟩ := mathieuTwentyTwo_projection_sylow h e ht ht2
  intro x hx
  apply hRP
  rw [hR]
  exact mem_map_of_mem e.toMonoidHom hx

/-- The authorized extension shape transports along an actual isomorphism. -/
theorem mathieuTwentyTwo_hexad_extension
    {L : Subgroup G} (e : L ≃* M22) (t : L) (ht2 : orderOf t = 2)
    (hext : ∀ B ∈ m22Blocks, AlternatingBySixteen (MulAction.stabilizer M22 B) 6) :
    AlternatingBySixteen (mathieuTwentyTwoHexadGroup e t) 6 :=
  (hext _ (m22FixedPoints_mem_blocks (e t) (by simpa using ht2))).of_equiv
    (mathieuTwentyTwoHexadGroupEquiv e t).symm

/-- Self-centralization of the model core transfers to the actual ambient subgroup. -/
theorem mathieuTwentyTwo_hexad_characteristicTwo
    {L : Subgroup G} (e : L ≃* M22) (t : L)
    (hc : centralizer
      (pCore 2 (MulAction.stabilizer M22 (m22FixedPoints (e t))) :
        Set (MulAction.stabilizer M22 (m22FixedPoints (e t)))) ≤
      pCore 2 (MulAction.stabilizer M22 (m22FixedPoints (e t)))) :
    centralizer (pCore 2 (mathieuTwentyTwoHexadGroup e t) :
      Set (mathieuTwentyTwoHexadGroup e t)) ≤ pCore 2 (mathieuTwentyTwoHexadGroup e t) :=
  (Theory.Quasithin.centralizer_pCore_le_iff 2 (mathieuTwentyTwoHexadGroupEquiv e t)).mpr hc

private theorem component_center_eq_bot {L : Subgroup G} (e : L ≃* M22) :
    center L = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center M22 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  rw [m22_center_eq_bot, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))

/-- Elements of N_S(L) fix the literal projection, even when S moves L. -/
theorem mathieuTwentyTwo_normalizer_fixes_projection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) {t : L}
    (ht : IsConjugationProjection L z t) {s : G}
    (hs : s ∈ (S : Subgroup H).map H.subtype) (hsN : s ∈ normalizer (L : Set G)) :
    L.normalizerMonoidHom ⟨s, hsN⟩ t = t := by
  let a := L.normalizerMonoidHom ⟨s, hsN⟩
  have hz : L.normalizerMonoidHom ⟨z, h.normalizes⟩ = MulAut.conj t := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact ht x
  have hc : Commute a (MulAut.conj t) := by
    rw [← hz]
    apply Commute.map _ L.normalizerMonoidHom
    exact Subtype.ext (h.central s hs)
  apply conj_injective_of_center_eq_bot (component_center_eq_bot e)
  apply MulEquiv.ext
  intro x
  have he := congrArg (fun b : MulAut L => b (a.symm x)) hc.eq
  simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply] using he

/-- An intrinsic automorphism-invariance result gives exactly the N_S(L)
invariance needed to form the component orbit of the hexad subgroup. -/
theorem mathieuTwentyTwo_hexad_normalized
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) {t : L}
    (ht : IsConjugationProjection L z t)
    (hinv : ∀ a : MulAut M22, a (e t) = e t →
      (MulAction.stabilizer M22 (m22FixedPoints (e t))).map a.toMonoidHom =
        MulAction.stabilizer M22 (m22FixedPoints (e t))) :
    ((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) ≤
      normalizer (mathieuTwentyTwoHexadGroup e t : Set G) := by
  intro s hs
  let a := L.normalizerMonoidHom ⟨s, hs.2⟩
  let b : MulAut M22 := e.symm.trans (a.trans e)
  have hb : b (e t) = e t := by
    change e (a (e.symm (e t))) = e t
    rw [e.symm_apply_apply, mathieuTwentyTwo_normalizer_fixes_projection h e ht hs.1 hs.2]
  have ha : (mathieuTwentyTwoHexadSubgroup e t).map a.toMonoidHom =
      mathieuTwentyTwoHexadSubgroup e t := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have hcomp : e.toMonoidHom.comp a.toMonoidHom =
        b.toMonoidHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (congrArg (fun y => e (a y)) (e.symm_apply_apply x)).symm
    rw [map_map, hcomp, ← map_map]
    change (((MulAction.stabilizer M22 (m22FixedPoints (e t))).comap e.toMonoidHom).map
      e.toMonoidHom).map b.toMonoidHom =
      ((MulAction.stabilizer M22 (m22FixedPoints (e t))).comap e.toMonoidHom).map e.toMonoidHom
    rw [map_comap_eq_self_of_surjective e.surjective, hinv b hb]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((mathieuTwentyTwoHexadSubgroup e t).map L.subtype).map
    (MulAut.conj s).toMonoidHom = (mathieuTwentyTwoHexadSubgroup e t).map L.subtype
  have hcomp : (MulAut.conj s).toMonoidHom.comp L.subtype =
      L.subtype.comp a.toMonoidHom := by
    ext x
    rfl
  rw [map_map, hcomp, ← map_map, ha]

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
