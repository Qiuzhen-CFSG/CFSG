module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeDoubledBaumann
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64ThompsonPlacement
public import Stellmacher.BaumannMap

/-!
# An actual Baumann-normalizer overgroup of the original Sylow

The full-core action identifies the component part of the Baumann normalizer
with a marked parabolic. Its intersection with the original join is therefore
proper and has a cubic factor beyond T. Its enlargement by N_G(T1) normalizes
the actual Baumann subgroup, so its two-core contains the full rank12 movement.
The identification with one of the original maximal parabolics is not assumed.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem map_normalizer {A B : Type*} [Group A] [Group B]
    (F : Subgroup A) (f : A →* B) (hf : Function.Injective f) :
    (normalizer (F : Set A)).map f = f.range ⊓ normalizer (F.map f : Set B) := by
  apply le_antisymm (le_inf (map_le_range _ _) (le_normalizer_map f))
  rintro _ ⟨⟨x,rfl⟩,hx⟩
  refine ⟨x,?_,rfl⟩
  have he : (normalizer (F.map f : Set B)).comap f = normalizer (F : Set A) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf]
  exact he ▸ hx

/-- The literal proper source overgroup and its actual enlargement retain
both the cubic component part and the full rank12 movement. -/
theorem normalizerEscape_fullCore64_baumann_overgroup
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
    let H := localJoin T L ⊓ normalizer (ChapterB.baumann T₁ : Set G)
    (T : Subgroup G) ≤ H ∧ H < localJoin T L ∧ 3 ∣ Nat.card (L ⊓ H : Subgroup G) ∧
      ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ ≤
        (normalizer (T₁ : Set G) ⊔ H).pCoreIn 2 := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := L ⊔ T₁
  let A := L.subgroupOf J
  let R := T₁.subgroupOf J
  let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
  have hCcard : Nat.card (commutatorCore A) = 64 := by
    change Nat.card ((commutatorCore A).map J.subtype) = 64 at hcard
    simpa only [card_map_of_injective J.subtype_injective] using hcard
  obtain ⟨m,hm,⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  have hm2 : m = 2 := by
    rcases hm with hm | hm
    · have hb := (h.abelianCore_fixedKernel_bounds hc (Or.inl hm) q).1
      have he := q.card
      rw [hm] at he
      change Nat.card (commutatorCore A) = 2^(3*1) * Nat.card (coreFixed A) at he
      rw [hCcard] at he
      change Nat.card (coreFixed A) ≤ 2 at hb
      norm_num at he
      omega
    · exact hm
  subst m
  have hz : coreFixed A = ⊥ :=
    (eq_bot_iff_card _).mpr (h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q)
  have hi : Function.Injective q.projection :=
    (MonoidHom.ker_eq_bot_iff q.projection).mp (q.kernel.trans hz)
  obtain ⟨P,hP⟩ := halfSylow_sylow_component_join D (selected_nonnormal s)
  have hPR : (P : Subgroup J) = R := by
    apply map_injective J.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  obtain ⟨d⟩ := h.exists_doubledCoreAction hc q hi P hPR.symm.le
  let B := ChapterB.baumann T₁
  let I := A ⊓ normalizer (ChapterB.baumann R : Set J)
  let H := localJoin T L ⊓ normalizer (B : Set G)
  let E := normalizer (T₁ : Set G) ⊔ H
  have hR : R.map J.subtype = T₁ := map_subgroupOf_eq_of_le le_sup_right
  have hB : (ChapterB.baumann R).map J.subtype = B := by
    change (R ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set J)).map
      J.subtype = _
    rw [baumann_map_injective J.subtype J.subtype_injective,hR]
    rfl
  have hI : I.map J.subtype = L ⊓ normalizer (B : Set G) := by
    rw [show I = A ⊓ normalizer (ChapterB.baumann R : Set J) from rfl,
      map_inf _ _ _ J.subtype_injective,map_normalizer _ _ J.subtype_injective,
      hB,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),range_subtype]
    exact (inf_assoc L J _).symm.trans (congrArg (fun K => K ⊓ normalizer (B : Set G))
      (inf_eq_left.mpr le_sup_left))
  have himage := d.baumann_normalizer_image hc hPR.symm
  have hsize : Nat.card (I.map d.actor) = 24 := by
    rw [himage,card_map_of_injective BinaryLinearThree.DoubledOffenders.δ_injective,
      card_map_of_injective (MulAut.conj d.frame).injective,
      Matrix.PSL3Two.card_lineParabolicSL]
  have h3 : 3 ∣ Nat.card (L ⊓ normalizer (B : Set G) : Subgroup G) := by
    rw [←hI,card_map_of_injective J.subtype_injective]
    exact (show 3 ∣ Nat.card (I.map d.actor) by rw [hsize]; decide).trans
      (card_map_dvd I d.actor)
  have hnot : ¬ L ≤ normalizer (B : Set G) := by
    intro hn
    have he : I = A := by
      apply map_injective J.subtype_injective
      rw [hI,inf_eq_left.mpr hn,map_subgroupOf_eq_of_le le_sup_left]
    have hcomp : A.map d.actor = BinaryLinearThree.DoubledOffenders.δ.range := by
      apply le_antisymm
      · rintro _ ⟨a,ha,rfl⟩
        exact ⟨_,(d.component ⟨a,ha⟩).symm⟩
      · rintro _ ⟨g,rfl⟩
        obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (pCore 2 A) (q.quotientEquiv.symm g)
        refine ⟨a,a.property,?_⟩
        rw [d.component,ha,MulEquiv.apply_symm_apply]
    rw [he,hcomp] at hsize
    have h168 : Nat.card BinaryLinearThree.DoubledOffenders.δ.range = 168 := by
      rw [MonoidHom.range_eq_map,card_map_of_injective
        BinaryLinearThree.DoubledOffenders.δ_injective,card_top,Matrix.PSL3Two.card_SL]
    omega
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (Parabolics.stabilizer_normalized D (selected_nonnormal s)).trans
      (normalizer_le_normalizer_baumann T₁)
  have hLH : L ⊓ H = L ⊓ normalizer (B : Set G) := by
    exact (inf_assoc L (localJoin T L) _).symm.trans (congrArg
      (fun K => K ⊓ normalizer (B : Set G))
      (inf_eq_left.mpr ((le_componentOrbit L T).trans le_sup_left)))
  refine ⟨le_inf le_sup_right hTB,lt_of_le_of_ne inf_le_left ?_,hLH.symm ▸ h3,?_⟩
  · intro he
    exact hnot (((le_componentOrbit L T).trans le_sup_left).trans (he ▸ inf_le_right))
  · have hBE : B ≤ E :=
      (show B ≤ T₁ from inf_le_left).trans (T₁.le_normalizer.trans le_sup_left)
    have hEN : E ≤ normalizer (B : Set G) :=
      sup_le (normalizer_le_normalizer_baumann T₁) inf_le_right
    have hBp : IsPGroup 2 B := T.isPGroup'.to_le
      ((show B ≤ T₁ from inf_le_left).trans inf_le_left)
    exact ((normalizerEscape_fullCore64_thompson_placement D s hout hc hcard).1.trans
      (ChapterB.elementaryAbelianMaxJ_le_baumann T₁)).trans
      (le_pCoreIn_of_normalizes hBp hBE hEN)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
