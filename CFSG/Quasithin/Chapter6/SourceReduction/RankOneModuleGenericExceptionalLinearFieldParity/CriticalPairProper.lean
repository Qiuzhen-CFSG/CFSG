module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.CriticalPairCentralized
public import Theory.GroupTheory.SylowCentralizerObstruction
public import Theory.GroupTheory.AbelianCommutatorIndex

/-!
# The proper-centralizer critical-pair case in the parity proof

A two-subgroup fixing a nonidentity element of a global TI point normalizes
that point. As the point lies in a Sylow center, Sylow conjugacy makes the
two-subgroup centralize the whole point. Apply this to D_H and an endpoint
point moved by D_H. Its intersection with O₂(H₁) is trivial, since that
intersection centralizes D_H. It embeds in H₁/O₂(H₁), giving n ≤ 4.

For each endpoint actor y, the commutator map D_H → A₁ has kernel C_D_H(y).
Thus |D_H:C_D_H(y)| ≤ |A₁| = 2ⁿ. The already proved opposite-core index
|U:D_H| ≤ 16 bounds displacement on the original U/Z₁ by n+4. Oddness gives
n ≤ 3, and hence the required mover has displacement at most seven. This
uses the existing index bound directly, without reversing the critical path
or assuming an additional natural-module normalizer calculation.

Together with CriticalPairCentralized this proves CriticalSource. The Seed
and LargeDisplacement premises still require their independent source proofs
inside the parity assembly owner qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.17, printed pp.641–642 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L H A : Subgroup G} {n : ℕ}

/-- Two-subgroups fixing a nonidentity point centralize its whole TI conjugate. -/
theorem Seed.twoGroup_centralizes_point_of_fixed
    (s : Seed T L H A n) (P : Subgroup G) (hP : IsPGroup 2 P)
    (a x : G) (hx : x ∈ (setup T L s.V H A).V₁.map (MulAut.conj a).toMonoidHom)
    (hx1 : x ≠ 1) (hc : P ≤ centralizer ({x} : Set G)) :
    P ≤ centralizer ((setup T L s.V H A).V₁.map (MulAut.conj a).toMonoidHom : Set G) := by
  let E := setup T L s.V H A
  let e := MulAut.conj a
  have hnormal := (s.point_isTI.map_equiv e).centralizer_le_normalizer hx hx1
  have hPnormal : P.map e.symm.toMonoidHom ≤ normalizer (E.V₁ : Set G) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := mem_normalizer_iff_map_conj_eq.mp (hnormal (hc hq))
    have hh' := congrArg (fun X : Subgroup G => X.map e.symm.toMonoidHom) hh
    have he : e.symm.toMonoidHom = (MulAut.conj a⁻¹).toMonoidHom := by
      ext z
      simp [e]
    rw [he] at hh'
    change ((E.V₁.conjBy a).conjBy q).conjBy a⁻¹ = (E.V₁.conjBy a).conjBy a⁻¹ at hh'
    rw [← conjBy_mul, ← conjBy_mul, ← conjBy_mul] at hh'
    change E.V₁.conjBy (e.symm.toMonoidHom q) = E.V₁
    rw [he]
    simpa only [inv_mul_cancel, conjBy_one, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc] using hh'
  have hT : (T : Subgroup G) ≤ centralizer (E.V₁ : Set G) := by
    intro t ht z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht |>.symm
  have hh := T.normalizing_pSubgroup_le_centralizer E.V₁ (P.map e.symm.toMonoidHom)
    hT (hP.map _) hPnormal
  have hm := (map_mono (f := e.toMonoidHom) hh).trans
    (map_centralizer_le_centralizer_image (E.V₁ : Set G) e.toMonoidHom)
  simpa [map_map, e] using hm

/-- In the proper branch a point moved by DH embeds in the original quotient. -/
theorem Seed.proper_exponent_le_four
    (s : Seed T L H A n) (C : s.f8.CriticalPath)
    (hlarge : LargeDisplacement (setup T L s.V H A)) : n ≤ 4 := by
  let E := setup T L s.V H A
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  have hDH : IsPGroup 2 C.DH :=
    (IsElementaryAbelian.isPGroup 2 E.U).to_le (commutatorPreimage_le _ _ _)
  have hspan : C.Ug = ⨆ (b : E.H) (l : L),
      E.V₁.map (MulAut.conj ((C.g : G)*b*l)).toMonoidHom := by
    change (conjugateSpanBy s.V E.H).map _ = _
    conv_lhs => arg 2; arg 1; rw [← s.point_span]
    rw [conjugateSpanBy_eq_iSup_conj, Subgroup.map_iSup]
    congr 1
    funext b
    rw [conjugateSpanBy_eq_iSup_conj, Subgroup.map_iSup, Subgroup.map_iSup]
    congr 1
    funext l
    change ((E.V₁.conjBy l).conjBy b).conjBy C.g = _
    rw [← conjBy_mul, ← conjBy_mul]
    rfl
  have hm : ∃ (b : E.H) (l : L), ¬ C.DH ≤ centralizer
      (E.V₁.map (MulAut.conj ((C.g : G)*b*l)).toMonoidHom : Set G) := by
    by_contra! hh
    apply s.critical_kernels_do_not_centralize C hlarge
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rw [hspan]
    exact iSup_le fun b => iSup_le fun l => le_centralizer_iff.mp (hh b l)
  obtain ⟨b,l,hm⟩ := hm
  let a : G := (C.g : G)*b*l
  let W := E.V₁.map (MulAut.conj a).toMonoidHom
  have hWU : W ≤ C.Ug := by rw [hspan]; exact le_iSup_of_le b (le_iSup_of_le l le_rfl)
  have hd : W ⊓ E.QH = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    by_contra hx1
    have hxc : x ∈ centralizer (C.DH : Set G) := kernel_intersection_centralizes C W hWU hx
    apply hm
    exact s.twoGroup_centralizes_point_of_fixed C.DH hDH a x hx.1 hx1
      (by intro d hd; exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc d hd))
  let : IsElementaryAbelian 2 E.V₁ := IsElementaryAbelian.of_injective
    (inclusion (point_le_span s.f8)) (inclusion_injective _)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hi := quotient_image_index_le W (hWU.trans C.Ug_le_H)
  rw [← inf_relIndex_right, inf_comm, hd, relIndex_bot_left,
    card_map_of_injective (MulAut.conj a).injective, s.point_card] at hi
  have hp : 2^n ≤ 2^4 := hi.trans (Nat.pow_le_pow_right (by decide) s.quotient_rank)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

/-- Every endpoint actor has displacement at most four plus the point exponent. -/
theorem Seed.endpoint_displacement_le
    (s : Seed T L H A n) (C : s.f8.CriticalPath)
    (y : G) (hy : y ∈ C.Ug) : displacement (setup T L s.V H A) y ≤ n + 4 := by
  let E := setup T L s.V H A
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  have hDU : C.DH ≤ E.U := commutatorPreimage_le _ _ _
  have hc : ⁅C.DH,C.Ug⁆ ≤ C.A₁ := by
    rw [commutator_comm]
    exact C.centralizer_commutators.1
  have hr := centralizer_relIndex_le_card_of_abelian_commutator C.DH E.U C.A₁
    hDU y (C.normalizes_U hy) (fun x hx =>
      hc (commutator_mem_commutator hx hy))
  have hrow : (centralizer ({y} : Set G)).relIndex C.DH ≤ 2^n := by
    change (centralizer ({y} : Set G)).relIndex C.DH ≤
      Nat.card (E.V₁.map (MulAut.conj (C.g : G)).toMonoidHom) at hr
    rw [card_map_of_injective (MulAut.conj (C.g : G)).injective, s.point_card] at hr
    exact hr
  have ht := relIndex_inf_mul_relIndex (centralizer ({y} : Set G)) C.DH E.U
  rw [inf_eq_left.mpr hDU] at ht
  have hbound : (centralizer ({y} : Set G)).relIndex E.U ≤ 2^(n+4) := by
    calc
      _ ≤ (centralizer ({y} : Set G) ⊓ C.DH).relIndex E.U :=
        relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
      _ = (centralizer ({y} : Set G)).relIndex C.DH * C.DH.relIndex E.U := ht.symm
      _ ≤ 2^n * 16 := Nat.mul_le_mul hrow (s.critical_indices_le_sixteen C).2
      _ = _ := by rw [pow_add]; rfl
  have hfix : E.U ⊓ centralizer ({y} : Set G) ≤
      commutatorPreimage E.U (zpowers y) E.V₁ := by
    apply le_commutatorPreimage inf_le_left
    have he : ⁅E.U ⊓ centralizer ({y} : Set G), zpowers y⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [zpowers_eq_closure, centralizer_closure]
      exact inf_le_right
    exact he.le.trans bot_le
  have hi := relIndex_le_of_le_left hfix
    (show (E.U ⊓ centralizer ({y} : Set G)).relIndex E.U ≠ 0 from index_ne_zero_of_finite)
  rw [inf_relIndex_left] at hi
  have hl := Nat.log_mono_right (b := 2) (hi.trans hbound)
  simpa only [displacement, Nat.log_pow (by decide : 1 < 2)] using hl

/-- The proper-centralizer branch produces a mover on the literal U/Z₁. -/
theorem Seed.smallMover_of_odd_large_displacement
    (s : Seed T L H A n) (hodd : Odd n)
    (hlarge : LargeDisplacement (setup T L s.V H A)) :
    SmallMover (setup T L s.V H A) := by
  let E := setup T L s.V H A
  obtain ⟨C⟩ := s.f8.exists_criticalPath
  have hn := s.proper_exponent_le_four C hlarge
  have hn3 : n ≤ 3 := by obtain ⟨k,hk⟩ := hodd; omega
  have hnot : ¬ C.Ug ≤ E.QH := by
    intro hle
    apply s.critical_centralizer_ne_span C hlarge
    rw [Dg_eq_core_intersection C, inf_eq_right.mpr hle]
  obtain ⟨y,hy,hyQ⟩ := SetLike.not_le_iff_exists.mp hnot
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  let : IsElementaryAbelian 2 C.Ug := IsElementaryAbelian.map _
  have hy2 : y^2 ∈ E.QH := by
    rw [elemPow_eq_one_of_isElementaryAbelian y hy]
    exact E.QH.one_mem
  have hb := s.endpoint_displacement_le C y hy
  exact ⟨y,C.Ug_le_H hy,hy2,hyQ,by omega⟩

/-- Both terminal F.8 branches, with no additional local callback. -/
theorem criticalSource (T : Sylow 2 G) (L H : Subgroup G) (n : ℕ) :
    CriticalSource T L H n := by
  intro A _B _c hodd s hlarge
  exact s.smallMover_of_odd_large_displacement hodd hlarge

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
