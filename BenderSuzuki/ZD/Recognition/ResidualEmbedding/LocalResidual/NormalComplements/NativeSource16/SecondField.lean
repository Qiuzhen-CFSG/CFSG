module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.FieldSource

/-!
# The second field circle forced by four-centralizer generation

For a marked four-group W containing u, the residual generation theorem
forces one nonidentity w in W to have a marked root not centralized by u.
That w differs from u. Conjugation by u on its nonsolvable circle therefore
has the square-field structure. This proves the source's replacement of v
by uv without assuming either resulting model or any commutation conclusion.

Source: GLS IV, Chapter 2, Proposition 16.5, equation (16H).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem square_field_of_noncentral_local_root
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) {z t v : G}
    (hz : z ∈ Z) (hzF : z ∈ F) (hzM : z ∈ M)
    (ht : t ∈ Z) (htF : t ∈ F) (htM : t ∉ M)
    (hns : ¬ Group.IsSolvable (localCircle Z F))
    (hv : PFAppendixIII.IsInvolution v) (hvF : v ∈ F) (hvM : v ∈ M)
    (hzv : Commute z v) (htv : Commute t v)
    (hnot : ¬ localCircleIn Z (F ⊓ M) ⊔ zpowers t ≤ centralizer ({v} : Set G)) :
    ∃ (hFM : ¬ F ≤ M) (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M),
      let a := source16_circleAction h.disconnected F hFM hne ⟨v,hvF⟩
      ∃ m : ℕ, 0 < m ∧
        Nonempty (localCircle Z F ≃* PSL2BinaryMatrixGroup (2 * m)) ∧
        Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) := by
  let C := localCircle Z F
  let f := localCircleHom Z F
  have hf := localCircleHom_injective Z F
  have hFM : ¬ F ≤ M := fun hh => htM (hh htF)
  have hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M := ⟨z,hz,hzF,hzM⟩
  refine ⟨hFM,hne,?_⟩
  let ρ := source16_circleAction h.disconnected F hFM hne
  let vF : F := ⟨v,hvF⟩
  let a := ρ vF
  have hav (x : C) : f (a x) = v * f x * v⁻¹ := rfl
  have ha2 : a ^ 2 = 1 := by
    change (ρ vF) ^ 2 = 1
    rw [← map_pow, show vF ^ 2 = 1 from Subtype.ext hv.sq_eq_one, map_one]
  let zC : C := ⟨⟨z,hzF⟩,subset_closure hz⟩
  let tC : C := ⟨⟨t,htF⟩,subset_closure ht⟩
  have haz : a zC = zC := hf (by rw [hav]; exact mul_inv_eq_iff_eq_mul.mpr hzv.symm.eq)
  have hat : a tC = tC := hf (by rw [hav]; exact mul_inv_eq_iff_eq_mul.mpr htv.symm.eq)
  obtain ⟨hc,hperfect,hm,_⟩ := localCircle_nonsolvable_structure h r ha F hF hFM hne hns
  obtain ⟨n,hn,hmodel⟩ := hm.exists_exponent
  have hodd : Odd (Nat.card (center C)) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  obtain ⟨P,hP,hmark⟩ := localCircle_exists_marked_sylow h r ha F hF hFM hne hns
  have hzC : PFAppendixIII.IsInvolution zC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions z hz) hzF) _
  have htC : PFAppendixIII.IsInvolution tC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions t ht) htF) _
  have htNP : tC ∉ normalizer (P : Set C) := by rw [← hP]; exact htM
  have haNP : (normalizer (P : Set C)).map a.toMonoidHom = normalizer (P : Set C) := by
    rw [← hP]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change f (a x) ∈ M
      rw [hav]
      exact M.mul_mem (M.mul_mem hvM hx) (M.inv_mem hvM)
    · intro x hx
      refine ⟨a x,?_,?_⟩
      · change f (a x) ∈ M
        rw [hav]
        exact M.mul_mem (M.mul_mem hvM hx) (M.inv_mem hvM)
      · change a (a x) = x
        have hh := DFunLike.congr_fun ha2 x
        simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hroot := localCircle_rootGenerated_map_eq h r F hF hFM hne P hP hmark ht htF
  have hnot' : ¬ rootGenerated (P : Subgroup C) tC ≤ a.fixedSubgroup := by
    intro hfix
    apply hnot
    intro x hx
    rw [← hroot] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have he := congrArg f ((MulAut.mem_fixedSubgroup a y).mp (hfix hy))
    rw [hav] at he
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨e,_,m,hmpos,hnm,hfixed,_⟩ := source16_square_field_of_nontrivial_root_action hn
    hperfect hodd hmodel P (hmark zC hz hzM) hzC htC htNP a ha2 haz hat haNP hnot'
  exact ⟨m,hmpos,⟨hnm ▸ e⟩,hfixed⟩

/-- Four-centralizer generation selects the second genuine field circle.
Both circle equivalences are derived; W is the source four-subgroup witness. -/
public theorem source16_exists_second_square_field_circle
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (hzu : Commute z u) (htu : Commute t u)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t)
    (hWz : W ≤ centralizer ({z} : Set G)) (hWt : W ≤ centralizer ({t} : Set G))
    (huW : u ∈ W) :
    ∃ w ∈ W, PFAppendixIII.IsInvolution w ∧ w ≠ u ∧
      let B := centralizer ({w} : Set G)
      ∃ (huB : u ∈ B) (hBM : ¬ B ≤ M) (hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M),
        let a := source16_circleAction h.disconnected B hBM hne ⟨u,huB⟩
        ∃ m : ℕ, 0 < m ∧
          Nonempty (localCircle Z B ≃* PSL2BinaryMatrixGroup (2 * m)) ∧
          Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) := by
  classical
  have hnotK := residualCommutator_not_le_involution_centralizer
    h.disconnected r hg hz hzM ht htM hu hzu htu
  have hex : ∃ w : W, w ≠ 1 ∧
      ¬ closure (residualCentralizerTrace Z M w) ⊔ zpowers t ≤ centralizer ({u} : Set G) := by
    by_contra hnone
    push Not at hnone
    apply hnotK
    rw [residualPair_four_generation h.disconnected ht htM W hW hWD hWt]
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    have hwi : PFAppendixIII.IsInvolution (w : G) :=
      ⟨hw,elemPow_eq_one_of_isElementaryAbelian (w : G) w.property⟩
    have hzw : Commute z (w : G) := (mem_centralizer_singleton_iff.mp (hWz w.property)).symm
    have htw : Commute t (w : G) := (mem_centralizer_singleton_iff.mp (hWt w.property)).symm
    have hns := source16_centralizer_nonsolvable h r ha ht htM hwi (hWD w.property)
    exact (source16_fixed_commutator_le_trace_root h r ha hz hzM ht htM hwi hzw htw hns).trans
      (hnone w (fun he => hw (congrArg Subtype.val he)))
  obtain ⟨w,hw,hnc⟩ := hex
  have hw1 : (w : G) ≠ 1 := fun he => hw (Subtype.ext he)
  have hwi : PFAppendixIII.IsInvolution (w : G) :=
    ⟨hw1,elemPow_eq_one_of_isElementaryAbelian (w : G) w.property⟩
  have hwu : (w : G) ≠ u := by
    intro he
    apply hnc
    rw [he]
    exact sup_le ((closure_le _).mpr (fun x hx => mem_centralizer_singleton_iff.mpr hx.2.2.eq))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htu.eq))
  have huw : Commute u (w : G) :=
    Subtype.ext_iff.mp (mul_comm (⟨u,huW⟩ : W) w)
  have hzw : Commute z (w : G) := (mem_centralizer_singleton_iff.mp (hWz w.property)).symm
  have htw : Commute t (w : G) := (mem_centralizer_singleton_iff.mp (hWt w.property)).symm
  have huB : u ∈ centralizer ({(w : G)} : Set G) := mem_centralizer_singleton_iff.mpr huw.eq
  refine ⟨w,w.property,hwi,hwu,huB,?_⟩
  apply square_field_of_noncentral_local_root h r ha _
    (r.involution_centralizer_ne_top h.disconnected hwi) hz
    (mem_centralizer_singleton_iff.mpr hzw.eq) hzM ht
    (mem_centralizer_singleton_iff.mpr htw.eq) htM
    (source16_centralizer_nonsolvable h r ha ht htM hwi (hWD w.property))
    hu huB (hWD huW).1 hzu htu
  rwa [source16_local_trace_circle]

end BenderSuzuki.ZD
