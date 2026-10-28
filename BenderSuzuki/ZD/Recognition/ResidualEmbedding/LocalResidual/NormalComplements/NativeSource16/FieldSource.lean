module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Field
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Omega

/-!
# The first square-field circle in Proposition 16.5

Conjugation by a second marked involution is the literal action on the
normal distinguished circle. Lemma 16.4(a) makes its action on the marked
root nontrivial. The concrete model split consequently identifies the circle
with a binary linear group over a square field, and identifies the actual
fixed subgroup over the square-root field.

Source: GLS IV, Chapter 2, Proposition 16.5, the paragraph following the
choice of W = ⟨u,v⟩.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- The actual conjugation action on the normal distinguished circle. -/
@[expose] public def source16_circleAction (h : IsProductDisconnected Z M)
    (F : Subgroup G) (hFM : ¬ F ≤ M) (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M) :
    F →* MulAut (localCircle Z F) := by
  let : (localCircle Z F).Normal := localCircle_normal h F hFM hne
  exact MulAut.conjNormal

omit [Finite G] in
public theorem source16_circleAction_apply (h : IsProductDisconnected Z M)
    (F : Subgroup G) (hFM : ¬ F ≤ M) (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    (v : F) (x : localCircle Z F) :
    localCircleHom Z F (source16_circleAction h F hFM hne v x) =
      (v : G) * localCircleHom Z F x * (v : G)⁻¹ := rfl

/-- A second involution commuting with the selected marked triple forces
an actual square-field model and square-root fixed group. -/
public theorem source16_square_field_circle
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u v : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ w ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution w →
      (residualCentralizerTrace Z M w).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (hv : PFAppendixIII.IsInvolution v) (hvD : v ∈ residualPairStabilizer M t)
    (hvu : Commute v u) (hzv : Commute z v) (htv : Commute t v) (hnevu : v ≠ u) :
    let B := centralizer ({u} : Set G)
    ∃ (hBM : ¬ B ≤ M) (hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M),
      let a := source16_circleAction h.disconnected B hBM hne
        ⟨v, mem_centralizer_singleton_iff.mpr hvu.eq⟩
      ∃ m : ℕ, 0 < m ∧
        Nonempty (localCircle Z B ≃* PSL2BinaryMatrixGroup (2 * m)) ∧
        Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  have hf := localCircleHom_injective Z B
  have hzB : z ∈ B := mem_centralizer_singleton_iff.mpr hzu.eq
  have htB : t ∈ B := mem_centralizer_singleton_iff.mpr htu.eq
  have hBM : ¬ B ≤ M := fun hh => htM (hh htB)
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M := ⟨z,hz,hzB,hzM⟩
  refine ⟨hBM,hne,?_⟩
  let ρ := source16_circleAction h.disconnected B hBM hne
  let vB : B := ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩
  let a := ρ vB
  have hav (x : C) : f (a x) = v * f x * v⁻¹ := rfl
  have ha2 : a ^ 2 = 1 := by
    change (ρ vB) ^ 2 = 1
    rw [← map_pow, show vB ^ 2 = 1 from Subtype.ext hv.sq_eq_one, map_one]
  let zC : C := ⟨⟨z,hzB⟩,subset_closure hz⟩
  let tC : C := ⟨⟨t,htB⟩,subset_closure ht⟩
  have haz : a zC = zC := hf (by rw [hav]; exact mul_inv_eq_iff_eq_mul.mpr hzv.symm.eq)
  have hat : a tC = tC := hf (by rw [hav]; exact mul_inv_eq_iff_eq_mul.mpr htv.symm.eq)
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  have hB := r.involution_centralizer_ne_top h.disconnected hu
  obtain ⟨hc,hperfect,hm,_⟩ := localCircle_nonsolvable_structure h r ha B hB hBM hne hns
  obtain ⟨n,hn,hmodel⟩ := hm.exists_exponent
  have hodd : Odd (Nat.card (center C)) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  obtain ⟨P,hP,hmark⟩ := localCircle_exists_marked_sylow h r ha B hB hBM hne hns
  have hzC : PFAppendixIII.IsInvolution zC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions z hz) hzB) _
  have htC : PFAppendixIII.IsInvolution tC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions t ht) htB) _
  have htNP : tC ∉ normalizer (P : Set C) := by rw [← hP]; exact htM
  have haNP : (normalizer (P : Set C)).map a.toMonoidHom = normalizer (P : Set C) := by
    rw [← hP]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change f (a x) ∈ M
      rw [hav]
      exact M.mul_mem (M.mul_mem hvD.1 hx) (M.inv_mem hvD.1)
    · intro x hx
      refine ⟨a x,?_,?_⟩
      · change f (a x) ∈ M
        rw [hav]
        exact M.mul_mem (M.mul_mem hvD.1 hx) (M.inv_mem hvD.1)
      · change a (a x) = x
        have hh := DFunLike.congr_fun ha2 x
        simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hroot := localCircle_rootGenerated_map_eq h r B hB hBM hne P hP hmark ht htB
  rw [source16_local_trace_circle] at hroot
  have hnot : ¬ rootGenerated (P : Subgroup C) tC ≤ a.fixedSubgroup := by
    intro hfix
    apply hnevu
    apply source16_unique_involution_marked_root_centralizer h r ha hg hz hzM ht htM hu huD
      hzu htu hmax hv hvu
    intro x hx
    rw [← hroot] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have he := congrArg f ((MulAut.mem_fixedSubgroup a y).mp (hfix hy))
    rw [hav] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨e,_,m,hmpos,hnm,hfixed,_⟩ := source16_square_field_of_nontrivial_root_action hn
    hperfect hodd hmodel P (hmark zC hz hzM) hzC htC htNP a ha2 haz hat haNP hnot
  exact ⟨m,hmpos,⟨hnm ▸ e⟩,hfixed⟩

end BenderSuzuki.ZD
