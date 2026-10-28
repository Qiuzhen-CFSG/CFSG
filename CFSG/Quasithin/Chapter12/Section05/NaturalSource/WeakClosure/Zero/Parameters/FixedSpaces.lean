module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Minimum
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Geometry

/-!
# The involution branch of a small-corank escaping centralizer

The original marking preserves quotient coranks. An automizer involution
fixing a subspace of corank at most three must have displacement rank three,
and that subspace is its entire fixed space. Conjugacy identifies this
fixed space with the marked first-involution space V₄+V₆. Its centralizer
therefore lies in a conjugate of G₆, which lies in M by the earlier local input.

This supplies a direct source-specialized exclusion using the original
G₆≤M from qt-d-1251-local. Applying E.6.13 directly to an involution fixed
space would require an odd induced centralizer, which that space does
not have. The subsequent obstruction argument instead uses this exclusion
to establish oddness for any remaining escaping centralizer.

Source: Aschbacher--Smith, 12.5.4--6, printed pp.819--820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
open scoped IsMulCommutative
namespace ExteriorMarking
variable (a : ExteriorMarking D)


omit [Finite G] in
private theorem subspace_card (W : Submodule (ZMod 2) SL5ExteriorSquare.V) :
    Nat.card (a.subspace W) = Nat.card W := by
  apply Nat.card_congr
  exact {
    toFun x := ⟨(a.coordinates ⟨x, a.subspace_le W x.property⟩).toAdd,
      (a.mem_subspace W _).mp x.property⟩
    invFun x := ⟨(a.coordinates.symm (Multiplicative.ofAdd x.val) : V),
      (a.mem_subspace W _).mpr (by rw [MulEquiv.apply_symm_apply]; exact x.property)⟩
    left_inv x := by
      apply Subtype.ext
      change (a.coordinates.symm (a.coordinates ⟨x, a.subspace_le W x.property⟩) : G) = x
      exact congrArg (fun v : V => (v : G)) (a.coordinates.symm_apply_apply _)
    right_inv x := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (a.coordinates.apply_symm_apply _) }

/-- Exterior coordinates preserve the actual quotient-corank convention. -/
theorem corank_subspace (W : Submodule (ZMod 2) SL5ExteriorSquare.V) :
    subgroupCorank V (a.subspace W) =
      Module.finrank (ZMod 2) (SL5ExteriorSquare.V ⧸ W) := by
  let : Finite SL5ExteriorSquare.V := Finite.of_equiv V a.coordinates.toEquiv
  have hsc : Nat.card ((a.subspace W).subgroupOf V) = Nat.card W :=
    (Nat.card_congr (subgroupOfEquivOfLe (a.subspace_le W)).toEquiv).trans
      (a.subspace_card W)
  have hc := ((a.subspace W).subgroupOf V).card_mul_index
  have hV : Nat.card V = Nat.card SL5ExteriorSquare.V :=
    Nat.card_congr a.coordinates.toEquiv
  rw [hsc, hV] at hc
  have hq := Submodule.card_eq_card_quotient_mul_card W
  have hi : (a.subspace W).relIndex V = Nat.card (SL5ExteriorSquare.V ⧸ W) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := W))
    exact hc.trans hq
  unfold subgroupCorank
  rw [hi, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow (by decide)]

omit [Finite G] in
/-- The first-involution fixed-space centralizer is controlled by the original G₆. -/
theorem centralizer_of_rank_three_involution_fixedSpace_le
    (hG₆ : a.Gi 6 ≤ a.M)
    (g : SL5TenDimensional.Group) (hg : orderOf g = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (SL5ExteriorSquare.displacement g)) = 3) :
    centralizer (a.subspace (SL5ExteriorSquare.fixedSpace g) : Set G) ≤ a.M := by
  have hne := (orderOf_eq_prime_iff.mp hg).2
  have hs : g * g = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hg).1
  have hc : IsConj SL5ExteriorSquare.j₁ g := by
    rcases SL5ExteriorSquare.involution_conjugacy_exhaustion g hne hs with hc | hc
    · exact hc
    · have hh := (SL5ExteriorSquare.ranks_of_isConj_j₂ hc).2
      omega
  obtain ⟨k, rfl⟩ := isConj_iff.mp hc
  obtain ⟨q, hq⟩ := a.quotientEquiv.surjective k
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hL : (l : G) ∈ a.M := L.le_normalizer l.property
  have hm : a.M.map (MulAut.conj (l : G)).toMonoidHom = a.M :=
    mem_normalizer_iff_map_conj_eq.mp (a.M.le_normalizer hL)
  have hnormal :
      normalizer ((a.Vi 6).map (MulAut.conj (l : G)).toMonoidHom : Set G) ≤ a.M := by
    rw [← map_equiv_normalizer_eq]
    exact (map_mono hG₆).trans_eq hm
  have hsub : (a.Vi 6).map (MulAut.conj (l : G)).toMonoidHom ≤
      a.subspace (SL5ExteriorSquare.fixedSpace (k * SL5ExteriorSquare.j₁ * k⁻¹)) := by
    rintro x ⟨v, hv, rfl⟩
    let v₀ : V := ⟨v, a.subspace_le _ hv⟩
    have hn := (mem_normalizer_iff.mp (D.normalizes l.property) v).mp v₀.property
    apply (a.mem_subspace _ ⟨(l : G) * v * (l : G)⁻¹, hn⟩).mpr
    have he := congrArg Multiplicative.toAdd (a.equivariant l v₀)
    rw [hl, hq] at he
    change (a.coordinates ⟨(l : G) * v * (l : G)⁻¹, hn⟩).toAdd =
      SL5TenDimensional.exteriorAction 2 k (a.coordinates v₀).toAdd at he
    rw [he, SL5ExteriorSquare.mem_fixedSpace]
    have hv₆ := (a.mem_subspace SL5ExteriorSquare.V₆ v₀).mp hv
    have hfix : SL5TenDimensional.exteriorAction 2 SL5ExteriorSquare.j₁
        (a.coordinates v₀).toAdd = (a.coordinates v₀).toAdd := by
      apply (SL5ExteriorSquare.mem_fixedSpace _ _).mp
      rw [SL5ExteriorSquare.fixedSpace_j₁]
      exact (show SL5ExteriorSquare.V₆ ≤ SL5ExteriorSquare.V₄ ⊔
        SL5ExteriorSquare.V₆ from le_sup_right) hv₆
    have hinv : SL5TenDimensional.exteriorAction 2 k⁻¹
        (SL5TenDimensional.exteriorAction 2 k (a.coordinates v₀).toAdd) =
          (a.coordinates v₀).toAdd := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    simp only [map_mul, Module.End.mul_apply, hinv, hfix]
  exact (Subgroup.centralizer_le hsub).trans
    ((Subgroup.centralizer_le_normalizer _).trans hnormal)

end ExteriorMarking

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The even local-image branch of the corank-three escape argument. -/
theorem centralizer_le_of_small_corank_involution
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U ≤ 3)
    (t : Automizer V) (ht : orderOf t = 2)
    (hfix : let := D.elementary
      ∀ v : V, (v : G) ∈ U →
        automizerRepresentation V t (Additive.ofMul v) = Additive.ofMul v) :
    centralizer (U : Set G) ≤ s.marking.M := by
  let := D.elementary
  obtain ⟨e, he⟩ := s.exists_full_automizer_equiv h
  let g := e t
  let F := s.marking.subspace (SL5ExteriorSquare.fixedSpace g)
  have hUF : U ≤ F := by
    intro v hv
    let v₀ : V := ⟨v, hUV hv⟩
    apply (s.marking.mem_subspace _ v₀).mpr
    apply (SL5ExteriorSquare.mem_fixedSpace _ _).mpr
    have hh := he t (Additive.ofMul v₀)
    rw [hfix v₀ hv] at hh
    exact hh.symm
  have hg : orderOf g = 2 := (e.orderOf_eq t).trans ht
  have hdim : Module.finrank (ZMod 2)
      (LinearMap.range (SL5ExteriorSquare.displacement g)) = 3 := by
    have hfcor := s.marking.corank_subspace (SL5ExteriorSquare.fixedSpace g)
    have hnull := LinearMap.finrank_range_add_finrank_ker (SL5ExteriorSquare.displacement g)
    have hquot := (SL5ExteriorSquare.fixedSpace g).finrank_quotient_add_finrank
    have hle := offender_corank_add hUF (s.marking.subspace_le
      (SL5ExteriorSquare.fixedSpace g))
    have hr := SL5ExteriorSquare.involution_displacement_ranks g
      ((orderOf_eq_prime_iff.mp hg).2)
      (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hg).1)
    change Module.finrank (ZMod 2) (LinearMap.range (SL5ExteriorSquare.displacement g)) +
      Module.finrank (ZMod 2) (SL5ExteriorSquare.fixedSpace g) = _ at hnull
    change subgroupCorank V F = _ at hfcor
    rcases hr with hr | hr <;> omega
  have hfcor : subgroupCorank V F = 3 := by
    rw [s.marking.corank_subspace]
    have hn := LinearMap.finrank_range_add_finrank_ker (SL5ExteriorSquare.displacement g)
    have hq := (SL5ExteriorSquare.fixedSpace g).finrank_quotient_add_finrank
    change Module.finrank (ZMod 2) (LinearMap.range (SL5ExteriorSquare.displacement g)) +
      Module.finrank (ZMod 2) (SL5ExteriorSquare.fixedSpace g) = _ at hn
    omega
  have hFV : F ≤ V := s.marking.subspace_le _
  let : IsElementaryAbelian 2 F := offender_elementary_of_le hFV
  have hadd := offender_corank_add hUF hFV
  have hzero : subgroupCorank F U = 0 := by omega
  have hEq := subgroup_eq_of_corank_zero hUF hzero
  rw [hEq]
  exact s.marking.centralizer_of_rank_three_involution_fixedSpace_le hG₆ g hg hdim

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
