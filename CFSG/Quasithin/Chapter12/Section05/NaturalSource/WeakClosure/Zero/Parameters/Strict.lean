module
public import Theory.Representation.SL5ExteriorSquare.SmallCorank
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.LowerBound
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction

/-!
# The strict exterior corank bound

The actual full automizer is SL₅(2). Its exterior-square action forces any
actor fixing a subspace of corank at most three to have square one. In an
escaping centralizer, a nonidentity such actor would be an involution; the
rank-three fixed-space identification and G₆ containment already exclude
that possibility. Thus the local centralizer equals the centralizer of V.

The lower bound excludes smaller coranks. E.6.13 excludes a Sylow-normal
obstruction, with its odd-residual premise proved in Obstructions. For the
remaining minimum, the local-centralizer equality supplies the actual
premise of E.6.12. Its conclusion r=1 contradicts the established r≥3.

Only Structural1222At from qt-d-1222-source and the original G₃,G₆
containments from qt-d-1251-local remain explicit. No numerical conclusion,
escaping-centralizer assertion or Held-center theorem is assumed.
Source: Aschbacher--Smith, E.6.3, E.6.12--13 and 12.5.6, pp.245,250,819--820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
include s

/-- A full automizer fixing a subspace of corank at most three has square one. -/
theorem square_eq_one_of_small_fixedSubgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U ≤ 3)
    (t : Automizer V)
    (hfix : let := D.elementary
      ∀ v : V, (v : G) ∈ U →
        automizerRepresentation V t (Additive.ofMul v) = Additive.ofMul v) :
    t * t = 1 := by
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
  have hd : 7 ≤ Module.finrank (ZMod 2) (SL5ExteriorSquare.fixedSpace g) := by
    have hfcor := s.marking.corank_subspace (SL5ExteriorSquare.fixedSpace g)
    have hquot := (SL5ExteriorSquare.fixedSpace g).finrank_quotient_add_finrank
    have hle := offender_corank_add hUF (s.marking.subspace_le
      (SL5ExteriorSquare.fixedSpace g))
    change subgroupCorank V F = _ at hfcor
    rw [SL5TenDimensional.finrank_exteriorModule_two] at hquot
    omega
  apply e.injective
  rw [map_mul, map_one]
  exact SL5ExteriorSquare.SmallActors.square_eq_one_of_large_fixedSpace g hd

/-- In an escaping small-corank centralizer the entire local action is trivial.
The full automizer calculation and the original G₆ containment discharge this
premise of E.6.12; it is not an extra escaping-centralizer assumption. -/
theorem localCentralizer_eq_of_small_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {U : Subgroup G} (hUV : U ≤ V) (hU : U ≠ ⊥)
    (hcor : subgroupCorank V U ≤ 3)
    (he : ¬ centralizer (U : Set G) ≤ s.marking.M) :
    s.marking.M ⊓ centralizer (U : Set G) =
      s.marking.M ⊓ centralizer (V : Set G) := by
  let := D.elementary
  have hE := s.hypothesisE61 h structural
  have hbot : inducedAutomizer V (s.marking.M ⊓ centralizer (U : Set G)) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro t ht
    change t = 1
    by_contra htne
    have hfix : ∀ v : V, (v : G) ∈ U →
        automizerRepresentation V t (Additive.ofMul v) = Additive.ofMul v := by
      intro v hv
      obtain ⟨n, hn, hnt⟩ := ht
      change V.normalizerMonoidHom.rangeRestrict n = t at hnt
      rw [← hnt]
      change Additive.ofMul (V.normalizerMonoidHom n v) = Additive.ofMul v
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_apply_coe]
      have hc := (mem_centralizer_iff.mp hn.2) (v : G) hv
      change (v : G) * (n : G) = (n : G) * (v : G) at hc
      rw [← hc, mul_inv_cancel_right]
    have ht2 := s.square_eq_one_of_small_fixedSubgroup h hUV hcor t hfix
    have horder : orderOf t = 2 :=
      orderOf_eq_prime (by simpa only [pow_two] using ht2) htne
    exact he (s.centralizer_le_of_small_corank_involution h hG₆ hUV hcor t horder hfix)
  apply le_antisymm
  · exact le_inf inf_le_left
      ((inducedAutomizer_eq_bot_iff (hE.localCentralizer_le_normalizer hU hUV)).mp hbot)
  · exact inf_le_inf_left _ (Subgroup.centralizer_le hUV)

/-- The strict global corank clause of original Lemma 12.5.6.
E.6.3 excludes smaller coranks, E.6.13 excludes normal obstructions, and
the exterior fixed-space calculation supplies the E.6.12 contradiction
for the remaining corank-three obstruction. -/
theorem three_lt_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    (3 : ℕ∞) < globalR V := by
  let := D.elementary
  have hlower := (s.three_le_globalR_and_globalS_eq_three h structural hG₃).1
  by_contra hr
  obtain ⟨U, hΓ, hc, hmin, _⟩ :=
    s.exists_nonnormal_small_obstruction_of_not_strict h structural hG₆ hr
  have hthree : subgroupCorank V U = 3 := by
    have hcl : 3 ≤ subgroupCorank V U := by exact_mod_cast hlower.trans hmin.ge
    omega
  have hE := s.hypothesisE61 h structural
  have hC := s.localCentralizer_eq_of_small_escape h structural hG₆
    hΓ.1 hΓ.2.1 (by omega) hΓ.2.2.1
  obtain ⟨W, _, _, _, _, heq⟩ := hE.hyperplane_escape_of_maximal_action
    (fun _ hW hmax hn => maximal_escape_action_knownSimple hE hW hmax hn)
    hΓ.2.1 hΓ.1 hC hΓ.2.2.1
  rw [heq] at hlower
  norm_num at hlower

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
