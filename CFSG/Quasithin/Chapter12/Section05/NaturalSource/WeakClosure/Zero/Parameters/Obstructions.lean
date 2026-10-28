module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.FixedSpaces
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Setup
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple

/-!
# Small-corank obstructions for the exterior module

An escaping centralizer of corank at most three has odd local automizer image:
an involution in that image would identify its fixed space with the original
subgroup, whose centralizer is controlled by the sixth parabolic. This proves
the odd-residual premise of E.6.13, so an escaping subgroup cannot be normal
in the chosen Sylow subgroup. Attainment of the global corank minimum then
reduces the strict bound in 12.5.6 to a nonnormal member of the E.6 family Γ.

The remaining nonnormal case is discharged in Parameters.Strict. The earlier TI input
belongs to qt-d-1222-source, and the sixth parabolic containment belongs to
qt-d-1251-local. Source: Aschbacher--Smith, E.6.1, E.6.13 and 12.5.6.
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

/-- The full local centralizer image has odd order in the small escaping case. -/
theorem odd_local_image_of_small_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U ≤ 3)
    (he : ¬ centralizer (U : Set G) ≤ s.marking.M) :
    Odd (Nat.card (inducedAutomizer V (s.marking.M ⊓ centralizer (U : Set G)))) := by
  let := D.elementary
  let I := inducedAutomizer V (s.marking.M ⊓ centralizer (U : Set G))
  by_contra ho
  have hd : 2 ∣ Nat.card I :=
    even_iff_two_dvd.mp ((Nat.even_or_odd (Nat.card I)).resolve_right ho)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 hd
  have ht' : orderOf (t : Automizer V) = 2 := (Subgroup.orderOf_coe t).trans ht
  apply he
  apply s.centralizer_le_of_small_corank_involution h hG₆ hUV hcor t ht'
  dsimp only
  intro v hv
  obtain ⟨n, hn, hnt⟩ := t.property
  change V.normalizerMonoidHom.rangeRestrict n = (t : Automizer V) at hnt
  rw [← hnt]
  change Additive.ofMul (V.normalizerMonoidHom n v) = Additive.ofMul v
  congr 1
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_apply_coe]
  have hc := (mem_centralizer_iff.mp hn.2) (v : G) hv
  change (v : G) * (n : G) = (n : G) * (v : G) at hc
  rw [← hc, mul_inv_cancel_right]

/-- The exterior calculation supplies the actual odd-residual clause of Γ. -/
theorem obstruction_of_small_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {U : Subgroup G} (hUV : U ≤ V) (hU : U ≠ ⊥)
    (hcor : subgroupCorank V U ≤ 3)
    (he : ¬ centralizer (U : Set G) ≤ s.marking.M) :
    U ∈ obstructionFamily s.marking.M V := by
  let := D.elementary
  have hE := s.hypothesisE61 h structural
  exact ⟨hUV, hU, he,
    oddCentralizerCondition_of_odd_image (hE.localCentralizer_le_normalizer hU hUV)
      (s.odd_local_image_of_small_escape h hG₆ hUV hcor he)⟩

/-- E.6.13 with its odd-image premise proved from the exterior calculation. -/
theorem centralizer_le_of_small_corank_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {U : Subgroup G} (hUV : U ≤ V) (hU : U ≠ ⊥)
    (hcor : subgroupCorank V U ≤ 3)
    (hn : (U.subgroupOf (T : Subgroup G)).Normal) :
    centralizer (U : Set G) ≤ s.marking.M := by
  by_contra he
  have hΓ := s.obstruction_of_small_escape h structural hG₆ hUV hU hcor he
  exact he (InvariantSubspaces.centralizer_le_of_normal_in_sylow_knownSimple
    (s.hypothesisE61 h structural) hU hUV hΓ.2.2.2 hn)

/-- A failure of the desired strict bound supplies a genuine, nonzero member
of Γ that is not normal in T. The minimum is taken over the full globalR domain. -/
theorem exists_nonnormal_small_obstruction_of_not_strict
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hr : ¬ (3 : ℕ∞) < globalR V) :
    ∃ U ∈ obstructionFamily s.marking.M V,
      subgroupCorank V U ≤ 3 ∧
      (subgroupCorank V U : ℕ∞) = globalR V ∧
      ¬ (U.subgroupOf (T : Subgroup G)).Normal := by
  let := D.elementary
  have hrle : globalR V ≤ 3 := le_of_not_gt hr
  obtain ⟨U, hUV, he, hmin⟩ := globalR_attained
    (ne_top_of_le_ne_top (by simp) hrle)
  have hc : subgroupCorank V U ≤ 3 := by
    exact_mod_cast hmin.le.trans hrle
  have hU : U ≠ ⊥ := by
    intro hb
    have hd := s.marking.linearCoordinates.finrank_eq.trans
      SL5TenDimensional.finrank_exteriorModule_two
    rw [hb, corank_bot, hd] at hc
    omega
  have hE := s.hypothesisE61 h structural
  have heM : ¬ centralizer (U : Set G) ≤ s.marking.M :=
    fun hh => he ((hE.centralizer_le_iff hU hUV).mp hh)
  refine ⟨U, s.obstruction_of_small_escape h structural hG₆ hUV hU hc heM,
    hc, hmin, ?_⟩
  exact fun hn => heM (s.centralizer_le_of_small_corank_normal h structural hG₆
    hUV hU hc hn)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
