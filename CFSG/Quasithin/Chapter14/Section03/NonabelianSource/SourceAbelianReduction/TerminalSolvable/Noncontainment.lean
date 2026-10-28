module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Defs
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# A moved terminal component cannot lie in M

A local lift K is perfect, and its T-conjugate span D is perfect and normal
in the original point normalizer H. If K lies in M, then so does D. Since
the seed-plane action of M is S₃, D centralizes the seed. Relative normality
propagates this to its H-conjugate span U. Thus K has trivial image in the
literal action on U/Z(U), contrary to the moved-component mark.

This proves the noncontainment needed by the component sieve independently
of component recognition or a comparison of the action kernel with O₂(K).
Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem perfect_le_centralizer
    {M D : Subgroup G} {T : Sylow 2 G}
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    [Group.IsPerfect D] (hDM : D ≤ M) : D ≤ centralizer (localModule T M : Set G) := by
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let DM := D.subgroupOf M
  let ed : DM ≃* D := subgroupOfEquivOfLe hDM
  let : Group.IsPerfect DM := Group.IsPerfect.ofSurjective
    (f := ed.symm.toMonoidHom) ed.symm.surjective
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide +kernel)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (M ⧸ C) := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hDC : DM ≤ C := le_of_isPerfect_of_solvable_quotient DM C
  intro x hx
  exact hDC (show (⟨x,hDM hx⟩ : M) ∈ DM from hx)

omit [Finite G] in
private theorem terminalDot_eq_bot_of_centralizes
    {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
    (F : InvariantFlag T V n) (K : Subgroup G)
    (hc : K ≤ centralizer (F.U : Set G)) : F.terminalDot K = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  intro k hk
  change F.terminalHatAction k = 1
  apply MulEquiv.ext
  intro u
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (center F.U) u
  rw [F.terminalHatAction_apply_mk]
  change QuotientGroup.mk' (center F.U) _ = QuotientGroup.mk' (center F.U) v
  congr 1
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_apply_coe]
  have he := mem_centralizer_iff.mp (hc hk) v v.property
  calc
    (k : G) * v * (k : G)⁻¹ = v * k * (k : G)⁻¹ :=
      congrArg (fun x : G => x * (k : G)⁻¹) he.symm
    _ = v := by group

omit [Finite G] in
theorem terminal_component_lift_not_le
    {T : Sylow 2 G} {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    (K : Subgroup G) (hKH : K ≤ F.H)
    (hcomp : (K.subgroupOf F.H).IsCComponent)
    (hnormal : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).Normal)
    (hne : F.terminalDot K ≠ ⊥) : ¬ K ≤ M := by
  intro hKM
  let D := conjugateSpanBy K (T : Subgroup G)
  let : Group.IsPerfect (K.subgroupOf F.H) := hcomp.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  let : Group.IsPerfect D := conjugateSpanBy_isPerfect K (T : Subgroup G)
  have hDM : D ≤ M := conjugateSpanBy_le hKM (hTM.trans M.le_normalizer)
  have hDH : D ≤ F.H := conjugateSpanBy_le hKH ((F.invariant 1).trans F.H.le_normalizer)
  have hn : F.H ≤ normalizer (D : Set G) := (normal_subgroupOf_iff_le_normalizer hDH).mp hnormal
  have hc : D ≤ centralizer (rankTwoSeed T M : Set G) := by
    rw [rankTwoSeed_eq_localModule T M]
    exact perfect_le_centralizer e hDM
  have hcU : D ≤ centralizer (F.U : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes D (rankTwoSeed T M) F.H hn hc
  exact hne (terminalDot_eq_bot_of_centralizes F K ((le_conjugateSpanBy K _).trans hcU))
omit [Finite G] in
/-- Apply noncontainment to the exact component-lifting contract. -/
theorem ComponentLift.not_le
    {T : Sylow 2 G} {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (h : ComponentLift F g K) : ¬ K ≤ M := by
  apply terminal_component_lift_not_le hTM e F K h.le_pointNormalizer h.component h.normal_span
  intro hb
  exact h.image_moved (by rw [hb, commutator_bot_left])

/-- Extract an actual local component outside M from the original nonsolvable
terminal action. The catalogue is not an input to this theorem. -/
theorem source_component_lift_outside
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ¬ K ≤ M := by
  let hrank := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := rankTwo_closure_geometry hrank F hne
  let he := F.uhat_elementary_of_point (by decide) d.two d.frattini_point
  let := he
  obtain ⟨hx, B, v, hyp, hSylow, L, hL, hm, hs, ho, hi,
    K, hKH, hlocal, hcomp, hmap, hiK, hnormal⟩ :=
    source_terminal_component_extraction hG T hempty hM hu hmany hcard e F hne g hgP hgH hn
  have hd : F.terminalDot K = L := hmap
  have hlift : ComponentLift F g K :=
    ⟨hKH, hlocal, hcomp, hd.symm ▸ hL, hd.symm ▸ hm, hnormal⟩
  exact ⟨K, hlift, hlift.not_le hM.1.2 e⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
