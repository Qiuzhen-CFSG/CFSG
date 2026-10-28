module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.SeedCommutator
public import Theory.GroupAction.MinimalNormal
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Actor
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Preparation for the solvable exclusion in 13.6.13

A solvable member of the literal X-family contains a minimal one. The
binary representation below is the actual faithful star action on U_v;
its restriction to the offender subgroup satisfies the complete B.5.6
interface using the given SQTK cover and trivial two-core.

The literal U_X lies in [U_v,X] and is invariant under X L_v T_v.
Consequently an independently established irreducibility of a containing
moved subgroup identifies that subgroup with U_X. The marked seed theorem
then supplies the nonzero L_v commutator. The classification construction
and irreducibility are not asserted here; they remain to be discharged in
the solvable-exclusion assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.13, printed p.929, and Hypothesis B.5.3 / Theorem B.5.6,
printed pp.104–105.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G]

/-- Inclusion minimality within the actual X-family. Solvability descends
from X, so smaller family members need not repeat that hypothesis. -/
def MinimalSolvable (L T : Subgroup G) (z v : G) (X : Subgroup (Gstar z v)) : Prop :=
  X ∈ XFamily L T z v ∧ Group.IsSolvable X ∧
    ∀ Y : Subgroup (Gstar z v), Y ∈ XFamily L T z v → Y ≤ X → Y = X

/-- The minimal choice in the first sentence of the source proof. -/
theorem exists_minimal_solvable [Finite G] (L T : Subgroup G) (z v : G)
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v) (hs : Group.IsSolvable X) :
    ∃ Y : Subgroup (Gstar z v), Y ≤ X ∧ MinimalSolvable L T z v Y := by
  obtain ⟨Y, hY, hYX, hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun Y : Subgroup (Gstar z v) => Y ∈ XFamily L T z v ∧ Group.IsSolvable Y) X ⟨hX, hs⟩
  refine ⟨Y, hYX, hY.1, hY.2, ?_⟩
  intro Z hZ hZY
  let : Group.IsSolvable Y := hY.2
  exact hmin Z ⟨hZ, Group.isSolvable_of_isSolvable_injective (inclusion_injective hZY)⟩ hZY

/-- The binary representation of the literal quotient on the literal U_v. -/
noncomputable def starRepresentation (z v : G) [IsElementaryAbelian 2 (Uv z v)] :
    Representation (ZMod 2) (Gstar z v) (Additive (Uv z v)) where
  toFun x := (starAction z v x).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul ((starAction z v 1) u.toMul) = u
    rw [map_one]
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul ((starAction z v (x * y)) u.toMul) = _
    rw [map_mul]
    rfl

/-- Faithfulness comes from the centralizer kernel defining G*_v. -/
theorem starRepresentation_injective (z v : G) [IsElementaryAbelian 2 (Uv z v)] :
    Function.Injective (starRepresentation z v) := by
  intro x y h
  apply starAction_injective z v
  apply MulEquiv.ext
  intro u
  exact congrArg Additive.toMul
    (congrArg (fun f : Module.End (ZMod 2) (Additive (Uv z v)) => f (Additive.ofMul u)) h)

/-- The linear representation retains the original conjugation convention. -/
theorem starRepresentation_mk_apply (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (g : Gv v) (u : Additive (Uv z v)) :
    ((starRepresentation z v (starMk z v g) u).toMul : G) =
      (g : G) * (u.toMul : G) * (g : G)⁻¹ := rfl

/-- Containment in the full displacement space, before any decomposition. -/
theorem UX_le_moved (L : Subgroup G) (z v : G) (X : Subgroup (Gstar z v)) :
    UX L z v X ≤ ⁅Uv z v, starPreimage z v X⁆ := by
  apply commutator_mono _ le_rfl
  exact conjugateSpanBy_mono le_rfl
    (sup_le (starPreimage_le_Gv z v X) (Lv_le_Gv L v))

/-- The subgroup U_X is inside the actual internal module. -/
theorem UX_le_Uv (L : Subgroup G) (z v : G) (X : Subgroup (Gstar z v)) :
    UX L z v X ≤ Uv z v :=
  (UX_le_moved L z v X).trans (le_normalizer_iff_commutator_le_left.mp
    ((starPreimage_le_Gv z v X).trans (Gv_normalizes_Uv z v)))

private theorem normalizes_commutator (A B C : Subgroup G)
    (hB : A ≤ normalizer (B : Set G)) (hC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer (⁅B, C⁆ : Subgroup G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hB ha),
    mem_normalizer_iff_map_conj_eq.mp (hC ha)]

/-- Both the residual and the Sylow actor preserve the literal U_X. -/
theorem UX_normalized (L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v) :
    starPreimage z v X ⊔ Lv L v ⊔ Tv T v ≤ normalizer (UX L z v X : Set G) := by
  let : X.Normal := hX.2
  have hA := starPreimage_normalized z v X
  apply normalizes_commutator
  · apply sup_le (le_normalizer_conjugateSpanBy _ _)
    apply normalizes_conjugateSpanBy
    · have hc : centralizer ({z} : Set G) = centralizer (zpowers z : Set G) := by
        rw [zpowers_eq_closure, centralizer_closure]
      exact (hfix.trans hc.le).trans (Subgroup.centralizer_le_normalizer _)
    · intro t ht
      rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        mem_normalizer_iff_map_conj_eq.mp (hA (show t ∈ Gv v from ht.2)),
        mem_normalizer_iff_map_conj_eq.mp (hL ht)]
  · exact (sup_le (sup_le (starPreimage_le_Gv z v X) (Lv_le_Gv L v))
      inf_le_right).trans hA

/-- Moving z makes its conjugate-span displacement nontrivial. -/
theorem UX_ne_bot_of_mem_Xz (L T : Subgroup G) (z v : G)
    {X : Subgroup (Gstar z v)} (hX : X ∈ Xz L T z v) : UX L z v X ≠ ⊥ := by
  intro hzero
  have hc : ⁅zpowers z, starPreimage z v X⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    exact (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hzero.le
  apply hX.2
  rw [commutator_comm] at hc
  simpa only [zpowers_eq_closure, centralizer_closure] using
    commutator_eq_bot_iff_le_centralizer.mp hc

/-- Irreducibility in subgroup language, on the actual subgroup W. -/
def IrreducibleOn (A W : Subgroup G) : Prop :=
  W ≠ ⊥ ∧ A ≤ normalizer (W : Set G) ∧
    ∀ B : Subgroup G, B ≤ W → A ≤ normalizer (B : Set G) → B = ⊥ ∨ B = W

/-- The middle inference of 13.6.13; irreducibility is an explicit local
hypothesis of this helper, not an assumption of the eventual source theorem. -/
theorem UX_eq_of_irreducible (L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v)
    (W : Subgroup G) (hUW : UX L z v X ≤ W)
    (hirr : IrreducibleOn (starPreimage z v X ⊔ Tv T v) W) :
    UX L z v X = W := by
  apply (hirr.2.2 _ hUW ?_).resolve_left
    (UX_ne_bot_of_mem_Xz L T z v (XFamily_subset_Xz L T z v hX))
  exact (sup_le (le_sup_of_le_left le_sup_left) le_sup_right).trans
    (UX_normalized L T z v hL hfix hX)

open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

/-- The full B.5.6 implication specialized to the faithful offender restriction. -/
theorem classify_star_offender [Finite G] (z v : G)
    [IsElementaryAbelian 2 (Uv z v)] {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥) :
    FFAlternatives.SourceAlternative (FFFactors.offenderRepresentation (starRepresentation z v)) := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  exact FFFactors.classify_offender (starRepresentation z v) classification
    (starMk z v) (starMk_surjective z v) hlocal (starRepresentation_injective z v) hcore

/-- The literal Thompson commutator puts X inside any normal overgroup of J*. -/
theorem X0_le_normal_of_thompson_le (L T : Subgroup G) (z v : G)
    {X : Subgroup (Gstar z v)} (hX : X ∈ X0 L T z v)
    (N : Subgroup (Gstar z v)) [N.Normal]
    (hJ : starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤ N) : X ≤ N := by
  rw [← hX.2.2.2]
  exact (commutator_mono le_rfl hJ).trans (commutator_le_right X N)

/-- Application to the actual faithful offender actor used by B.5.6. -/
theorem XFamily_le_offender (L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (Uv z v)]
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v)
    (hJ : starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤
      FFFactors.offenderActor (starRepresentation z v)) :
    X ≤ FFFactors.offenderActor (starRepresentation z v) :=
  X0_le_normal_of_thompson_le L T z v hX.1 _ hJ

/-- The literal U_X equals an irreducible moved subgroup and L_v acts nontrivially
on it, using the marked form of both seed-commutator clauses. -/
theorem marked_UX_eq_and_commutator_ne_bot [Finite G]
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s))
    (W : Subgroup G) (hUW : UX L (A5Module.markedZ s) (A5Module.markedV s) X ≤ W)
    (hirr : IrreducibleOn (starPreimage (A5Module.markedZ s) (A5Module.markedV s) X ⊔
      Tv T (A5Module.markedV s)) W) :
    UX L (A5Module.markedZ s) (A5Module.markedV s) X = W ∧
      ⁅W, Lv L (A5Module.markedV s)⁆ ≠ ⊥ := by
  have he := UX_eq_of_irreducible L T _ _ hL hfix hX W hUW hirr
  refine ⟨he, ?_⟩
  rw [← he]
  exact (marked_Xz_commutators_ne_bot s T S hS hfix
    (XFamily_subset_Xz L T _ _ hX)).2

/-- Choose the minimal solvable member while retaining both actual
commutator conclusions of 13.6.11 and the seed movement of 13.6.12. -/
theorem exists_minimal_solvable_seed [Finite G]
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s))
    (hsolv : Group.IsSolvable X) :
    ∃ Y : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s)),
      Y ≤ X ∧ MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) Y ∧
      Y ∈ Xz L T (A5Module.markedZ s) (A5Module.markedV s) ∧
      ⁅⁅zpowers (A5Module.markedZ s), starPreimage (A5Module.markedZ s) (A5Module.markedV s) Y⁆,
        Lv L (A5Module.markedV s)⁆ ≠ ⊥ ∧
      ⁅UX L (A5Module.markedZ s) (A5Module.markedV s) Y, Lv L (A5Module.markedV s)⁆ ≠ ⊥ := by
  obtain ⟨Y, hYX, hY⟩ := exists_minimal_solvable L T _ _ hX hsolv
  have hYz := XFamily_subset_Xz L T _ _ hY.1
  exact ⟨Y, hYX, hY, hYz, marked_Xz_commutators_ne_bot s T S hS hfix hYz⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
end
