module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryNativePaths
public import Theory.GroupAction.CubicTree.TotalSingularity
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# The binary exceptional maximum regular-path length

The nonidentity element of the native five-path fixer fixes the displayed
six-path and moves a forward choice at each endpoint. Both endpoints have
valence three, so this gives a regular six-path. The order-two bound on the
five-fixer identifies every nontrivial fixer with that element. Kernel-checked
binary octonion entries show that it fixes none of the four two-step
continuations. Five-path transitivity and reversal then give odd fixers for
all paths of length at least seven, ruling out regularity at either root type.

The calculation uses the actual G₂(2)′ parabolics and their full order-32
Borel. The only new finite certificates compare individual matrix entries.
Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
(10.9), printed pp.162–163. The root conventions come from the licensed
ATLAS imports; see `LICENSES/ATLAS.txt`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.BinaryMaximum
open Theory.GroupTheory Subgroup SimpleGraph SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry.RankTwo
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair
open BinaryPaths
local notation "F" => BinaryPaths.family
private def prefixWord : DerivedModel := b*a*b*a
private theorem fix_base {g : DerivedModel} {i : Bool} (hg : g ∈ F i) :
    g • base F i = base F i := by
  change g ∈ stabilizer F (base F i)
  simpa only [stabilizer, base, Subgroup.CosetGeometry.stabilizer_base] using hg

private theorem mem_of_fix {g : DerivedModel} {i : Bool}
    (hg : g • base F i = base F i) : g ∈ F i := by
  change g ∈ stabilizer F (base F i) at hg
  simpa only [stabilizer, base, Subgroup.CosetGeometry.stabilizer_base] using hg

private theorem pow_smul_injective {A X : Type*} [Group A] [MulAction A X]
    {p : ℕ} [Fact p.Prime] (a : A) (x : X) (ha : a ^ p = 1)
    (hx : a • x ≠ x) : Function.Injective (fun i : Fin p => a ^ i.val • x) := by
  have hi (n : ℕ) : (fun y : X => a • y)^[n] x = a ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hm : Function.minimalPeriod (fun y : X => a • y) x = p := by
    apply Function.minimalPeriod_eq_prime
    · change (fun y : X => a • y)^[p] x = x
      rw [hi, ha, one_smul]
    · exact hx
  intro i j hij
  apply Fin.ext
  exact Function.iterate_injOn_Iio_minimalPeriod (f := fun y : X => a • y) (x := x)
    (by simpa only [hm, Set.mem_Iio] using i.isLt)
    (by simpa only [hm, Set.mem_Iio] using j.isLt)
    (by simpa only [hi] using hij)

private theorem neighbor_powers {i : Bool} {p : ℕ} [Fact p.Prime]
    (a : DerivedModel) (ha : a ∈ F i) (hap : a ^ p = 1) (hna : a ∉ F (!i))
    (hc : Nat.card ((graph F).neighborSet (base F i)) = p)
    {v : Vertex F} (hv : (graph F).Adj (base F i) v) :
    ∃ j : Fin p, a ^ j.val • base F (!i) = v := by
  let f : Fin p → (graph F).neighborSet (base F i) := fun j =>
    ⟨a ^ j.val • base F (!i), by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (a ^ j.val)).toHom.map_adj
        (show (graph F).Adj (base F i) (base F (!i)) from
          ⟨by cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩)
      change (graph F).Adj (a ^ j.val • base F i) _ at hh
      rwa [fix_base (Subgroup.pow_mem _ ha _)] at hh⟩
  have hf : Function.Injective f := by
    intro j k hjk
    exact pow_smul_injective a (base F (!i)) hap
      (fun he => hna (mem_of_fix he)) (congrArg Subtype.val hjk)
  have : Finite ((graph F).neighborSet (base F i)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : p.Prime).ne_zero)
  have hs := hf.bijective_of_nat_card_le (by rw [hc]; simp)
  obtain ⟨j,hj⟩ := hs.2 ⟨v,hv⟩
  exact ⟨j,congrArg Subtype.val hj⟩


private theorem translate_ne {g : DerivedModel} {i : Bool} (hg : g ∉ F i) :
    g • base F i ≠ base F i := fun he => hg (mem_of_fix he)
private theorem moved_translate {g w : DerivedModel} {i : Bool}
    (hg : w⁻¹*g*w ∉ F i) : g • (w • base F i) ≠ w • base F i := by
  intro he
  apply translate_ne hg
  have hh := congrArg (fun v : Vertex F => w⁻¹ • v) he
  simpa only [mul_smul,inv_smul_smul] using hh
private theorem mover_moves :
    mover • (a • base F false) ≠ a • base F false ∧
    mover • ((endWord*a) • base F false) ≠ (endWord*a) • base F false := by
  have check :
      ((a⁻¹*mover*a).val*z).val (Atlas.SplitOctonion.basisVector 5) 0 ≠
        (z*(a⁻¹*mover*a).val).val (Atlas.SplitOctonion.basisVector 5) 0 ∧
      (((endWord*a)⁻¹*mover*(endWord*a)).val*z).val (Atlas.SplitOctonion.basisVector 5) 0 ≠
        (z*((endWord*a)⁻¹*mover*(endWord*a)).val).val (Atlas.SplitOctonion.basisVector 5) 0 := by
    decide +kernel
  constructor
  · apply moved_translate
    intro hc
    exact check.1 (congrArg (fun g : Model (ZMod 2) =>
      g.val (Atlas.SplitOctonion.basisVector 5) 0) (firstParabolic_centralizes_z _ hc))
  · apply moved_translate
    intro hc
    exact check.2 (congrArg (fun g : Model (ZMod 2) =>
      g.val (Atlas.SplitOctonion.basisVector 5) 0) (firstParabolic_centralizes_z _ hc))
private theorem first_choice_adj : (graph F).Adj (base F true)
    (a • base F false) := by
  have h := (Subgroup.CosetGeometry.translationGraphIso F a).toHom.map_adj
    (show (graph F).Adj (base F true) (base F false) from
      ⟨by decide,Subgroup.CosetGeometry.incident_base F true false⟩)
  change (graph F).Adj (a • base F true) (a • base F false) at h
  rw [fix_base a_mem] at h
  exact h

private theorem right_choice_forward : Forward sixPath ((endWord*a) • base F false) := by
  refine ⟨?_,?_⟩
  · change (graph F).Adj (endWord • base F true) ((endWord*a) • base F false)
    have hh := (Subgroup.CosetGeometry.translationGraphIso F endWord).toHom.map_adj first_choice_adj
    change (graph F).Adj (endWord • base F true) (endWord • (a • base F false)) at hh
    simpa only [mul_smul] using hh
  · change (endWord*a) • base F false ≠ prefixWord • base F false
    have ht : endWord • base F false = prefixWord • base F false := by
      change (prefixWord*b) • base F false = prefixWord • base F false
      rw [mul_smul,fix_base b_mem]
    rw [← ht,mul_smul]
    intro hh
    apply translate_ne (i := false) a_not_mem
    have hh' := congrArg (fun v : Vertex F => endWord⁻¹ • v) hh
    simpa only [inv_smul_smul] using hh'

private theorem left_choice_backward : Backward sixPath (a • base F false) :=
  ⟨first_choice_adj,translate_ne a_not_mem⟩

theorem sixPath_regular : Regular (A := DerivedModel) sixPath := by
  have ha : GraphAction (graph F) DerivedModel :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  have hc := card_neighbors_of_indices F (fun _ => 3) family_indices
  have hright : Nat.card ((graph F).neighborSet sixPath.endpoint) = 3 := hc _
  have hleft : Nat.card ((graph F).neighborSet (base F true)) = 3 := hc _
  refine ⟨(rightRegular_reverse_iff sixPath).mp ?_,?_⟩
  · apply rightRegular_of_moved_forward ha (reverse sixPath)
      (by simpa only [endpoint_reverse] using hleft) mover
      (by intro y hy; exact mover_fixes y (by simpa only [vertices_reverse,List.mem_reverse] using hy))
      ((forward_reverse_iff_backward sixPath).mpr left_choice_backward) mover_moves.1
  · exact rightRegular_of_moved_forward ha sixPath hright mover mover_fixes
      right_choice_forward mover_moves.2

private theorem false_neighbors {v : Vertex F}
    (hv : (graph F).Adj (base F false) v) :
    ∃ j : Fin 3, b ^ j.val • base F true = v :=
  @neighbor_powers false 3 ⟨by decide⟩ b b_mem (Subtype.ext cubicActor_cube) b_not_mem
    (by rw [card_neighbor_base, family_indices]) _ hv
private theorem true_neighbors {v : Vertex F}
    (hv : (graph F).Adj (base F true) v) :
    ∃ j : Fin 3, a ^ j.val • base F false = v :=
  @neighbor_powers true 3 ⟨by decide⟩ a a_mem (Subtype.ext movingActor_cube) a_not_mem
    (by rw [card_neighbor_base, family_indices]) _ hv

private theorem mover_fixes_five : mover ∈ pathStabilizer F path := by
  intro v hv
  apply mover_fixes v
  rw [sixPath,vertices_snoc]
  exact List.mem_append_left _ hv

private theorem five_nontrivial_eq {g : DerivedModel}
    (hg : g ∈ pathStabilizer F path) (hne : g ≠ 1) : g = mover := by
  classical
  by_contra hne'
  let H := pathStabilizer F path
  let : Fintype H := Fintype.ofFinite H
  have hh : 2 < Fintype.card H := Fintype.two_lt_card_iff.mpr
    ⟨⟨g,hg⟩,1,⟨mover,mover_fixes_five⟩,
      fun he => hne (congrArg Subtype.val he),
      fun he => hne' (congrArg Subtype.val he),
      fun he => mover_ne_one (congrArg Subtype.val he).symm⟩
  change 2 < Fintype.card (pathStabilizer F path) at hh
  have hc := path_fixer_card_le
  rw [Nat.card_eq_fintype_card] at hc
  omega

private def continuationWord (k l : ℕ) : DerivedModel := prefixWord * b ^ k * a ^ l
private theorem continuation_check : ∀ k l : Fin 3, k ≠ 0 → l ≠ 0 →
    (((continuationWord k.val l.val)⁻¹*mover*continuationWord k.val l.val).val*z).val
      (Atlas.SplitOctonion.basisVector 5) 0 ≠
    (z*((continuationWord k.val l.val)⁻¹*mover*continuationWord k.val l.val).val).val
      (Atlas.SplitOctonion.basisVector 5) 0 := by
  decide +kernel
private theorem mover_not_fix_continuation (k l : Fin 3) (hk : k ≠ 0) (hl : l ≠ 0) :
    mover • (continuationWord k.val l.val • base F false) ≠
      continuationWord k.val l.val • base F false := by
  apply moved_translate
  intro hm
  exact continuation_check k l hk hl (congrArg (fun g : Model (ZMod 2) =>
    g.val (Atlas.SplitOctonion.basisVector 5) 0) (firstParabolic_centralizes_z _ hm))
/-- The unique involution of the five-fixer fixes none of the four possible
nonbacktracking two-step continuations. -/
theorem five_involution_no_two_step {g : DerivedModel}
    (hg : g ∈ pathStabilizer F path) (_h2 : g ^ 2 = 1) (hne : g ≠ 1)
    {v w : Vertex F} (hv : (graph F).Adj path.endpoint v)
    (hvne : v ≠ path.penultimate) (hw : (graph F).Adj v w)
    (hwne : w ≠ path.endpoint) : g • w ≠ w := by
  rw [five_nontrivial_eq hg hne]
  have hvl : (graph F).Adj (base F false) (prefixWord⁻¹ • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F prefixWord⁻¹).toHom.map_adj hv
    change (graph F).Adj (prefixWord⁻¹ • (prefixWord • base F false)) (prefixWord⁻¹ • v) at hh
    simpa only [inv_smul_smul] using hh
  obtain ⟨k,hk⟩ := false_neighbors hvl
  have hv' : v = (prefixWord * b ^ k.val) • base F true := by
    have hh := congrArg (fun x : Vertex F => prefixWord • x) hk
    simpa only [smul_inv_smul,← mul_smul,mul_inv_cancel,one_smul] using hh.symm
  have hk0 : k ≠ 0 := by
    intro he
    apply hvne
    rw [hv',he]
    change (prefixWord * b ^ 0) • base F true = (b*a*b) • base F true
    simp only [pow_zero,mul_one,prefixWord,mul_smul,fix_base (i := true) a_mem]
  have hwl : (graph F).Adj (base F true) ((prefixWord * b ^ k.val)⁻¹ • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F
      (prefixWord * b ^ k.val)⁻¹).toHom.map_adj hw
    change (graph F).Adj ((prefixWord * b ^ k.val)⁻¹ • v)
      ((prefixWord * b ^ k.val)⁻¹ • w) at hh
    rw [hv'] at hh
    simpa only [inv_smul_smul] using hh
  obtain ⟨l,hl⟩ := true_neighbors hwl
  have hw' : w = continuationWord k.val l.val • base F false := by
    have hh := congrArg (fun x : Vertex F => (prefixWord * b ^ k.val) • x) hl
    simpa only [continuationWord,smul_inv_smul,← mul_smul,mul_inv_cancel,one_smul] using hh.symm
  have hl0 : l ≠ 0 := by
    intro he
    apply hwne
    rw [hw',he]
    change (prefixWord * b ^ k.val * a ^ 0) • base F false = prefixWord • base F false
    simp only [pow_zero,mul_one,mul_smul,fix_base (i := false) (Subgroup.pow_mem _ b_mem _)]
  rw [hw']
  exact mover_not_fix_continuation k l hk0 hl0

private theorem nativeAction : GraphAction (graph F) DerivedModel :=
  ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩

/-- No involution fixes a nonbacktracking seven-path starting at the cubic type. -/
theorem seven_no_involution_cubic {v : Vertex F} (hv : v.type = true)
    (p : BasedWalk (graph F) 7 v) (hp : p.Nonbacktracking)
    {x : DerivedModel} (hx : x ∈ pathStabilizer F p) (h2 : x ^ 2 = 1) : x = 1 := by
  by_contra hne
  obtain ⟨g0,ha⟩ := exists_path_translate_of_rootPathTransitive F
    (BinaryPaths.rootPathTransitive_five true) path path_nb hv
    (p.take 5 (by decide)) (nonbacktracking_take _ p hp)
  have hxpre : x ∈ pathStabilizer F (p.take 5 (by decide)) := by
    intro w hw
    apply hx w
    rw [BasedWalk.vertices_take] at hw
    exact List.mem_of_mem_take hw
  rw [←pathStabilizer_map_conj_of_vertices F path (p.take 5 (by decide)) g0 ha] at hxpre
  obtain ⟨y,hy,hye⟩ := hxpre
  have hy2 : y ^ 2 = 1 := (MulAut.conj g0).injective (by
    rw [map_pow,map_one]
    change (MulAut.conj g0).toMonoidHom y ^ 2 = 1
    rw [hye,h2])
  have hyne : y ≠ 1 := fun he => hne (by rw [←hye,he,map_one])
  rcases p with ⟨v1,v2,v3,v4,v5,v6,v7,z0⟩
  change [g0 • base F true, g0 • base F false, g0 • (b • base F true),
      g0 • ((b*a) • base F false), g0 • ((b*a*b) • base F true),
      g0 • (prefixWord • base F false)] = [v,v1,v2,v3,v4,v5] at ha
  simp only [List.cons.injEq] at ha
  have h4 := ha.2.2.2.2.1
  have h5 := ha.2.2.2.2.2.1
  have hv6 : (graph F).Adj path.endpoint (g0⁻¹ • (v6 : Vertex F)) := by
    have hh := nativeAction.map_adj g0⁻¹ v6.property
    change (graph F).Adj (prefixWord • base F false) (g0⁻¹ • (v6 : Vertex F))
    simpa only [←h5,inv_smul_smul] using hh
  have hv6ne : g0⁻¹ • (v6 : Vertex F) ≠ path.penultimate := by
    intro he
    apply hp.2.2.2.2.1
    exact (inv_smul_eq_iff.mp he).trans h4
  have hv7 := nativeAction.map_adj g0⁻¹ v7.property
  have hv7ne : g0⁻¹ • (v7 : Vertex F) ≠ path.endpoint := by
    intro he
    apply hp.2.2.2.2.2.1
    exact (inv_smul_eq_iff.mp he).trans h5
  apply five_involution_no_two_step hy hy2 hyne hv6 hv6ne hv7 hv7ne
  have hx7 := hx v7 (by change (v7 : Vertex F) ∈ [v,v1,v2,v3,v4,v5,v6,v7]; simp)
  have hh := congrArg (fun w : Vertex F => g0⁻¹ • w) hx7
  rw [←hye] at hh
  change g0⁻¹ • ((g0*y*g0⁻¹) • (v7 : Vertex F)) = _ at hh
  simpa only [mul_smul,inv_smul_smul] using hh

/-- Reversal includes the other cubic orientation in the same obstruction. -/
theorem seven_no_involution {v : Vertex F}
    (p : BasedWalk (graph F) 7 v) (hp : p.Nonbacktracking)
    {x : DerivedModel} (hx : x ∈ pathStabilizer F p) (h2 : x ^ 2 = 1) : x = 1 := by
  by_cases hv : v.type = true
  · exact seven_no_involution_cubic hv p hp hx h2
  · have he : p.endpoint.type = true := by
      have hne : v.type ≠ p.endpoint.type := by
        intro he
        have hh := (even_walk_iff F p.toWalk).mpr he
        rw [BasedWalk.length_toWalk] at hh
        exact (by decide : ¬ Even 7) hh
      cases hv' : v.type <;> cases he : p.endpoint.type <;> simp_all
    apply seven_no_involution_cubic he (reverse p) (nonbacktracking_reverse p hp) _ h2
    intro w hw
    exact hx w (by simpa only [vertices_reverse,List.mem_reverse] using hw)

/-- Every longer native path has an odd pointwise fixer. -/
theorem long_fixer_odd {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking) (hn : 7 ≤ n) :
    Odd (Nat.card (pathStabilizer F p)) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := pathStabilizer F p) 2
    (even_iff_two_dvd.mp he)
  have hx2 : (x : DerivedModel) ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one x
    rw [hx] at hh
    exact congrArg Subtype.val hh
  have hxpre : (x : DerivedModel) ∈ pathStabilizer F (p.take 7 hn) := by
    intro w hw
    apply x.property w
    rw [BasedWalk.vertices_take] at hw
    exact List.mem_of_mem_take hw
  have hone := seven_no_involution (p.take 7 hn) (nonbacktracking_take _ p hp) hxpre hx2
  have hex : x = 1 := Subtype.ext hone
  rw [hex,orderOf_one] at hx
  contradiction

/-- Odd fixers obstruct endpoint transitivity in both native root types. -/
theorem long_not_rightRegular {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking) (hn : 7 ≤ n) :
    ¬ RightRegular (A := DerivedModel) p := by
  intro hr
  have ho := long_fixer_odd p hp hn
  cases n with
  | zero => omega
  | succ n =>
    have hc := card_forward_of_cubic p (card_neighbors_of_indices F (fun _ => 3) family_indices _)
    obtain ⟨z,hz⟩ : Nonempty {z : Vertex F // Forward p z} :=
      (Nat.card_pos_iff.mp (by rw [hc]; decide)).1
    have he : MulAction.orbit (pathStabilizer F p) z = {w | Forward p w} := by
      apply Set.Subset.antisymm
      · rintro _ ⟨g,rfl⟩
        exact forward_smul_of_fixes nativeAction p g g.property hz
      · intro w hw
        obtain ⟨g,hg,hgw⟩ := hr z w hz hw
        exact ⟨⟨g,hg⟩,hgw⟩
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
      (pathStabilizer F p) z)
    rw [Nat.card_prod,he] at hh
    change Nat.card {z : Vertex F // Forward p z} * _ = _ at hh
    rw [hc] at hh
    have hev : Even 2 := by decide
    exact (Nat.not_even_iff_odd.mpr ho) (hh ▸ hev.mul_right _)

/-- The native regular-path maximum is at most six, for either root type. -/
theorem regular_length_le_six {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking)
    (hr : Regular (A := DerivedModel) p) : n ≤ 6 := by
  by_contra hn
  exact long_not_rightRegular p hp (by omega) hr.2


end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.BinaryMaximum
