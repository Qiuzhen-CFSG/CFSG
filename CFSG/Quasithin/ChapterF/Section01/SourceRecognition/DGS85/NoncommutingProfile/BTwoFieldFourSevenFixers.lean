module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.RegularSixPath
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# The field-four native regular-path upper bound

In the marked cubic--quintic J₂ action, the representative five-path fixer
has a unique involution, the native Borel row 83. The five quintic neighbors
are the powers of the marked order-five turn, and the three cubic neighbors
are the powers of the marked order-three actor. Kernel-checked permutation
certificates show that this involution fixes none of the eight possible
nonbacktracking two-step continuations. Five-path transitivity and reversal
therefore give odd fixers for every path of length at least seven, at either
root type. Such a fixer cannot act transitively on two or four forward exits.

All computations use the existing ATLAS degree-100 carrier and its faithful
inclusion; the native Borel and endpoint subgroups are unchanged.
Source: DGS, *Groups and Graphs* (1985), (10.9), printed pp.162--163.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.FieldFourPathUpper
open Theory.GroupTheory Subgroup SimpleGraph SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry.RankTwo
open Sporadic.LeechRelated.J2
open ExceptionalParabolics GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData PairNormalizer.RadicalData
open GeneratorPair.SecondOrbitCertificate SecondParabolic.Overlap
open SecondParabolic.BorelAutomorphisms PathCertificates
local notation "F" => PathCertificates.family
local notation "u" => oddGenerator 0

private theorem fix_base {g : Carrier} {i : Bool} (hg : g ∈ F i) :
    g • base F i = base F i := by
  change g ∈ stabilizer F (base F i)
  simpa only [stabilizer, base, Subgroup.CosetGeometry.stabilizer_base] using hg

private theorem mem_of_fix {g : Carrier} {i : Bool}
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
    (a : Carrier) (ha : a ∈ F i) (hap : a ^ p = 1) (hna : a ∉ F (!i))
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

set_option maxRecDepth 100000 in
private theorem u_cube : u ^ 3 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow, oddGenerator_inclusion, map_one]
  decide +kernel

private theorem quintic_neighbors {v : Vertex F}
    (hv : (graph F).Adj (base F false) v) :
    ∃ j : Fin 5, turn ^ j.val • base F true = v :=
  @neighbor_powers false 5 ⟨by decide⟩ turn turn_mem_l₁ turn_five turn_not_alpha
    (by rw [card_neighbor_base, family_indices]; rfl) _ hv

private theorem cubic_neighbors {v : Vertex F}
    (hv : (graph F).Adj (base F true) v) :
    ∃ j : Fin 3, u ^ j.val • base F false = v :=
  @neighbor_powers true 3 ⟨by decide⟩ u odd_mem_alpha u_cube odd_not_beta
    (by rw [card_neighbor_base, family_indices]; rfl) _ hv

set_option maxRecDepth 100000 in
private theorem involution_index_check : ∀ i : Fin 384,
    bTable i (terminalCenterTable 1) = terminalCenterTable (bTable i 1) →
    bTable i (bTable i 0) = 0 → bTable i (bTable i 1) = 1 → i = 0 ∨ i = 83 := by
  apply allFin
  decide +kernel

private theorem five_involution_eq {g : Carrier}
    (hg : g ∈ pathStabilizer F (path true)) (h2 : g ^ 2 = 1) (hne : g ≠ 1) :
    g = mover := by
  have hh := path_true_fixer_le hg
  obtain ⟨i,hi⟩ := exists_bElement ⟨g,hh.1⟩
  have he : inclusion g = bTable i := by
    rw [← bElement_table]
    exact congrArg (fun x : B => inclusion (x : Carrier)) hi.symm
  have hc := congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp hh.2)
  change inclusion g * inclusion (longWord * z * longWord⁻¹) =
    inclusion (longWord * z * longWord⁻¹) * inclusion g at hc
  rw [terminalCenter_inclusion,he] at hc
  have hs := congrArg inclusion h2
  rw [map_pow,map_one,he] at hs
  have hj := involution_index_check i
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hc)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hs)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hs)
  rcases hj with rfl | rfl
  · exfalso
    apply hne
    apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [he,map_one]
    decide +kernel
  · exact (congrArg Subtype.val hi).symm

private def continuationWord (k l : ℕ) : Carrier := longWord * turn ^ k * u ^ l
private def continuationTable (k l : ℕ) : Equiv.Perm (Fin 100) :=
  turnTable * oddTable 0 * turnTable * oddTable 0 * turnTable ^ k * oddTable 0 ^ l
private theorem continuation_inclusion (k l : ℕ) :
    inclusion (continuationWord k l) = continuationTable k l := by
  simp only [continuationWord,longWord,map_mul,map_pow,turn_inclusion,
    oddGenerator_inclusion,continuationTable]

set_option maxRecDepth 100000 in
private theorem continuation_check : ∀ k : Fin 5, ∀ l : Fin 3, k ≠ 0 → l ≠ 0 →
    ((continuationTable k.val l.val)⁻¹ * bTable 83 * continuationTable k.val l.val *
      FirstFusion.tPerm) 0 ≠
    (FirstFusion.tPerm * ((continuationTable k.val l.val)⁻¹ * bTable 83 *
      continuationTable k.val l.val)) 0 := by
  decide +kernel

private theorem mover_not_fix_continuation (k : Fin 5) (l : Fin 3)
    (hk : k ≠ 0) (hl : l ≠ 0) :
    mover • (continuationWord k.val l.val • base F false) ≠
      continuationWord k.val l.val • base F false := by
  intro he
  have hm : (continuationWord k.val l.val)⁻¹ * mover * continuationWord k.val l.val ∈
      F false := by
    apply mem_of_fix
    have hh := congrArg (fun v : Vertex F => (continuationWord k.val l.val)⁻¹ • v) he
    simpa only [mul_smul,inv_smul_smul] using hh
  have hh := congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp hm)
  simp only [map_mul,map_inv,mover,bElement_table,continuation_inclusion] at hh
  change _ * inclusion FirstFusion.t = inclusion FirstFusion.t * _ at hh
  rw [FirstFusion.inclusion_t] at hh
  exact continuation_check k l hk hl (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hh)

/-- The unique involution of the five-fixer fixes none of the eight possible
nonbacktracking two-step continuations. -/
theorem five_involution_no_two_step {g : Carrier}
    (hg : g ∈ pathStabilizer F (path true)) (h2 : g ^ 2 = 1) (hne : g ≠ 1)
    {v w : Vertex F} (hv : (graph F).Adj (path true).endpoint v)
    (hvne : v ≠ (path true).penultimate) (hw : (graph F).Adj v w)
    (hwne : w ≠ (path true).endpoint) : g • w ≠ w := by
  rw [five_involution_eq hg h2 hne]
  have hvl : (graph F).Adj (base F false) (longWord⁻¹ • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F longWord⁻¹).toHom.map_adj hv
    change (graph F).Adj (longWord⁻¹ • (longWord • base F false)) (longWord⁻¹ • v) at hh
    simpa only [inv_smul_smul] using hh
  obtain ⟨k,hk⟩ := quintic_neighbors hvl
  have hv' : v = (longWord * turn ^ k.val) • base F true := by
    have hh := congrArg (fun x : Vertex F => longWord • x) hk
    simpa only [smul_inv_smul,← mul_smul,mul_inv_cancel,one_smul] using hh.symm
  have hk0 : k ≠ 0 := by
    intro he
    apply hvne
    rw [hv',he]
    change (longWord * turn ^ 0) • base F true = (turn*u*turn) • base F true
    simp only [pow_zero,mul_one,longWord,mul_smul,fix_base (i := true) odd_mem_alpha]
  have hwl : (graph F).Adj (base F true) ((longWord * turn ^ k.val)⁻¹ • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F
      (longWord * turn ^ k.val)⁻¹).toHom.map_adj hw
    change (graph F).Adj ((longWord * turn ^ k.val)⁻¹ • v)
      ((longWord * turn ^ k.val)⁻¹ • w) at hh
    rw [hv'] at hh
    simpa only [inv_smul_smul] using hh
  obtain ⟨l,hl⟩ := cubic_neighbors hwl
  have hw' : w = continuationWord k.val l.val • base F false := by
    have hh := congrArg (fun x : Vertex F => (longWord * turn ^ k.val) • x) hl
    simpa only [continuationWord,smul_inv_smul,← mul_smul,mul_inv_cancel,one_smul] using hh.symm
  have hl0 : l ≠ 0 := by
    intro he
    apply hwne
    rw [hw',he]
    change (longWord * turn ^ k.val * u ^ 0) • base F false = longWord • base F false
    simp only [pow_zero,mul_one,mul_smul,fix_base (i := false) (Subgroup.pow_mem _ turn_mem_l₁ _)]
  rw [hw']
  exact mover_not_fix_continuation k l hk0 hl0

private theorem nativeAction : GraphAction (graph F) Carrier :=
  ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩

/-- No involution fixes a nonbacktracking seven-path starting at the cubic type. -/
theorem seven_no_involution_cubic {v : Vertex F} (hv : v.type = true)
    (p : BasedWalk (graph F) 7 v) (hp : p.Nonbacktracking)
    {x : Carrier} (hx : x ∈ pathStabilizer F p) (h2 : x ^ 2 = 1) : x = 1 := by
  by_contra hne
  obtain ⟨a,ha⟩ := exists_path_translate_of_rootPathTransitive F
    (rootPathTransitive_five true) (path true) (path_nonbacktracking true) hv
    (p.take 5 (by decide)) (nonbacktracking_take _ p hp)
  have hxpre : x ∈ pathStabilizer F (p.take 5 (by decide)) := by
    intro w hw
    apply hx w
    rw [BasedWalk.vertices_take] at hw
    exact List.mem_of_mem_take hw
  rw [←pathStabilizer_map_conj_of_vertices F (path true) (p.take 5 (by decide)) a ha] at hxpre
  obtain ⟨y,hy,hye⟩ := hxpre
  have hy2 : y ^ 2 = 1 := (MulAut.conj a).injective (by
    rw [map_pow,map_one]
    change (MulAut.conj a).toMonoidHom y ^ 2 = 1
    rw [hye,h2])
  have hyne : y ≠ 1 := fun he => hne (by rw [←hye,he,map_one])
  rcases p with ⟨v1,v2,v3,v4,v5,v6,v7,z0⟩
  change [a • base F true, a • base F false, a • (turn • base F true),
      a • ((turn*u) • base F false), a • ((turn*u*turn) • base F true),
      a • (longWord • base F false)] = [v,v1,v2,v3,v4,v5] at ha
  simp only [List.cons.injEq] at ha
  have h4 := ha.2.2.2.2.1
  have h5 := ha.2.2.2.2.2.1
  have hv6 : (graph F).Adj (path true).endpoint (a⁻¹ • (v6 : Vertex F)) := by
    have hh := nativeAction.map_adj a⁻¹ v6.property
    change (graph F).Adj (longWord • base F false) (a⁻¹ • (v6 : Vertex F))
    simpa only [←h5,inv_smul_smul] using hh
  have hv6ne : a⁻¹ • (v6 : Vertex F) ≠ (path true).penultimate := by
    intro he
    apply hp.2.2.2.2.1
    exact (inv_smul_eq_iff.mp he).trans h4
  have hv7 := nativeAction.map_adj a⁻¹ v7.property
  have hv7ne : a⁻¹ • (v7 : Vertex F) ≠ (path true).endpoint := by
    intro he
    apply hp.2.2.2.2.2.1
    exact (inv_smul_eq_iff.mp he).trans h5
  apply five_involution_no_two_step hy hy2 hyne hv6 hv6ne hv7 hv7ne
  have hx7 := hx v7 (by change (v7 : Vertex F) ∈ [v,v1,v2,v3,v4,v5,v6,v7]; simp)
  have hh := congrArg (fun w : Vertex F => a⁻¹ • w) hx7
  rw [←hye] at hh
  change a⁻¹ • ((a*y*a⁻¹) • (v7 : Vertex F)) = _ at hh
  simpa only [mul_smul,inv_smul_smul] using hh

/-- Reversal includes the quintic orientation in the same obstruction. -/
theorem seven_no_involution {v : Vertex F}
    (p : BasedWalk (graph F) 7 v) (hp : p.Nonbacktracking)
    {x : Carrier} (hx : x ∈ pathStabilizer F p) (h2 : x ^ 2 = 1) : x = 1 := by
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
  have hx2 : (x : Carrier) ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one x
    rw [hx] at hh
    exact congrArg Subtype.val hh
  have hxpre : (x : Carrier) ∈ pathStabilizer F (p.take 7 hn) := by
    intro w hw
    apply x.property w
    rw [BasedWalk.vertices_take] at hw
    exact List.mem_of_mem_take hw
  have hone := seven_no_involution (p.take 7 hn) (nonbacktracking_take _ p hp) hxpre hx2
  have hex : x = 1 := Subtype.ext hone
  rw [hex,orderOf_one] at hx
  contradiction

private theorem forward_card {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) (n+1) v) :
    Nat.card {z : Vertex F // Forward p z} = if p.endpoint.type then 2 else 4 := by
  classical
  have hc := card_neighbors_of_indices F (fun i => if i then 3 else 5) family_indices p.endpoint
  have : Finite ((graph F).neighborSet p.endpoint) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases p.endpoint.type <;> decide)
  let : Fintype ((graph F).neighborSet p.endpoint) := Fintype.ofFinite _
  let e : {z : Vertex F // Forward p z} ≃
      {z : (graph F).neighborSet p.endpoint //
        z ≠ ⟨p.penultimate,p.adj_penultimate_endpoint.symm⟩} := {
    toFun z := ⟨⟨z,z.property.1⟩,fun he => z.property.2 (congrArg Subtype.val he)⟩
    invFun z := ⟨z.val,z.val.property,fun he => z.property (Subtype.ext he)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ←Nat.card_eq_fintype_card,hc]
  cases p.endpoint.type <;> simp

/-- Odd fixers obstruct endpoint transitivity in both native valences. -/
theorem long_not_rightRegular {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking) (hn : 7 ≤ n) :
    ¬ RightRegular (A := Carrier) p := by
  intro hr
  have ho := long_fixer_odd p hp hn
  cases n with
  | zero => omega
  | succ n =>
    have hc := forward_card p
    obtain ⟨z,hz⟩ : Nonempty {z : Vertex F // Forward p z} :=
      (Nat.card_pos_iff.mp (by rw [hc]; cases p.endpoint.type <;> decide)).1
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
    have hev : Even (if p.endpoint.type then 2 else 4) := by
      cases p.endpoint.type <;> decide
    exact (Nat.not_even_iff_odd.mpr ho) (hh ▸ hev.mul_right _)

/-- The native regular-path maximum is at most six, for either root type. -/
theorem regular_length_le_six {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking)
    (hr : Regular (A := Carrier) p) : n ≤ 6 := by
  by_contra hn
  exact long_not_rightRegular p hp (by omega) hr.2

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.FieldFourPathUpper
