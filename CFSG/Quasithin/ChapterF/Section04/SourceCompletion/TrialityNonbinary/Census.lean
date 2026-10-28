module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Geometry
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.LongGirth

/-!
# Order equality and diameter of full triality extension completions

Girth twelve makes the odd paths of lengths 1,3,5 have distinct endpoints.
Their census is exactly the native opposite-parabolic index. Comparing with
the full extension order bound forces equality of orders and exhausts each
opposite vertex type. Every vertex is therefore within distance six.
The extension factor cancels at the marked endpoints; it is never discarded.

Source: Aschbacher--Smith F.4.6--7, F.4.13 and F.4.24, pp.276--280,287--288.
These are the numerical and geometric inputs, not a group recognition theorem.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon SimpleGraph.BasedWalk

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.SmallCompletion

variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)
variable {M : Type*} [Group M] (c : Completion E M)
local notation "q" => Parameters.q (binaryParameters m hm)

/-- The three short odd path counts retain the native unequal branching factors. -/
theorem completion_card_odd_paths (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) (k : Fin 3) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) (2*k.val+1) (base c.cosetFamily i) //
      p.Nonbacktracking} = SmallCompletion.degree m hm i * q^(4*k.val) := by
  have hc := completion_card_neighbors E c hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.ne_of_gt (degree_pos m hm _))
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  rw [card_nonbacktracking_succ (graph c.cosetFamily) (fun v => v.type) (SmallCompletion.degree m hm) hf hc]
  cases i <;> fin_cases k <;> simp [SmallCompletion.degree, forwardCount] <;> ring

private abbrev ShortOddPaths (i : Bool) := Σ k : Fin 3,
  {p : BasedWalk (graph c.cosetFamily) (2*k.val+1) (base c.cosetFamily i) // p.Nonbacktracking}

private def fiberEquiv (i : Bool) : {v : Vertex c.cosetFamily // v.type = i} ≃ M ⧸ c.cosetFamily i where
  toFun v := v.property ▸ v.val.coset
  invFun r := ⟨⟨i,r⟩,rfl⟩
  left_inv := by rintro ⟨⟨i,r⟩,h⟩; cases h; rfl
  right_inv _ := rfl

private def shortOddEndpoint (i : Bool) : ShortOddPaths E c i → {v : Vertex c.cosetFamily // v.type = !i} :=
  fun ⟨k,p⟩ => ⟨p.val.endpoint, by
    have he := QuadrangleRecognition.even_length_iff (G := graph c.cosetFamily)
      (fun v : Vertex c.cosetFamily => v.type)
      (fun h => h.1) p.val.toWalk
    rw [BasedWalk.length_toWalk] at he
    have hodd : ¬ Even (2*k.val+1) := by rintro ⟨a,ha⟩; omega
    have hn := fun ht => hodd (he.mpr ht)
    change ¬ (i = p.val.endpoint.type) at hn
    exact Bool.eq_not_iff.mpr (Ne.symm hn)⟩

private theorem shortOddEndpoint_injective (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (i : Bool) : Function.Injective (shortOddEndpoint E c i) := by
  rintro ⟨j,p,hp⟩ ⟨k,r,hr⟩ he
  have hend : p.endpoint = r.endpoint := congrArg Subtype.val he
  have hg := completion_cycle_length_ge_twelve E c hoverlap
  have hp' := isPath_of_nonbacktracking_of_cycle_bound
    (N := 11) (fun v w hw => by have := hg v w hw; omega) p hp (by omega)
  have hr' := isPath_of_nonbacktracking_of_cycle_bound
    (N := 11) (fun v w hw => by have := hg v w hw; omega) r hr (by omega)
  have hw : p.toWalk = r.toWalk.copy rfl hend.symm := by
    by_contra hne
    obtain ⟨v,_,_,w,hw,hl⟩ := hp'.exists_isCycle_length_le_add_of_ne
      ((Walk.isPath_copy _ _ _).mpr hr') hne
    have hb := hg v w hw
    simp only [Walk.length_copy, BasedWalk.length_toWalk] at hl
    omega
  have hjk : j = k := by
    apply Fin.ext
    have hl := congrArg Walk.length hw
    simp only [Walk.length_copy, BasedWalk.length_toWalk] at hl
    omega
  subst k
  apply congrArg (Sigma.mk j)
  apply Subtype.ext
  apply BasedWalk.vertices_injective
  have hs := congrArg Walk.support hw
  simpa only [Walk.support_copy, BasedWalk.support_toWalk] using hs

private theorem shortOddPaths_card
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    Nat.card (ShortOddPaths E c i) = cosetCount m hm (!i) := by
  have (k : Fin 3) : Finite {p : BasedWalk (graph c.cosetFamily) (2*k.val+1)
      (base c.cosetFamily i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by
      rw [completion_card_odd_paths E c hoverlap]
      exact Nat.ne_of_gt (Nat.mul_pos (degree_pos m hm i) (by rw [binaryParameters_q]; positivity)))
  rw [Nat.card_sigma]
  simp only [completion_card_odd_paths E c hoverlap]
  simp [Fin.sum_univ_succ, cosetCount]
  ring

/-- The three short odd path counts give the native lower bound at each type. -/
theorem completion_card_coset_ge [Finite M]
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    cosetCount m hm i ≤ Nat.card (M ⧸ c.cosetFamily i) := by
  have h := Nat.card_le_card_of_injective
    ((fiberEquiv E c (!(!i))) ∘ shortOddEndpoint E c (!i))
    ((fiberEquiv E c (!(!i))).injective.comp (shortOddEndpoint_injective E c hoverlap (!i)))
  rw [shortOddPaths_card E c hoverlap] at h
  simpa only [Bool.not_not] using h

/-- Both coset bounds are sharp under the original full extension order bound. -/
theorem completion_card_coset_eq [Finite M]
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) = cosetCount m hm i :=
  le_antisymm (completion_card_coset_le E c horder i) (completion_card_coset_ge E c hoverlap i)

/-- Equality of full group orders, without any native recognition premise. -/
theorem completion_order_eq [Finite M]
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) : Nat.card M = Nat.card E.carrier := by
  have hi : (c.cosetFamily true).index = (E.family true).index := by
    change Nat.card (M ⧸ c.cosetFamily true) = Nat.card (E.carrier ⧸ E.family true)
    rw [E.card_coset_eq_native (conj_injective m hm), native_family]
    rw [card_coset m hm]
    exact completion_card_coset_eq E c hoverlap horder true
  have hl : Nat.card (c.cosetFamily true) = Nat.card (E.family true) := by
    rw [← E.completion_family (native_generate m hm)]
    exact c.right_card.trans (E.completion (native_generate m hm)).right_card.symm
  calc
    Nat.card M = (c.cosetFamily true).index * Nat.card (c.cosetFamily true) :=
      (c.cosetFamily true).index_mul_card.symm
    _ = (E.family true).index * Nat.card (E.family true) := by rw [hi, hl]
    _ = Nat.card E.carrier := (E.family true).index_mul_card

/-- Exhaustion by short odd paths bounds opposite vertices by distance five. -/
theorem completion_opposite_dist_le [Finite M]
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool)
    (v : Vertex c.cosetFamily) (hv : v.type = !i) :
    (graph c.cosetFamily).dist (base c.cosetFamily i) v ≤ 5 := by
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have hcard : Nat.card (ShortOddPaths E c i) =
      Nat.card {v : Vertex c.cosetFamily // v.type = !i} := by
    rw [shortOddPaths_card E c hoverlap, Nat.card_congr (fiberEquiv E c (!i)),
      completion_card_coset_eq E c hoverlap horder]
  have hs := ((Nat.bijective_iff_injective_and_card (shortOddEndpoint E c i)).mpr
    ⟨shortOddEndpoint_injective E c hoverlap i, hcard⟩).2
  obtain ⟨⟨k,p,hp⟩,he⟩ := hs ⟨v,hv⟩
  have he' : p.endpoint = v := congrArg Subtype.val he
  have hd := SimpleGraph.dist_le p.toWalk
  rw [BasedWalk.length_toWalk, he'] at hd
  exact hd.trans (by omega)

/-- The full order bound implies diameter at most six, uniformly also at q=4. -/
theorem completion_diameter_le [Finite M]
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier)
    (v w : Vertex c.cosetFamily) : (graph c.cosetFamily).dist v w ≤ 6 := by
  have hb (i : Bool) (y : Vertex c.cosetFamily) :
      (graph c.cosetFamily).dist (base c.cosetFamily i) y ≤ 6 := by
    by_cases hy : y.type = !i
    · exact (completion_opposite_dist_le E c hoverlap horder i y hy).trans (by omega)
    · obtain ⟨z,hz,_,_⟩ := completion_thick E c hoverlap y y y
      have hztype : z.type = !i := by
        have hn := hz.1
        cases i <;> cases hy' : y.type <;> cases hz' : z.type <;> simp_all
      have hd := completion_opposite_dist_le E c hoverlap horder i z hztype
      have ht := (completion_connected E c).dist_triangle (u := base c.cosetFamily i) (v := z) (w := y)
      rw [dist_eq_one_iff_adj.mpr hz.symm] at ht
      omega
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hd := hb v.type (g⁻¹ • w)
  have ht := (completion_graphAction E c).dist_smul g (base c.cosetFamily v.type) (g⁻¹ • w)
  rw [hg, smul_inv_smul] at ht
  exact ht.le.trans hd

/-- The hexagon has an actual twelve-cycle, obtained from a seven-path and
its shorter geodesic with the same endpoints. -/
theorem completion_twelve_cycle [Finite M]
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 12 := by
  have htwo : HasTwoNeighbors (graph c.cosetFamily) := by
    intro v a
    obtain ⟨z,hz,ha,_⟩ := completion_thick E c hoverlap v a a
    exact ⟨z,hz,ha⟩
  let x := base c.cosetFamily false
  obtain ⟨p,hp,_⟩ := exists_extension htwo (by decide : 0 ≤ 7)
    (BasedWalk.ofWalk (Walk.nil : (graph c.cosetFamily).Walk x x)) (by trivial)
  have hg := completion_cycle_length_ge_twelve E c hoverlap
  have hp' := isPath_of_nonbacktracking_of_cycle_bound
    (N := 11) (fun v w hw => by have := hg v w hw; omega) p hp (by omega)
  have htype : p.endpoint.type = !false := by
    have he := QuadrangleRecognition.even_length_iff (G := graph c.cosetFamily)
      (fun v : Vertex c.cosetFamily => v.type) (fun h => h.1) p.toWalk
    have hn : ¬ Even p.toWalk.length := by rw [BasedWalk.length_toWalk]; decide
    have hn' := fun h => hn (he.mpr h)
    change ¬ (false = p.endpoint.type) at hn'
    exact Bool.eq_not_iff.mpr (Ne.symm hn')
  have hd := completion_opposite_dist_le E c hoverlap horder false p.endpoint htype
  change (graph c.cosetFamily).dist x p.endpoint ≤ 5 at hd
  obtain ⟨r,hr,hl⟩ := (completion_connected E c).exists_path_of_dist x p.endpoint
  have hne : p.toWalk ≠ r := by
    intro he
    have he' := congrArg Walk.length he
    rw [BasedWalk.length_toWalk,hl] at he'
    omega
  obtain ⟨v,_,_,w,hw,hlen⟩ := hp'.exists_isCycle_length_le_add_of_ne hr hne
  refine ⟨v,w,hw,?_⟩
  have hb := hg v w hw
  rw [BasedWalk.length_toWalk,hl] at hlen
  omega

/-- The literal six-path count from the arms vertex. -/
theorem completion_card_six_paths
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) 6 (base c.cosetFamily false) //
      p.Nonbacktracking} = (q^3+1)*q^9 := by
  have hc := completion_card_neighbors E c hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.ne_of_gt (degree_pos m hm _))
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type :=
    fun h => Bool.eq_not_iff.mpr h.1.symm
  rw [card_nonbacktracking_succ (graph c.cosetFamily) (fun v => v.type) (SmallCompletion.degree m hm) hf hc]
  simp [SmallCompletion.degree, forwardCount]
  ring

/-- The order bound supplies the actual F.4.7 smallness witness at distance six.
The count works at the smallest nonbinary parameter q=4. -/
theorem completion_small [Finite M] (hm2 : 1 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ x y : Vertex c.cosetFamily, (graph c.cosetFamily).dist x y = 6 ∧
      ∃ p r : (graph c.cosetFamily).Walk x y, p.length = 6 ∧ r.length = 6 ∧ p ≠ r := by
  classical
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have hq : 4 ≤ q := by
    rw [binaryParameters_q]
    exact pow_le_pow_right₀ (by decide : 1 ≤ 2) hm2
  have hv : Nat.card (Vertex c.cosetFamily) ≤ (q^3+q+2)*(q^8+q^4+1) := by
    rw [Nat.card_congr (vertexEquivSum c.cosetFamily), Nat.card_sum]
    have h := Nat.add_le_add (completion_card_coset_le E c horder false)
      (completion_card_coset_le E c horder true)
    exact h.trans_eq (by simp only [cosetCount, SmallCompletion.degree, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]; ring)
  have hp : Nat.card (Vertex c.cosetFamily) <
      Nat.card {p : BasedWalk (graph c.cosetFamily) 6 (base c.cosetFamily false) //
        p.Nonbacktracking} := by
    rw [completion_card_six_paths E c hoverlap]
    apply lt_of_le_of_lt hv
    have h1 : q^3+q+2 ≤ 2*q^3 := by
      have hp : q^2 ≤ q^3 := pow_le_pow_right₀ (by omega : 1 ≤ q) (by decide : 2 ≤ 3)
      nlinarith
    have h2 : q^8+q^4+1 ≤ 2*q^8 := by
      have h4 : 2 ≤ q^4 := (by decide : 2 ≤ 4).trans
        (hq.trans (Nat.le_self_pow (by decide : 4 ≠ 0) _))
      nlinarith [show (q^4)^2 = q^8 by ring]
    have hpos : 0 < q^9 := pow_pos (by omega) _
    calc
      _ ≤ (2*q^3)*(2*q^8) := Nat.mul_le_mul h1 h2
      _ = 4*q^11 := by ring
      _ ≤ q*q^11 := Nat.mul_le_mul_right _ hq
      _ = q^12 := by ring
      _ < q^12+q^9 := Nat.lt_add_of_pos_right hpos
      _ = (q^3+1)*q^9 := by ring
  have hn : ¬ Function.Injective (fun p :
      {p : BasedWalk (graph c.cosetFamily) 6 (base c.cosetFamily false) // p.Nonbacktracking} =>
      p.val.endpoint) := fun hi => (Nat.not_le_of_gt hp) (Nat.card_le_card_of_injective _ hi)
  obtain ⟨p,r,he,hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨base c.cosetFamily false,p.val.endpoint,
    geodesic_of_half_girth (completion_connected E c)
      (completion_cycle_length_ge_twelve E c hoverlap) p.val p.property,
    p.val.toWalk,r.val.toWalk.copy rfl he.symm,BasedWalk.length_toWalk _,?_,?_⟩
  · simp only [Walk.length_copy,BasedWalk.length_toWalk]
  · intro hh
    apply hne
    apply Subtype.ext
    apply BasedWalk.vertices_injective 6 (base c.cosetFamily false)
    have hs := congrArg Walk.support hh
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
