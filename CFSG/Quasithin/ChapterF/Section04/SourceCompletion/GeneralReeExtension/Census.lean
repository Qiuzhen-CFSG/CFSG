module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Geometry
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.OctagonRecognition

/-!
# Order equality and smallness of full general Ree extension completions

Girth sixteen makes the odd walks of lengths 1,3,5,7 have distinct
endpoints. Their count is the native Suzuki-parabolic index. Cancellation
of the marked endpoint orders against the full extension bound gives order
equality. For q≥8 the number (q+1)q^11 of eight-walks exceeds the total
allowed vertices. A collision therefore gives distinct opposite geodesics;
nine-path transitivity then supplies diameter eight and a sixteen-cycle.

The extension factor is retained throughout. All positive Ree parameters,
including q=8, are covered. These results prove the numerical and geometric
part of F.4.24; a native group identification is not a consequence asserted
here and still requires the Ree specialization of F.4.17.
Source: Aschbacher–Smith F.4.6–7, F.4.13 and F.4.24,
printed pp.276–280,287–288.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon SimpleGraph.BasedWalk

private def degree (m : ℕ) (i : Bool) :=
  (if i then (2^(2*m+1))^2 else 2^(2*m+1)) + 1

variable {m : ℕ} (E : SourceExtension m) {M : Type*} [Group M] (c : Completion E M)

/-- The four short odd path counts retain the native unequal branching factors. -/
theorem completion_card_odd_paths (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (k : Fin 4) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) (2*k.val+1) (base c.cosetFamily false) //
      p.Nonbacktracking} = (2^(2*m+1)+1) * (2^(2*m+1))^(3*k.val) := by
  have hc := completion_card_neighbors E c hm hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> simp)
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  rw [card_nonbacktracking_succ (graph c.cosetFamily) (fun v => v.type) (degree m) hf hc]
  fin_cases k <;> simp [degree, forwardCount] <;> ring

/-- The exact eight-walk count from the marked linear vertex. -/
theorem completion_card_eight_paths (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) 8 (base c.cosetFamily false) //
      p.Nonbacktracking} = (2^(2*m+1)+1) * (2^(2*m+1))^11 := by
  have hc := completion_card_neighbors E c hm hoverlap
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> simp)
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := card_nonbacktracking_succ (graph c.cosetFamily) (fun v => v.type)
    (degree m) hf hc 7 (base c.cosetFamily false)
  rw [h]
  simp [degree, forwardCount]
  ring

private abbrev ShortOddPaths := Σ k : Fin 4,
  {p : BasedWalk (graph c.cosetFamily) (2*k.val+1) (base c.cosetFamily false) // p.Nonbacktracking}

private def trueFiberEquiv : {v : Vertex c.cosetFamily // v.type = true} ≃ M ⧸ c.cosetFamily true where
  toFun v := v.property ▸ v.val.coset
  invFun q := ⟨⟨true,q⟩,rfl⟩
  left_inv := by rintro ⟨⟨i,q⟩,h⟩; cases h; rfl
  right_inv _ := rfl

private def shortOddEndpoint : ShortOddPaths E c → {v : Vertex c.cosetFamily // v.type = true} :=
  fun ⟨k,p⟩ => ⟨p.val.endpoint, by
    have he := QuadrangleRecognition.even_length_iff (G := graph c.cosetFamily)
      (fun v : Vertex c.cosetFamily => v.type)
      (fun h => h.1) p.val.toWalk
    rw [BasedWalk.length_toWalk] at he
    have hodd : ¬ Even (2*k.val+1) := by rintro ⟨a,ha⟩; omega
    have hn := fun ht => hodd (he.mpr ht)
    change ¬ (false = p.val.endpoint.type) at hn
    cases h : p.val.endpoint.type <;> simp_all⟩

private theorem shortOddEndpoint_injective (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (shortOddEndpoint E c) := by
  rintro ⟨i,p,hp⟩ ⟨j,q,hq⟩ he
  have hend : p.endpoint = q.endpoint := congrArg Subtype.val he
  have hg := completion_cycle_length_ge_sixteen E c hm hoverlap
  have hp' := isPath_of_nonbacktracking_of_cycle_bound
    (N := 15) (fun v w hw => by have := hg v w hw; omega) p hp (by omega)
  have hq' := isPath_of_nonbacktracking_of_cycle_bound
    (N := 15) (fun v w hw => by have := hg v w hw; omega) q hq (by omega)
  have hw : p.toWalk = q.toWalk.copy rfl hend.symm := by
    by_contra hne
    obtain ⟨v,_,_,w,hw,hl⟩ := hp'.exists_isCycle_length_le_add_of_ne
      ((Walk.isPath_copy _ _ _).mpr hq') hne
    have hb := hg v w hw
    simp only [Walk.length_copy, BasedWalk.length_toWalk] at hl
    omega
  have hij : i = j := by
    apply Fin.ext
    have hl := congrArg Walk.length hw
    simp only [Walk.length_copy, BasedWalk.length_toWalk] at hl
    omega
  subst j
  apply congrArg (Sigma.mk i)
  apply Subtype.ext
  apply BasedWalk.vertices_injective
  have hs := congrArg Walk.support hw
  simpa only [Walk.support_copy, BasedWalk.support_toWalk] using hs

/-- The short odd paths give the native lower bound without an order hypothesis. -/
theorem completion_card_coset_ge [Finite M] (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    ReeF4.SmallCompletion.cosetCount m true ≤ Nat.card (M ⧸ c.cosetFamily true) := by
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have (k : Fin 4) : Finite {p : BasedWalk (graph c.cosetFamily) (2*k.val+1)
      (base c.cosetFamily false) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [completion_card_odd_paths E c hm hoverlap]; positivity)
  have hc : Nat.card (ShortOddPaths E c) = ReeF4.SmallCompletion.cosetCount m true := by
    rw [Nat.card_sigma]
    simp only [completion_card_odd_paths E c hm hoverlap]
    simp [Fin.sum_univ_succ, ReeF4.SmallCompletion.cosetCount]
    ring
  rw [← hc]
  exact Nat.card_le_card_of_injective ((trueFiberEquiv E c) ∘ shortOddEndpoint E c)
    ((trueFiberEquiv E c).injective.comp (shortOddEndpoint_injective E c hm hoverlap))

/-- The full extension order bound forces equality of group orders. -/
theorem completion_order_eq [Finite M] (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) : Nat.card M = Nat.card E.carrier := by
  have hi : (c.cosetFamily true).index = (E.family true).index := by
    change Nat.card (M ⧸ c.cosetFamily true) = Nat.card (E.carrier ⧸ E.family true)
    rw [E.card_coset_eq_native (ReeF4.SmallCompletion.conj_injective m hm)]
    change Nat.card (M ⧸ c.cosetFamily true) =
      Nat.card (ReeF4.Model m ⧸ ReeF4.SourceCompletion.family m true)
    rw [ReeF4.SmallCompletion.card_coset m hm]
    exact le_antisymm (completion_card_coset_le E c hm horder true)
      (completion_card_coset_ge E c hm hoverlap)
  have hgen : ReeF4.Parabolics.parabolic m .linear ⊔
      ReeF4.Parabolics.parabolic m .suzuki = ⊤ := by
    rw [sup_comm]
    exact GreenBook.LieModels.ReeFour.parabolics_generate m
  have hl : Nat.card (c.cosetFamily true) = Nat.card (E.family true) := by
    rw [← E.completion_family hgen]
    exact c.right_card.trans (E.completion hgen).right_card.symm
  calc
    Nat.card M = (c.cosetFamily true).index * Nat.card (c.cosetFamily true) :=
      (c.cosetFamily true).index_mul_card.symm
    _ = (E.family true).index * Nat.card (E.family true) := by rw [hi, hl]
    _ = Nat.card E.carrier := (E.family true).index_mul_card

/-- The order bound forces two distinct geodesics between vertices at distance eight,
exactly the smallness condition of F.4.7. -/
theorem completion_small [Finite M] (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ x y : Vertex c.cosetFamily, (graph c.cosetFamily).dist x y = 8 ∧
      ∃ p q : (graph c.cosetFamily).Walk x y, p.length = 8 ∧ q.length = 8 ∧ p ≠ q := by
  classical
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have hq : 8 ≤ 2^(2*m+1) :=
    pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 3 ≤ 2*m+1)
  have hv : Nat.card (Vertex c.cosetFamily) ≤
      ((2^(2*m+1))^2+2^(2*m+1)+2) * ((2^(2*m+1))^3+1) * ((2^(2*m+1))^6+1) := by
    rw [Nat.card_congr (vertexEquivSum c.cosetFamily), Nat.card_sum]
    have h := Nat.add_le_add (completion_card_coset_le E c hm horder false)
      (completion_card_coset_le E c hm horder true)
    exact h.trans_eq (by simp only [ReeF4.SmallCompletion.cosetCount,
      Bool.false_eq_true, ↓reduceIte]; ring)
  have hp : Nat.card (Vertex c.cosetFamily) <
      Nat.card {p : BasedWalk (graph c.cosetFamily) 8 (base c.cosetFamily false) //
        p.Nonbacktracking} := by
    rw [completion_card_eight_paths E c hm hoverlap]
    apply lt_of_le_of_lt hv
    let q := 2^(2*m+1)
    have h1 : q^2+q+2 ≤ 2*q^2 := by dsimp [q]; nlinarith
    have h2 : q^3+1 ≤ 2*q^3 := by
      have : 0 < q^3 := by dsimp [q]; positivity
      omega
    have h3 : q^6+1 ≤ 2*q^6 := by
      have : 0 < q^6 := by dsimp [q]; positivity
      omega
    calc
      _ ≤ (2*q^2)*(2*q^3)*(2*q^6) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = 8*q^11 := by ring
      _ < (q+1)*q^11 := Nat.mul_lt_mul_of_pos_right (by dsimp [q]; omega) (by dsimp [q]; positivity)
  have hn : ¬ Function.Injective (fun p :
      {p : BasedWalk (graph c.cosetFamily) 8 (base c.cosetFamily false) // p.Nonbacktracking} =>
      p.val.endpoint) := by
    intro hi
    exact (Nat.not_le_of_gt hp) (Nat.card_le_card_of_injective _ hi)
  obtain ⟨p,q,he,hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨base c.cosetFamily false,p.val.endpoint,
    completion_eight_geodesic E c hm hoverlap p.val p.property,p.val.toWalk,
    q.val.toWalk.copy rfl he.symm,BasedWalk.length_toWalk _,?_,?_⟩
  · simp only [Walk.length_copy,BasedWalk.length_toWalk]
  · intro hh
    apply hne
    apply Subtype.ext
    apply BasedWalk.vertices_injective 8 (base c.cosetFamily false)
    have hs := congrArg Walk.support hh
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

/-- Every order-bounded whole-overlap completion has the full octagon geometry. -/
theorem completion_octagon [Finite M] (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 16 ≤ p.length) ∧
      (∀ v w, (graph c.cosetFamily).dist v w ≤ 8) ∧
      (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 16) := by
  apply OctagonRecognition.octagon_of_small (completion_graphAction E c)
    (completion_connected E c) ?_ (completion_nine_transitive E c hm hoverlap)
    (·.type) (fun h => h.1) (fun h => (same_orbit_iff _ _ _).mpr h)
    (completion_small E c hm hoverlap horder)
  intro v a
  obtain ⟨z,hz,ha,_⟩ := completion_thick E c hm hoverlap v a a
  exact ⟨z,hz,ha⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
