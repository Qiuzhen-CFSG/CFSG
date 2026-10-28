module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversalIndices

/-!
# Reversing the genuine critical geodesic

The second kernel identity of F.9.15 and faithfulness make the positive-rank
actor detect a neighbor β of γ. The actual conjugate span selects β. Dropping
the initial edge, reversing, and adjoining β constructs a walk of length b;
minimality of the critical distance proves it geodesic after normalization.

Both edges require stabilizer adjustments. The new left conjugator is
h⁻¹ g_b⁻¹ t with h,t in H, not in general g_b⁻¹. `Reversal` records these
factors and the complete vertex-by-vertex walk identity. Its witness is
constructed, not a symmetry assumption. F.9.11's length bound and F.9.15's
literal kernel identity remain explicit earlier-result hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.12–17,
printed pp.322–324, applied in 13.8.25 on printed p.962. This module supplies
the graph pair; actor-specific module eligibility remains separate.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] {L T H V : Subgroup G}

def translate (a : G0 L T H) : graph L T H →g graph L T H where
  toFun v := a • v
  map_rel' h := ⟨h.1, h.2.smul _ a⟩

theorem firstKernel_map_le (a : G0 L T H) (v : Vertex L T H) :
    (firstKernel L T H v).map (MulAut.conj (a : G)).toMonoidHom ≤
      firstKernel L T H (a • v) := by
  apply le_inf
  · rw [vertexGroup_smul]
    exact map_mono inf_le_left
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    have hadj : (graph L T H).Adj v (a⁻¹ • w) := by
      have hh := (translate a⁻¹).map_rel hw
      change (graph L T H).Adj (a⁻¹ • (a • v)) (a⁻¹ • w) at hh
      simpa only [inv_smul_smul] using hh
    have hvw : firstKernel L T H v ≤ vertexGroup L T H (a⁻¹ • w) :=
      inf_le_right.trans ((iInf_le _ (a⁻¹ • w)).trans (iInf_le _ hadj))
    have hh := map_mono (f := (MulAut.conj (a : G)).toMonoidHom) hvw
    rw [← vertexGroup_smul, smul_inv_smul] at hh
    exact hh

theorem firstKernel_smul (a : G0 L T H) (v : Vertex L T H) :
    firstKernel L T H (a • v) =
      (firstKernel L T H v).map (MulAut.conj (a : G)).toMonoidHom := by
  apply le_antisymm _ (firstKernel_map_le a v)
  have hh := map_mono (f := (MulAut.conj (a : G)).toMonoidHom)
    (firstKernel_map_le a⁻¹ (a • v))
  have hc := conjugate_inverse_cancel (a : G)⁻¹ (firstKernel L T H (a • v))
  simp only [inv_inv] at hc
  simpa only [inv_smul_smul, Subgroup.coe_inv, hc] using hh

def inG0 (h : H) : G0 L T H := ⟨h, (show H ≤ G0 L T H from le_sup_right) h.property⟩

theorem inG0_one (h : H) : inG0 (L := L) (T := T) h • base L T H true = base L T H true := by
  change inG0 h ∈ MulAction.stabilizer (G0 L T H) (base L T H true)
  rw [CosetGeometry.stabilizer_base]
  exact h.property

theorem neighbor (a : G0 L T H) :
    (graph L T H).Adj (a • base L T H false) (a • base L T H true) :=
  (translate a).map_rel ⟨Bool.false_ne_true, CosetGeometry.incident_base _ _ _⟩

theorem exists_neighbor_transporter {w : Vertex L T H}
    (hw : (graph L T H).Adj (base L T H true) w) :
    ∃ h : H, inG0 (L := L) (T := T) h • base L T H false = w := by
  have htype : w.type = false := by
    have ht := hw.1
    change true ≠ w.type at ht
    cases he : w.type <;> simp_all
  obtain ⟨a, ha, hw⟩ := (CosetGeometry.incident_base_iff _ true w).mp hw.2
  have haH : (a : G) ∈ H := ha
  refine ⟨⟨a, haH⟩, ?_⟩
  have he : inG0 (L := L) (T := T) (⟨a, haH⟩ : H) = a := Subtype.ext rfl
  rw [he]
  rcases w with ⟨i, q⟩
  dsimp at htype
  subst i
  change CosetGeometry.Vertex.mk false (a • ((1 : G0 L T H) : _)) =
    CosetGeometry.Vertex.mk false q
  apply congrArg (CosetGeometry.Vertex.mk false)
  simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using hw

/-- Select a neighbor from the actual conjugate span, not a reversed-pair witness. -/
theorem neighbor_witness (c : CriticalPair L T H V)
    (hV : ¬ c.Vgamma ≤ firstKernel L T H (base L T H true)) :
    ∃ h : H, ¬ V.map (MulAut.conj ((c.gb * inG0 h : G0 L T H) : G)).toMonoidHom ≤
      firstKernel L T H (base L T H true) := by
  by_contra! hn
  apply hV
  apply (map_le_iff_le_comap).mpr
  apply (closure_le _).mpr
  rintro x ⟨h, hh, v, hv, rfl⟩
  have hm := hn ⟨h, hh⟩ (mem_map_of_mem
    (MulAut.conj ((c.gb * inG0 (⟨h, hh⟩ : H) : G0 L T H) : G)).toMonoidHom hv)
  change (MulAut.conj (c.gb : G)) (h * v * h⁻¹) ∈ firstKernel L T H (base L T H true)
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, inG0, mul_inv_rev, mul_assoc] using hm

/-- The reversed segment before edge normalization. -/
def reversedWalk (c : CriticalPair L T H V) {β : Vertex L T H}
    (hβ : (graph L T H).Adj β c.gamma) :
    (graph L T H).Walk β (base L T H true) :=
  ((c.path.drop 1).copy c.first rfl).reverse.cons hβ

theorem reversedWalk_length (c : CriticalPair L T H V) {β : Vertex L T H}
    (hβ : (graph L T H).Adj β c.gamma) (hb : 1 ≤ c.path.length) :
    (reversedWalk c hβ).length = c.path.length := by
  simp only [reversedWalk, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length]
  omega

theorem reversedWalk_first (c : CriticalPair L T H V) {β : Vertex L T H}
    (hβ : (graph L T H).Adj β c.gamma) :
    (reversedWalk c hβ).getVert 1 = c.gamma := by
  simp [reversedWalk]

theorem reversedWalk_previous (c : CriticalPair L T H V) {β : Vertex L T H}
    (hβ : (graph L T H).Adj β c.gamma) (hb : 3 ≤ c.path.length) :
    (reversedWalk c hβ).getVert (c.path.length - 1) = c.second := by
  rw [reversedWalk, SimpleGraph.Walk.getVert_cons _ _ (by omega),
    SimpleGraph.Walk.getVert_reverse]
  simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length,
    SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.drop_getVert]
  have he : 1 + (c.path.length - 1 - (c.path.length - 1 - 1)) = 2 := by omega
  rw [he]

/-- Two stabilizer factors record the normalization of both edges. -/
structure Reversal (c : CriticalPair L T H V) where
  adjustment : H
  terminalAdjustment : H
  pair : CriticalPair L T H V
  beta_critical : ¬ V.map (MulAut.conj
    ((c.gb * inG0 adjustment : G0 L T H) : G)).toMonoidHom ≤
      firstKernel L T H (base L T H true)
  terminal_zero : inG0 (L := L) (T := T) terminalAdjustment • base L T H false = c.second
  gamma_eq : pair.gamma = (c.gb * inG0 adjustment)⁻¹ • base L T H true
  gb_eq : pair.gb = (c.gb * inG0 adjustment)⁻¹ * inG0 terminalAdjustment
  walk_eq : ∀ n, pair.path.getVert n = (c.gb * inG0 adjustment)⁻¹ •
    (reversedWalk c (show (graph L T H).Adj
      ((c.gb * inG0 adjustment) • base L T H false) c.gamma from by
        have hh := neighbor (c.gb * inG0 adjustment)
        simpa only [mul_smul, inG0_one, c.gb_one] using hh)).getVert n

set_option backward.isDefEq.respectTransparency false in
/-- F.9.17's geometric construction. Its earlier input is exactly the
failure of the first-kernel containment at gamma, as supplied by F.9.15.
Critical distance minimality proves the newly constructed walk geodesic. -/
theorem exists_reversal (c : CriticalPair L T H V)
    (hb : 3 ≤ c.path.length)
    (hV : ¬ c.Vgamma ≤ firstKernel L T H (base L T H true)) :
    Nonempty (Reversal c) := by
  obtain ⟨h, hbad⟩ := neighbor_witness c hV
  let k : G0 L T H := c.gb * inG0 h
  have hk : k • base L T H true = c.gamma := by
    simp only [k, mul_smul, inG0_one, c.gb_one]
  have hadj : (graph L T H).Adj (k • base L T H false) c.gamma := by
    rw [← hk]
    exact neighbor k
  let p := reversedWalk c hadj
  have hp : p.length = c.path.length := reversedWalk_length c hadj (by omega)
  let w : (graph L T H).Walk (base L T H false) (k⁻¹ • base L T H true) :=
    (p.map (translate k⁻¹)).copy (inv_smul_smul k _) rfl
  have hwlen : w.length = c.path.length := by
    dsimp only [w]
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
    exact hp
  have hwget (n : ℕ) : w.getVert n = k⁻¹ • p.getVert n := by
    dsimp only [w]
    rw [SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map]
    rfl
  have hwfirst : w.getVert 1 = base L T H true := by
    rw [hwget, reversedWalk_first, ← hk, inv_smul_smul]
  have hwprev : w.getVert (w.length - 1) = k⁻¹ • c.second := by
    rw [hwlen, hwget, reversedWalk_previous c hadj hb]
  have hcrit : ¬ V ≤ firstKernel L T H (k⁻¹ • base L T H true) := by
    intro hv
    have hh := map_mono (f := (MulAut.conj (k : G)).toMonoidHom) hv
    rw [← firstKernel_smul, smul_inv_smul] at hh
    exact hbad hh
  have hdist : (graph L T H).dist (base L T H false)
      (k⁻¹ • base L T H true) = w.length := by
    apply le_antisymm (SimpleGraph.dist_le w)
    rw [hwlen, c.length_eq]
    exact Nat.sInf_le ⟨_, ⟨w⟩, rfl, hcrit⟩
  have hadj₂ : (graph L T H).Adj (base L T H true) c.second := by
    have hh := c.path.adj_getVert_succ (i := 1) (by omega)
    rwa [c.first] at hh
  obtain ⟨t, ht⟩ := exists_neighbor_transporter hadj₂
  let d : CriticalPair L T H V := {
    gamma := k⁻¹ • base L T H true
    path := w
    length_eq := hwlen.trans c.length_eq
    distance_eq := hdist
    critical := hcrit
    first := hwfirst
    gb := k⁻¹ * inG0 t
    gb_zero := by rw [mul_smul, ht, hwprev]
    gb_one := by rw [mul_smul, inG0_one] }
  exact ⟨⟨h, t, d, hbad, ht, rfl, rfl, hwget⟩⟩


/-- The actual conjugator includes both edge-stabilizer adjustments. -/
theorem Reversal.conjugator_val {c : CriticalPair L T H V} (r : Reversal c) :
    (r.pair.gb : G) = (r.adjustment : G)⁻¹ * (c.gb : G)⁻¹ * r.terminalAdjustment := by
  rw [r.gb_eq]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inG0]

theorem Reversal.beta_adj {c : CriticalPair L T H V} (r : Reversal c) :
    (graph L T H).Adj ((c.gb * inG0 r.adjustment) • base L T H false) c.gamma := by
  have hh := neighbor (c.gb * inG0 r.adjustment)
  simpa only [mul_smul, inG0_one, c.gb_one] using hh

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Representation.BinaryOffender

/-- The second intersection identity of F.9.15 supplies the geometric
noncontainment as soon as the actual quotient actor has positive rank. -/
theorem not_le_firstKernel_of_rank
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (V₃ V₁ : Subgroup G) (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ)
    (hUV : c.Ugamma V₃ ≤ c.Vgamma) (hVH : c.Vgamma ≤ H)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) V₁)
    (hrank : 0 < rank (Source.starImage H (c.Ugamma V₃))) :
    ¬ c.Vgamma ≤ firstKernel L T H (base L T H true) := by
  intro hker
  have hn : c.Vgamma ≤ normalizer (V₁ : Set G) :=
    hVH.trans (s.centralizes.trans (centralizer_le_normalizer _))
  have he : c.Ugamma V₃ ≤ Source.Egamma c.Vgamma (Source.UH H V₃) V₁ :=
    (le_inf hUV (hUV.trans hker)).trans hF915.le
  have hc : ⁅c.Ugamma V₃, Source.UH H V₃⁆ ≤ V₁ :=
    (commutator_mono he le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hn)
  have hd : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ :=
    le_antisymm (commutatorPreimage_le _ _ _) (le_commutatorPreimage le_rfl hc)
  rw [rank, ← s.Dgamma_relIndex _ (hUV.trans hVH) hfaith, hd,
    relIndex_self] at hrank
  simp at hrank

/-- Construct the reversed graph pair from the source rank, faithfulness,
and the explicit F.9.11 and F.9.15 conclusions. -/
theorem exists_reversal_of_rank
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (V₃ V₁ : Subgroup G) (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ) (hb : 3 ≤ c.path.length)
    (hUV : c.Ugamma V₃ ≤ c.Vgamma) (hVH : c.Vgamma ≤ H)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) V₁)
    (hrank : 0 < rank (Source.starImage H (c.Ugamma V₃))) :
    Nonempty (Reversal c) :=
  exists_reversal c hb (not_le_firstKernel_of_rank V₃ V₁ c s hfaith hUV hVH hF915 hrank)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
