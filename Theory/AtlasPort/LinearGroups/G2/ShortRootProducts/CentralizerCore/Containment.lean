module

public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Coordinates

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Subgroup hiding mul
open Atlas.G2.LieParabolicSetup
/-!
# The full short-root centralizer lies in the long parabolic

An octonion fixed by a nonzero C root and having square zero lies in the
span of the first three basis vectors. An automorphism centralizing that
root sends the second and third basis vectors into this space. Their
product is the first basis vector, so the automorphism preserves its line.
This puts the entire centralizer in the actual singular-point stabilizer.
The existing relative factorization consequently applies to every element
of the full centralizer, with no additional placement hypothesis.

The marked J₂ local-action comparison uses this result in K.4.5. It also
supplies the concrete short-root containment underlying B.4.6(6).
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.88–90 and p.460. The octonion table and
root maps are the attributed ATLAS definitions imported above; no additional
upstream source is copied here.
-/

@[expose] public section
namespace Atlas.G2.ShortRootProducts.CentralizerCore
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
private theorem fixed_square_zero (r : K) (hr : r ≠ 0) (x : Carrier K)
    (hf : (rootC r).val x = x) (hs : mul x x = 0) :
    x = ![x 0,x 1,x 2,0,0,0,0,0] := by
  have h1 := congrFun hf 1
  have h2 := congrFun hf 2
  have h3 := congrFun hf 3
  simp [rootC, rootCEquiv, rootCLinear, rootCApply] at h1 h2 h3
  have h5 : x 5 = 0 := h1.resolve_left hr
  have h6 : x 6 = 0 := h2.resolve_left hr
  have h7 : x 7 = 0 := h3.resolve_left hr
  have h33 := congrFun hs 3
  have h44 := congrFun hs 4
  simp [mul,h5,h6,h7] at h33 h44
  ext i
  fin_cases i <;> simp [h5,h6,h7,h33,h44]

omit [CharP K 2] in
private theorem image_shape (r : K) (hr : r ≠ 0) (g : Model K)
    (hc : Commute g (rootC r)) (i : Fin 8)
    (hi : (rootC r).val (basisVector i) = basisVector i)
    (hs : mul (basisVector i : Carrier K) (basisVector i) = 0) :
    g.val (basisVector i) =
      ![g.val (basisVector i) 0,g.val (basisVector i) 1,g.val (basisVector i) 2,0,0,0,0,0] := by
  apply fixed_square_zero r hr
  · have h := congrArg (fun k : Model K => k.val (basisVector i)) hc.eq
    change g.val ((rootC r).val (basisVector i)) = (rootC r).val (g.val (basisVector i)) at h
    rw [hi] at h
    exact h.symm
  · rw [← automorphism_mul,hs,map_zero]

theorem centralizer_rootC_le_parabolic (r : K) (hr : r ≠ 0) :
    centralizer ({rootC r} : Set (Model K)) ≤ parabolic₂ := by
  intro g hg
  have hc : Commute g (rootC r) := mem_centralizer_singleton_iff.mp hg
  have h1 := image_shape r hr g hc 1
    (by ext i; fin_cases i <;> simp [rootC,rootCEquiv,rootCLinear,rootCApply,basisVector])
    (by ext i; fin_cases i <;> simp [mul,basisVector])
  have h2 := image_shape r hr g hc 2
    (by ext i; fin_cases i <;> simp [rootC,rootCEquiv,rootCLinear,rootCApply,basisVector])
    (by ext i; fin_cases i <;> simp [mul,basisVector])
  have hm : mul (basisVector 1 : Carrier K) (basisVector 2) = basisVector 0 := by
    ext i; fin_cases i <;> simp [mul,basisVector,CharTwo.neg_eq]
  have he := automorphism_mul g (basisVector 1) (basisVector 2)
  rw [hm,h1,h2] at he
  let a := g.val (basisVector 1) 1 * g.val (basisVector 2) 2 +
    g.val (basisVector 1) 2 * g.val (basisVector 2) 1
  have ha : g.val (basisVector 0) = a • (basisVector 0 : Carrier K) := by
    rw [he]
    ext i
    fin_cases i <;> simp [mul,basisVector,a,CharTwo.neg_eq,CharTwo.sub_eq_add]
  have hn : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    apply first_basis_ne_zero (K := K)
    exact g.val.injective (ha.trans g.val.map_zero.symm)
  change g ∈ parabolic
  rw [parabolic_eq_pointStabilizer]
  exact (mem_pointStabilizer_iff g).mpr
    ⟨Units.mk0 a hn, by simpa only [Units.smul_def,Units.val_mk0] using ha⟩

/-- The actual full centralizer, with the relative-parabolic premise discharged. -/
theorem centralizer_rootC_eq_product (r : K) (hr : r ≠ 0) :
    centralizer ({rootC r} : Set (Model K)) = centralizerProduct := by
  rw [← parabolic_inf_centralizer_rootC r hr,
    inf_eq_right.mpr (centralizer_rootC_le_parabolic r hr)]

/-- Every element of the full centralizer has the checked A/B/C and SL₂ factors. -/
theorem centralizer_rootC_factor (r : K) (hr : r ≠ 0) {g : Model K}
    (hg : g ∈ centralizer ({rootC r} : Set (Model K))) :
    ∃ (p : Multiplicative (K × K)) (t : K) (M : Matrix.SpecialLinearGroup (Fin 2) K),
      g = longRootHom p * rootC t * PairStabilizer.blockHom M :=
  parabolic_centralizer_factor r hr (centralizer_rootC_le_parabolic r hr hg) hg

end Atlas.G2.ShortRootProducts.CentralizerCore
