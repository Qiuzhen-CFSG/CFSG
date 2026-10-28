module

public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.LinearCombination

/-!
# The four-dimensional fixed space of an octonion involution

In characteristic different from two, a nonidentity octonion involution has
complementary positive and negative eigenspaces. The polar norm is nondegenerate
on each. Right multiplication by a negative eigenvector of nonzero norm
identifies the eigenspaces, so both have dimension four. No finite-field or
involution-conjugacy hypothesis is used.

This supplies the dimension input to `InvolutionFusion.involutions_isConj`, used
in the ordinary G₂ multiplier argument of Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1. The norm and multiplication conventions
come from Gerald Höhn and the ATLAS contributors' licensed split-octonion port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion
open Atlas.SplitOctonion
variable {F : Type*} [Field F]

def fixedSpace (g : Model F) : Submodule F (Carrier F) where
  carrier := {x | g.val x = x}
  zero_mem' := map_zero _
  add_mem' hx hy := by change g.val _ = _; rw [map_add, hx, hy]
  smul_mem' r x hx := by change g.val _ = _; rw [map_smul, hx]

private def negSpace (g : Model F) : Submodule F (Carrier F) where
  carrier := {x | g.val x = -x}
  zero_mem' := by simp
  add_mem' hx hy := by change g.val _ = _; rw [map_add, hx, hy, neg_add]
  smul_mem' r x hx := by change g.val _ = _; rw [map_smul, hx, smul_neg]

@[simp] theorem mem_fixedSpace (g : Model F) (x : Carrier F) :
    x ∈ fixedSpace g ↔ g.val x = x := Iff.rfl
@[simp] private theorem mem_negSpace (g : Model F) (x : Carrier F) :
    x ∈ negSpace g ↔ g.val x = -x := Iff.rfl

private theorem twice (g : Model F) (hg : g ^ 2 = 1) (x : Carrier F) :
    g.val (g.val x) = x := congrArg (fun a : Model F => a.val x) hg

private theorem halves (hF : (2 : F) ≠ 0) (x y : Carrier F) :
    (2 : F)⁻¹ • (x + y) + (2 : F)⁻¹ • (x - y) = x := by
  rw [← smul_add]
  have he : x + y + (x - y) = (2 : F) • x := by module
  rw [he, smul_smul, inv_mul_cancel₀ hF, one_smul]

private theorem signed_decomposition (hF : (2 : F) ≠ 0) (g : Model F) (hg : g ^ 2 = 1)
    (x : Carrier F) : ∃ a ∈ fixedSpace g, ∃ b ∈ negSpace g, x = a + b := by
  refine ⟨(2 : F)⁻¹ • (x + g.val x), ?_, (2 : F)⁻¹ • (x - g.val x), ?_,
    (halves hF x (g.val x)).symm⟩
  · change g.val _ = _
    rw [map_smul, map_add, twice g hg, add_comm]
  · change g.val _ = -_
    rw [map_smul, map_sub, twice g hg, ← smul_neg]
    congr 1
    abel

private theorem signed_orthogonal (hF : (2 : F) ≠ 0) (g : Model F)
    {a b : Carrier F} (ha : a ∈ negSpace g) (hb : b ∈ fixedSpace g) :
    normPolar a b = 0 := by
  have h := automorphism_normPolar g a b
  change g.val a = -a at ha
  change g.val b = b at hb
  rw [ha, hb, map_neg, LinearMap.neg_apply] at h
  exact (mul_eq_zero.mp (show (2 : F) * normPolar a b = 0 by linear_combination -h)).resolve_left hF

private theorem neg_nondegenerate (hF : (2 : F) ≠ 0) (g : Model F) (hg : g ^ 2 = 1)
    {a : Carrier F} (ha : a ∈ negSpace g)
    (h : ∀ b ∈ negSpace g, normPolar a b = 0) : a = 0 := by
  apply normPolar_nondegenerate
  intro y
  obtain ⟨u, hu, v, hv, rfl⟩ := signed_decomposition hF g hg y
  rw [map_add, signed_orthogonal hF g ha hu, h v hv, zero_add]

private theorem exists_neg_nonisotropic (hF : (2 : F) ≠ 0) (g : Model F)
    (hg : g ^ 2 = 1) (hne : g ≠ 1) : ∃ a ∈ negSpace g, norm a ≠ 0 := by
  by_contra hn
  have hz : ∀ a ∈ negSpace g, norm a = 0 := by simpa using hn
  have hall : ∀ a ∈ negSpace g, a = 0 := by
    intro a ha
    apply neg_nondegenerate hF g hg ha
    intro b hb
    rw [normPolar_eq, hz _ ((negSpace g).add_mem ha hb), hz _ ha, hz _ hb]
    ring
  apply hne
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨a, ha, b, hb, rfl⟩ := signed_decomposition hF g hg x
  rw [hall b hb, add_zero]
  exact ha

/-- Right multiplication exchanges the two eigenspaces. -/
private def fixedNegEquiv (g : Model F) (v : Carrier F) (hv : v ∈ negSpace g)
    (hn : norm v ≠ 0) : fixedSpace g ≃ₗ[F] negSpace g where
  toFun x := ⟨mul x.val v, by
    change g.val (mul x.val v) = -mul x.val v
    rw [automorphism_mul, x.property, hv]
    simpa using mul_smul (-1 : F) x.val v⟩
  invFun y := ⟨(norm v)⁻¹ • mul y.val (conjugate v), by
    change g.val _ = _
    rw [map_smul, automorphism_mul, y.property, automorphism_conjugate, hv]
    have hc : conjugate (-v) = -conjugate v := by
      simpa using conjugate_smul (-1 : F) v
    rw [hc]
    have hm : mul (-y.val) (-conjugate v) = mul y.val (conjugate v) := by
      calc
        _ = -mul y.val (-conjugate v) := by simpa using smul_mul (-1 : F) y.val (-conjugate v)
        _ = mul y.val (conjugate v) := by
          have he : mul y.val (-conjugate v) = -mul y.val (conjugate v) := by
            simpa using mul_smul (-1 : F) y.val (conjugate v)
          rw [he, neg_neg]
    rw [hm]⟩
  left_inv x := by
    apply Subtype.ext
    exact (rightMulEquiv v hn).left_inv x.val
  right_inv y := by
    apply Subtype.ext
    exact (rightMulEquiv v hn).right_inv y.val
  map_add' x y := by apply Subtype.ext; exact add_mul x.val y.val v
  map_smul' r x := by apply Subtype.ext; exact smul_mul r x.val v

/-- Every nonidentity involution fixes exactly four octonion dimensions. -/
theorem fixedSpace_finrank (hF : (2 : F) ≠ 0) (g : Model F)
    (hg : g ^ 2 = 1) (hne : g ≠ 1) : Module.finrank F (fixedSpace g) = 4 := by
  have hsup : fixedSpace g ⊔ negSpace g = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, ha, b, hb, rfl⟩ := signed_decomposition hF g hg x
    exact Submodule.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩
  have hinf : fixedSpace g ⊓ negSpace g = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    have he : x = -x := hx.1.symm.trans hx.2
    have hz : (2 : F) • x = 0 := by
      calc
        _ = x + x := by module
        _ = 0 := by nth_rw 1 [he]; exact neg_add_cancel x
    exact (smul_eq_zero.mp hz).resolve_left hF
  obtain ⟨v, hv, hn⟩ := exists_neg_nonisotropic hF g hg hne
  have he := (fixedNegEquiv g v hv hn).finrank_eq
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace g) (negSpace g)
  rw [hsup, hinf, finrank_top, finrank_bot, carrier_finrank] at hd
  omega
end Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion

end
