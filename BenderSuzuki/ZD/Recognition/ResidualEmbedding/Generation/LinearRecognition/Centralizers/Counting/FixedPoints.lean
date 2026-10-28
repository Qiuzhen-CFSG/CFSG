module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts

/-!
# Fixed cosets and the distinguished centralizer orbit

Fusion control in `M` puts every coset fixed by an involution `v ∈ M`
in the orbit of the base coset under `C_G(v)`: adjust a coset representative
by an element of `M` to make it commute with `v`. The local factorization
`C_G(v) = Lᵥ C_D(v)` then identifies this orbit with the `Lᵥ`-orbit.
This uses the literal coset action and original two-point stabilizer.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 4.2(d), 12.4(e), and
the fixed-point calculation in the proof of Lemma 12.8.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The distinguished centralizer closure is transitive on all fixed cosets
of an involution of `D`, using local factorization and fusion control. -/
public theorem pair_involution_fixedPoints_eq_centralizerClosure_orbit
    (r : SimpleReduction Z M) {z t v : G}
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    {beta : G ⧸ M | v • beta = beta} =
      MulAction.orbit (centralizerClosure Z v) (QuotientGroup.mk 1 : G ⧸ M) := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have hvfix : v • alpha = alpha := by
    change v ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [baseCoset_stabilizer]
    exact hvD.1
  apply Set.Subset.antisymm
  · intro beta hbeta
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective beta
    have hgalpha : g • alpha = QuotientGroup.mk g := by
      change (QuotientGroup.mk (g * 1) : G ⧸ M) = QuotientGroup.mk g
      rw [mul_one]
    have hgfix : v • (g • alpha) = g • alpha := by
      rw [hgalpha]
      exact hbeta
    have hvconj : MulAut.conj g⁻¹ v ∈ M := by
      rw [← baseCoset_stabilizer M]
      apply MulAction.mem_stabilizer_iff.mpr
      change (g⁻¹ * v * (g⁻¹)⁻¹) • alpha = alpha
      rw [inv_inv]
      rw [mul_smul, mul_smul, hgfix, inv_smul_smul]
    obtain ⟨S, hSM, hf⟩ := r.fusion
    obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hv
      (IsInvolution.map_of_injective hv (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective)
      hvD.1 hvconj (isConj_iff.mpr ⟨g⁻¹, rfl⟩)
    have hc : g * (m : G) ∈ centralizer ({v} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      change (m : G) * v * (m : G)⁻¹ = g⁻¹ * v * (g⁻¹)⁻¹ at hm
      rw [inv_inv] at hm
      calc
        (g * (m : G)) * v = g * ((m : G) * v * (m : G)⁻¹) * m := by group
        _ = v * (g * (m : G)) := by rw [hm]; group
    change g * (m : G) ∈ (centralizer ({v} : Set G) : Set G) at hc
    rw [show (centralizer ({v} : Set G) : Set G) = _ from
      hlocal.centralizer_factorization v hvD hv] at hc
    obtain ⟨l, hl, d, hd, he⟩ := hc
    change l * d = g * (m : G) at he
    have hmfix : (m : G) • alpha = alpha := by
      change (m : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
      rw [baseCoset_stabilizer]
      exact m.property
    have hdfix : d • alpha = alpha := by
      change d ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
      rw [baseCoset_stabilizer]
      exact hd.1.1
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨l, hl⟩, ?_⟩
    change l • alpha = QuotientGroup.mk g
    calc
      l • alpha = (l * d) • alpha := by rw [mul_smul, hdfix]
      _ = (g * (m : G)) • alpha := by rw [he]
      _ = QuotientGroup.mk g := by
        rw [mul_smul, hmfix]
        exact hgalpha
  · intro beta hbeta
    obtain ⟨l, rfl⟩ := MulAction.mem_orbit_iff.mp hbeta
    change v • ((l : G) • alpha) = (l : G) • alpha
    have hc := mem_centralizer_singleton_iff.mp (centralizerClosure_le Z v l.property)
    rw [← mul_smul, ← hc, mul_smul, hvfix]

end BenderSuzuki.ZD
