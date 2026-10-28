module

public import Theory.PGroupCore
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Tactic.Group

/-!
# Centralizing two layers and the prime residual

If D centralizes a finite p-subgroup W and [D,Q] lies in W, the
commutator displacement embeds D/C_D(Q) in the function group Q → W.
Thus Oᵖ(D) centralizes Q. No characteristicness or centrality of W in Q
is required.

If Q and W are normal in G, their full two-layer fixer is normal. When
C_{Oᵖ(G)}(Q) lies in a normal subgroup R and O_p(G/R) is trivial, this
fixer lies in R: its residual lies in R and its image modulo R is a
normal p-subgroup. The quotients and residuals are all intrinsic.

Source: the coprime-action step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Proposition E.5.1, printed p.242. The displacement
calculation also underlies `CentralCharacteristicAutomorphisms`.
-/

open scoped commutatorElement

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Fixing a p-layer and the quotient forces the p-residual to centralize the group. -/
public theorem residual_centralizes_of_two_layer {p : ℕ} (D Q W : Subgroup G)
    (hW : IsPGroup p W) (hc : D ≤ centralizer (W : Set G))
    (hd : ⁅D, Q⁆ ≤ W) : (pResidual p D).map D.subtype ≤ centralizer (Q : Set G) := by
  have hqd : ⁅Q, D⁆ ≤ W := by rwa [commutator_comm]
  have hvalue (d : D) (q : Q) : ⁅(q : G), (d : G)⁆ ∈ W :=
    hqd (commutator_mem_commutator q.property d.property)
  let displacement : D →* (Q → W) := {
    toFun := fun d q => ⟨⁅(q : G), (d : G)⁆, hvalue d q⟩
    map_one' := by funext q; exact Subtype.ext (by simp)
    map_mul' := by
      intro d e
      funext q
      apply Subtype.ext
      change ⁅(q : G), (d : G) * (e : G)⁆ =
        ⁅(q : G), (d : G)⁆ * ⁅(q : G), (e : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hfix := mem_centralizer_iff.mp (hc d.property) _ (hvalue e q)
      calc
        _ = ⁅(q : G), (d : G)⁆ * ((d : G) * ⁅(q : G), (e : G)⁆) * (d : G)⁻¹ := by group
        _ = _ := by rw [← hfix]; group }
  have hfunctions : IsPGroup p (Q → W) := by
    obtain ⟨n, hn⟩ := hW.exists_card_dvd_pow
    intro f
    refine ⟨n, ?_⟩
    funext q
    exact orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard (f q)).trans hn)
  have hk : pResidual p D ≤ displacement.ker :=
    sInf_le ⟨inferInstance, (hfunctions.to_subgroup displacement.range).of_equiv
      (QuotientGroup.quotientKerEquivRange displacement).symm⟩
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_centralizer_iff]
  intro q hq
  have he := congrArg (fun f : Q → W => (f ⟨q, hq⟩ : G))
    (MonoidHom.mem_ker.mp (hk hd))
  exact commutatorElement_eq_one_iff_mul_comm.mp he

/-- A normal two-layer fixer lies in R when its residual centralizer does and G/R has trivial p-core. -/
public theorem two_layer_le_radical {p : ℕ} (Q W R : Subgroup G)
    [Q.Normal] [W.Normal] [R.Normal]
    (hW : IsPGroup p W) (hR : pCore p (G ⧸ R) = ⊥)
    (hc : pResidual p G ⊓ centralizer (Q : Set G) ≤ R) :
    centralizer (W : Set G) ⊓ commutatorPreimage ⊤ Q W ≤ R := by
  let H := centralizer (W : Set G) ⊓ commutatorPreimage ⊤ Q W
  have hn : (commutatorPreimage ⊤ Q W).Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp (commutatorPreimage_normalized ⊤ Q W ⊤
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal)
  let _ := hn
  have hcomm : ⁅H, Q⁆ ≤ W :=
    (commutator_mono inf_le_right le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ Q W le_normalizer_of_normal)
  have hres : (pResidual p H).map H.subtype ≤ R :=
    (le_inf (map_pResidual_le p H.subtype)
      (residual_centralizes_of_two_layer H Q W hW inf_le_left hcomm)).trans hc
  let π := QuotientGroup.mk' R
  have himage : IsPGroup p (H.map π) := by
    rintro ⟨x, hx⟩
    obtain ⟨h, hh, rfl⟩ := hx
    obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := H) p
      (QuotientGroup.mk' (pResidual p H) ⟨h, hh⟩)
    have hr : (⟨h, hh⟩ : H) ^ p ^ n ∈ pResidual p H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pResidual p H) ((⟨h, hh⟩ : H) ^ p ^ n) = 1
      rwa [map_pow]
    refine ⟨n, Subtype.ext ?_⟩
    change (π h) ^ p ^ n = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hres (mem_map_of_mem _ hr))
  have hle : H.map π ≤ pCore p (G ⧸ R) := le_sSup
    ⟨Normal.map inferInstance π (QuotientGroup.mk'_surjective R), himage⟩
  intro x hx
  have hb : π x ∈ (⊥ : Subgroup (G ⧸ R)) := hR ▸ hle (mem_map_of_mem π hx)
  exact (QuotientGroup.eq_one_iff x).mp hb

end Subgroup
