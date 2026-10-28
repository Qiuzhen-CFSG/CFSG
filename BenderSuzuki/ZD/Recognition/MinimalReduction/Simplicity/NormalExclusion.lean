module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Components
public import Theory.GroupTheory.ZStar.InvolutionSupplement

/-!
# Normal subgroups in the distinguished point stabilizer

Let N be normal in G and contained in M. A distinct commuting N-conjugate
of a distinguished involution would give an involutory product in N.
Product disconnection puts its centralizer in M; Sylow fusion control
then puts every transporter back into M. Normality of N would force G=M.

Thus every distinguished involution is isolated relative to N. The trivial
solvable radical makes the odd core of N trivial, so Z-star makes each such
involution centralize N. Since they generate G, N is abelian, hence trivial.
This direct argument needs no minimal-normal subgroup or component selection.

Source: GLS, Volume 4, Chapter 2, Lemma 4.9, the normal-subgroup exclusion
in its first paragraph; the transporter input is Lemma 4.2(c).
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem isolated_on_normal_subgroup
    (h : IsProductDisconnected Z M) (S : Sylow 2 G)
    (hSM : (S : Subgroup G) ≤ M) (hf : ControlsFusionIn M (S : Subgroup G))
    (N : Subgroup G) [N.Normal] (hNM : N ≤ M) {z : G} (hz : z ∈ Z)
    (a : N) (hc : Commute ((a : G) * z * (a : G)⁻¹) z) :
    (a : G) * z * (a : G)⁻¹ = z := by
  by_contra hne
  let v := (a : G) * z * (a : G)⁻¹
  have hvZ : v ∈ Z := h.invariant a z hz
  have hi := h.involutions z hz
  have hv := h.involutions v hvZ
  have hpN : z * v ∈ N := by
    have he : z * v = (z * (a : G) * z⁻¹) * (a : G)⁻¹ := by
      rw [hi.inv_eq_self]
      dsimp [v]
      group
    rw [he]
    exact N.mul_mem ((inferInstance : N.Normal).conj_mem a a.property z)
      (N.inv_mem a.property)
  have hprod : PFAppendixIII.IsInvolution (z * v) := by
    refine ⟨?_, ?_⟩
    · intro he
      have hvz : v = z⁻¹ := eq_inv_of_mul_eq_one_right he
      exact hne (hvz.trans hi.inv_eq_self)
    · rw [hc.symm.mul_pow, hi.sq_eq_one, hv.sq_eq_one, one_mul]
  apply h.proper
  apply top_unique
  intro g _
  exact involution_transporter_mem S hSM hf hprod (hNM hpN)
    (h.product_centralizer z hz v hvZ hprod (hNM hpN))
    (hNM ((inferInstance : N.Normal).conj_mem (z * v) hpN g))

/-- The normal-subgroup exclusion in GLS Lemma 4.9. The conclusion holds
without the additional two-centrality and single-class hypotheses available
to the source consumer. -/
public theorem normal_eq_bot_of_productDisconnected_fusion
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hf : ControlsFusionIn M (S : Subgroup G))
    (hrad : solvableRadical G = ⊥)
    (N : Subgroup G) [N.Normal] (hNM : N ≤ M) : N = ⊥ := by
  have hGcore := oddCore_eq_bot_of_radicalFree hrad
  have hmap : (pPrimeCore 2 N).map N.subtype = ⊥ := by
    apply bot_unique
    rw [← hGcore]
    exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N
  have hNcore : pPrimeCore 2 N = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := pPrimeCore 2 N)
      (f := N.subtype) N.subtype_injective).mp hmap
  have hZ : Z ⊆ Subgroup.centralizer (N : Set G) := by
    intro z hz
    exact Glauberman.ZStar.centralizes_normal_of_isolated_in_sup_zpowers N
      (h.involutions z hz) hNcore (isolated_on_normal_subgroup h S hSM hf N hNM hz)
  have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hZ
  have hsolv : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => Subtype.ext
    ((Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_top (a : G)))
      (b : G) b.property).symm)
  apply bot_unique
  rw [← hrad]
  exact le_solvableRadical N inferInstance hsolv

end BenderSuzuki.ZD
