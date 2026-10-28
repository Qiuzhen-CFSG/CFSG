module
public import Stellmacher.SectionTwo.LemmaTwoFour
public import Stellmacher.SectionTwo.LemmaTwoFiveDefs
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian
public import Stellmacher.TwoResidualSylowSupplement

/-!
# Contained automorphism orbits in the pushing-up two-core

Under the exact hypotheses of Stellmacher (2.5), the subgroup `V` in the
chosen Sylow two-subgroup lies in `pushingUpQ S`, the copy of `O₂(G)`.
If every translate of `V` by an odd-order automorphism subgroup lies in
that two-core, their ambient join is normal in `G`.

The standing characteristic-two hypothesis puts `V` in `O₂(G)`. Each
translate is normal inside the Sylow subgroup, so their join `K` is
normalized by the Sylow subgroup. The identity translate gives `V ≤ K`,
and Stellmacher (2.4) gives
`[K,O²(G)] ≤ [O₂(G),O²(G)] ≤ V ≤ K`. Thus the two-residual also normalizes
`K`; since it and the Sylow subgroup generate `G`, the join is normal.

This packages the contained-orbit consequence of Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), (3.2), p.14, needed by (3.5) and cited in (2.5) of
`refs/latex/stellmacher-n-group.tex`. The required commutator input comes
from the proved (2.4), so the graph structure theorem need not be rebuilt
here. The public statement retains all (2.5) quotient and oddness hypotheses.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionTwo

universe u

private theorem containedOrbitNormal_of_commutator_le
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcomm :
      ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ vSubgroup S) :
    ∀ U : Subgroup (MulAut S),
      (∀ τ : U, (τ : MulAut S) • vSubgroupInSylow S ≤ pushingUpQ S) →
      (⨆ τ : U, automorphismTranslateV S (τ : MulAut S)).Normal := by
  intro U hcontained
  let VS : Subgroup S := vSubgroupInSylow S
  let KS : Subgroup S := ⨆ τ : U, (τ : MulAut S) • VS
  let K : Subgroup G :=
    ⨆ τ : U, automorphismTranslateV S (τ : MulAut S)
  have hV_le_Q : vSubgroup S ≤ pCore 2 G := (vSubgroup_le_twoCore_and_elementaryAbelian h S).1
  have hQ_le_S : pCore 2 G ≤ (S : Subgroup G) :=
    fitting_pCore_le_sylow S
  have hV_le_S : vSubgroup S ≤ (S : Subgroup G) := hV_le_Q.trans hQ_le_S
  have hmapVS : VS.map (S : Subgroup G).subtype = vSubgroup S := by
    apply Subgroup.map_comap_eq_self
    simpa using hV_le_S
  have hKS_normal : KS.Normal := by
    have hVS_normal : VS.Normal :=
      Subgroup.normalClosure_normal.comap (S : Subgroup G).subtype
    let _ (τ : U) : ((τ : MulAut S) • VS).Normal := by
      change (VS.map ((τ : MulAut S) : S →* S)).Normal
      exact hVS_normal.map _ (τ : MulAut S).surjective
    exact Subgroup.iSup_normal _
  have hK_eq : K = KS.map (S : Subgroup G).subtype := by
    rw [Subgroup.map_iSup]
    rfl
  have hK_le_Q : K ≤ pCore 2 G := by
    rw [iSup_le_iff]
    intro τ
    exact (Subgroup.map_mono (hcontained τ)).trans
      (Subgroup.map_comap_le (S : Subgroup G).subtype (pCore 2 G))
  have hV_le_K : vSubgroup S ≤ K := by
    let oneU : U := ⟨1, U.one_mem⟩
    calc
      vSubgroup S = automorphismTranslateV S (oneU : MulAut S) := by
        unfold automorphismTranslateV
        change vSubgroup S =
          (VS.map ((oneU : MulAut S) : S →* S)).map
            (S : Subgroup G).subtype
        have hone : ((oneU : MulAut S) : S →* S) = MonoidHom.id S := by
          ext x
          rfl
        rw [hone, Subgroup.map_id]
        exact hmapVS.symm
      _ ≤ K := le_iSup (fun τ : U ↦
        automorphismTranslateV S (τ : MulAut S)) oneU
  have hS_normalizes :
      (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, hK_eq]
    have hmapped := Subgroup.map_mono
      (f := (S : Subgroup G).subtype)
      (Subgroup.commutator_le_left KS (⊤ : Subgroup S))
    rw [Subgroup.map_commutator] at hmapped
    have hmaptop :
        (⊤ : Subgroup S).map (S : Subgroup G).subtype =
          (S : Subgroup G) := by
      ext x
      simp
    rw [hmaptop] at hmapped
    exact hmapped
  have hres_normalizes :
      twoResidualAmbient (⊤ : Subgroup G) ≤
        Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono hK_le_Q le_rfl).trans
      (hcomm.trans hV_le_K)
  have hnormalizer_top : Subgroup.normalizer (K : Set G) = ⊤ := by
    apply top_unique
    rw [← twoResidualAmbient_top_sup_sylow S]
    exact sup_le hres_normalizes hS_normalizes
  change K.Normal
  exact Subgroup.normalizer_eq_top_iff.mp hnormalizer_top

/-- The formal `V` lies in the two-core, and an odd automorphism orbit of `V`
which stays in that two-core generates an ambient-normal subgroup. -/
public theorem pushing_up_three_two_contained_orbit_normal
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (_hq : Function.Surjective q)
    (_hker : q.ker = cSubgroup S)
    (_hbar : Nonempty
      (barG ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) :
    vSubgroupInSylow S ≤ pushingUpQ S ∧
      ∀ U : Subgroup (MulAut S),
        Odd (Nat.card U) →
        (∀ τ : U, (τ : MulAut S) • vSubgroupInSylow S ≤ pushingUpQ S) →
        (⨆ τ : U, automorphismTranslateV S (τ : MulAut S)).Normal := by
  refine ⟨?_, fun U _hU hcontained ↦ ?_⟩
  · exact fun _ hx ↦ (vSubgroup_le_twoCore_and_elementaryAbelian h S).1 hx
  · exact containedOrbitNormal_of_commutator_le h S
      (lemma_two_four h S hcharacteristic hunique) U hcontained

end Stellmacher.SectionTwo
