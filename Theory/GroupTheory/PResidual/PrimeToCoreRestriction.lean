module

public import Theory.GroupTheory.PResidual.PrimeToCoreMap

/-!
# P-cores of overgroups of the prime-to-p residual

An intermediate subgroup containing `O^{p′}(G)` has the same embedded p-core
as `G`; normality of the intermediate subgroup is not required. Its core is
a p-subgroup, so belongs to the residual and is normal there. The residual's
characteristic core is normal in `G`, giving one containment; restriction of
`O_p(G)` gives the other.

For the finite reductive application, a positive Sylow in the residual and
an opposition element with disjoint unipotent factors kill the full p-core.
This uses no simplicity assumption and does not omit solvable small groups.
The Sylow and opposition geometry are separate source inputs. Conjugation
here is `n * x * n⁻¹`; for the source right-conjugation convention use the
inverse representative.

Source: GLS3, §§2.2, 2.3 and the p-reduced Levi step of 2.6.5(e,f).
-/

public section

namespace Subgroup

variable {G A : Type*} [Group G] [Group A]

/-- Every overgroup of the prime-to-p residual has the same embedded p-core. -/
theorem map_pCore_eq_of_primeToResidual_le (p : ℕ) (H : Subgroup G)
    (hH : primeToResidual p G ≤ H) :
    (pCore p H).map H.subtype = pCore p G := by
  let R := primeToResidual p G
  let Q := (pCore p H).map H.subtype
  have hQR : Q ≤ R := le_primeToResidual_of_isPGroup (pCore_isPGroup.map _)
  apply le_antisymm
  · have hN : (Q.subgroupOf R).Normal := by
      constructor
      intro x hx g
      obtain ⟨y, hy, hyx⟩ := hx
      let gH : H := ⟨g, hH g.property⟩
      refine ⟨gH * y * gH⁻¹, (inferInstance : (pCore p H).Normal).conj_mem y hy gH, ?_⟩
      change (g : G) * (y : G) * (g : G)⁻¹ = (g : G) * (x : G) * (g : G)⁻¹
      change (y : G) = (x : G) at hyx
      rw [hyx]
    have hle : Q.subgroupOf R ≤ pCore p R :=
      le_sSup ⟨hN, (pCore_isPGroup.map H.subtype).comap_subtype⟩
    have hm := map_mono (f := R.subtype) hle
    rw [map_subgroupOf_eq_of_le hQR, map_pCore_primeToResidual] at hm
    exact hm
  · have hcoreH : pCore p G ≤ H :=
      (le_primeToResidual_of_isPGroup pCore_isPGroup).trans hH
    have hle : (pCore p G).subgroupOf H ≤ pCore p H :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    simpa only [map_subgroupOf_eq_of_le hcoreH] using map_mono (f := H.subtype) hle

/-- An opposition witness kills the full core, even if the Sylow was supplied
only in the prime-to-p residual. -/
theorem pCore_eq_bot_of_residualSylow_opposition (p : ℕ)
    (f : G →* A) (hf : Function.Injective f) (U : Subgroup A)
    (S : Sylow p (primeToResidual p G))
    (hS : (S : Subgroup (primeToResidual p G)).map
      (f.comp (primeToResidual p G).subtype) ≤ U)
    (n : G) (hdis : Disjoint U (U.map (MulAut.conj (f n)).toMonoidHom)) :
    pCore p G = ⊥ := by
  have hcoreU : (pCore p G).map f ≤ U := by
    rw [← map_pCore_primeToResidual p, map_map]
    exact (map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans hS
  apply le_bot_iff.mp
  intro x hx
  have hxU : f x ∈ U := hcoreU (mem_map_of_mem f hx)
  have hy : n⁻¹ * x * n ∈ pCore p G := by
    simpa only [inv_inv] using (inferInstance : (pCore p G).Normal).conj_mem x hx n⁻¹
  have hyU : f (n⁻¹ * x * n) ∈ U := hcoreU (mem_map_of_mem f hy)
  have hxOpp : f x ∈ U.map (MulAut.conj (f n)).toMonoidHom := by
    refine ⟨f (n⁻¹ * x * n), hyU, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have hxone : f x = 1 := disjoint_iff_inf_le.mp hdis ⟨hxU, hxOpp⟩
  exact hf (hxone.trans (map_one f).symm)

end Subgroup
