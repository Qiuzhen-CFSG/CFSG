module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Products
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension

/-!
# Local closures across a component orbit

Let K lie in a centerless component L of a finite group, and let a two-group
A act by conjugation. Assume only that A ∩ N(L) normalizes K. If K has a
nontrivial self-centralizing two-core and maps onto A₇ with two-group kernel,
then the full generated subgroup X = K ⊔ A has the same core properties and
is a two-group extension of a group mapping onto a direct power of A₇ with
two-group kernel.

The normal subgroup N is the join of all A-conjugates of K, restricted to X.
Stabilizer invariance and independence of distinct centerless components
identify N with a finite direct power of K. The factor maps produce the
actual alternating-power quotient. The quotient X/N is an image of A;
characteristic two passes from the direct product N to this extension.

This conditional construction supplies the component-orbit local overgroup
used in Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526. The model-specific
factor and invariance hypotheses are inputs to this general theorem.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The full two-subgroup closure of a stabilizer-invariant local factor in a
centerless component has characteristic two and an actual alternating-power
quotient, with two-groups above and below that quotient. -/
theorem component_local_closure
    {L A K : Subgroup G} (hL : IsComponent G L) (hZ : center L = ⊥)
    (hA : IsPGroup 2 A) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hne : pCore 2 K ≠ ⊥)
    (hchar : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (f : K →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    pCore 2 (K ⊔ A : Subgroup G) ≠ ⊥ ∧
      centralizer (pCore 2 (K ⊔ A : Subgroup G) : Set (K ⊔ A : Subgroup G)) ≤
        pCore 2 (K ⊔ A : Subgroup G) ∧
      AlternatingPowerTwoExtension (K ⊔ A : Subgroup G) 7 := by
  obtain ⟨n, _, ⟨e⟩⟩ := componentOrbit_localFactor_equiv_power hL hZ hKL hinv
  let X := K ⊔ A
  let N := (componentOrbit K A).subgroupOf X
  let : N.Normal := componentOrbit_normal_subgroupOf_sup K A
  let eN : N ≃* (Fin n → K) :=
    (subgroupOfEquivOfLe (componentOrbit_le_sup K A)).trans e.symm
  have hN : centralizer (pCore 2 N : Set N) ≤ pCore 2 N :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 eN).mpr
      (centralizer_pCore_power_le hchar)
  have hq : IsPGroup 2 (X ⧸ N) := componentOrbit_quotient_isPGroup K A hA
  have hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    centralizer_pCore_le_of_normal_pGroup_quotient N hN hq
  have hXne : pCore 2 X ≠ ⊥ := by
    intro hb
    apply hne
    apply bot_unique
    intro k _
    rw [hb] at hX
    have hc : inclusion (show K ≤ X from le_sup_left) k ∈
        centralizer ((⊥ : Subgroup X) : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [mem_bot.mp hy]
      simp
    have he := mem_bot.mp (hX hc)
    exact mem_bot.mpr ((inclusion_injective (show K ≤ X from le_sup_left))
      (he.trans (map_one (inclusion (show K ≤ X from le_sup_left))).symm))
  obtain ⟨F, hF, hFk⟩ := power_surjection_kernel_isPGroup (I := Fin n) f hf hk
  let g : N →* (Fin n → alternatingGroup (Fin 7)) := F.comp eN.toMonoidHom
  have hgk : IsPGroup 2 g.ker := by
    change IsPGroup 2 (F.comp eN.toMonoidHom).ker
    rw [← MonoidHom.comap_ker]
    exact hFk.comap_of_injective eN.toMonoidHom eN.injective
  exact ⟨hXne, hX, N, inferInstance, hq, n, g, hF.comp eN.surjective, hgk⟩

end Theory.GroupTheory

end
