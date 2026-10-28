module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Products
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension

/-!
# Alternating sections of local component closures

The orbit of a stabilizer-invariant local subgroup in a centerless component
is a finite direct power of that subgroup. A supplied alternating quotient
therefore gives a quotient of the orbit onto the corresponding alternating
power. The orbit is normal in its join with the actor, with two-group upper
quotient when the actor is a two-group. Characteristic two passes first to
the direct power and then to this extension.

This extends the degree-seven construction to arbitrary alternating degree,
for the degree-six hexad application in Aschbacher–Smith 2.3.9(7)(f),
printed pp.525–526. Only the stabilizer of the component must fix the local
factor; the actor may permute distinct components.
-/

public section

open Subgroup
namespace Theory.GroupTheory

/-- Transport the normal layer, upper quotient and alternating-power map
along a genuine group isomorphism. -/
theorem AlternatingPowerTwoExtension.of_equiv
    {K P : Type*} [Group K] [Group P] {d : ℕ}
    (h : AlternatingPowerTwoExtension K d) (e : K ≃* P) :
    AlternatingPowerTwoExtension P d := by
  obtain ⟨N, hn, hq, n, f, hf, hk⟩ := h
  let := hn
  let V := N.map e.toMonoidHom
  let : V.Normal := Subgroup.Normal.map hn e.toMonoidHom e.surjective
  let eN : N ≃* V := e.subgroupMap N
  let g := f.comp eN.symm.toMonoidHom
  refine ⟨V, inferInstance, ?_, n, g, hf.comp eN.symm.surjective, ?_⟩
  · exact hq.of_equiv (QuotientGroup.congr N V e rfl)
  · change IsPGroup 2 (f.comp eN.symm.toMonoidHom).ker
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective eN.symm.toMonoidHom eN.symm.injective

/-- The full actor closure has characteristic two and an actual normal
alternating-power section with two-groups both above and below it. -/
theorem component_local_closure_alternatingPower
    {G : Type*} [Group G] [Finite G] {d : ℕ} {L A K : Subgroup G}
    (hL : IsComponent G L) (hZ : center L = ⊥)
    (hA : IsPGroup 2 A) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hchar : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (f : K →* alternatingGroup (Fin d)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    centralizer (pCore 2 (K ⊔ A : Subgroup G) : Set (K ⊔ A : Subgroup G)) ≤
        pCore 2 (K ⊔ A : Subgroup G) ∧
      AlternatingPowerTwoExtension (K ⊔ A : Subgroup G) d := by
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
  obtain ⟨F, hF, hFk⟩ := power_surjection_kernel_isPGroup (I := Fin n) f hf hk
  let g : N →* (Fin n → alternatingGroup (Fin d)) := F.comp eN.toMonoidHom
  have hgk : IsPGroup 2 g.ker := by
    change IsPGroup 2 (F.comp eN.toMonoidHom).ker
    rw [← MonoidHom.comap_ker]
    exact hFk.comap_of_injective eN.toMonoidHom eN.injective
  exact ⟨hX, N, inferInstance, hq, n, g, hF.comp eN.surjective, hgk⟩

end Theory.GroupTheory

end
