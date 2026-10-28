module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction
public import Theory.AlgebraicGroup.RootSystems.Weyl
/-!
# F4 root automorphisms and the full weight lattice

Weyl transitivity on bases reduces a root automorphism to the numbered
Cartan-matrix stabilizer. The unique double edge fixes the middle two nodes,
then the outer nodes, so this stabilizer is trivial. Consequently every actual
F4 root automorphism is Weyl. The final extensionality theorem records that
roots span all integral weights, using the determinant-one coordinate map.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §3; GLS3 §1.8.
The consumer is the actual F4 torus-normalizer action.
-/

open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
public noncomputable section

private theorem cartan_minus_two (i j : Fin 4)
    (h : typeF4CartanMatrix i j = -2) : i = 1 ∧ j = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [typeF4CartanMatrix, Fin.ext_iff]

private theorem cartan_first (i : Fin 4)
    (h1 : typeF4CartanMatrix i 1 = -1) (h2 : typeF4CartanMatrix i 2 = 0) : i = 0 := by
  fin_cases i <;> simp_all [typeF4CartanMatrix, Fin.ext_iff]

private theorem cartan_last (i : Fin 4)
    (h1 : typeF4CartanMatrix 1 i = 0) (h2 : typeF4CartanMatrix 2 i = -1) : i = 3 := by
  fin_cases i <;> simp_all [typeF4CartanMatrix, Fin.ext_iff]

private theorem cartan_stabilizer (e : Fin 4 → Fin 4)
    (he : ∀ i j, typeF4CartanMatrix (e i) (e j) = typeF4CartanMatrix i j) : e = id := by
  have h12 := cartan_minus_two (e 1) (e 2) (he 1 2)
  have h0 : e 0 = 0 := cartan_first (e 0)
    (by simpa only [h12.1] using (he 0 1).trans (show typeF4CartanMatrix 0 1 = -1 by decide +kernel)) (by simpa only [h12.2] using (he 0 2).trans (show typeF4CartanMatrix 0 2 = 0 by decide +kernel))
  have h3 : e 3 = 3 := cartan_last (e 3)
    (by simpa only [h12.1] using (he 1 3).trans (show typeF4CartanMatrix 1 3 = 0 by decide +kernel)) (by simpa only [h12.2] using (he 2 3).trans (show typeF4CartanMatrix 2 3 = -1 by decide +kernel))
  funext i
  fin_cases i <;> simp [h0, h3, h12.1, h12.2]

private theorem base_stabilizer (f : RootPairing.Aut typeF4RootPairing) (hf : f • typeF4RootPairing_base = typeF4RootPairing_base) : f = 1 := by
  have hm (r : typeF4Roots) : f.indexEquiv r ∈ typeF4RootPairing_base.support ↔ r ∈ typeF4RootPairing_base.support := by
    conv_lhs => rw [← hf]
    change f.indexEquiv r ∈ (RootPairing.Base.mapAut f typeF4RootPairing_base).support ↔ _
    rw [RootPairing.Base.mem_mapAut_support, Equiv.symm_apply_apply]
  let e : typeF4RootPairing_base.support ≃ typeF4RootPairing_base.support := Equiv.subtypeEquiv f.indexEquiv (fun r => (hm r).symm)
  let p : Equiv.Perm (Fin 4) := typeF4RootPairing_baseEquiv.trans
    (e.trans typeF4RootPairing_baseEquiv.symm)
  have hp (i : Fin 4) : (typeF4RootPairing_baseEquiv (p i)).val =
      f.indexEquiv (typeF4RootPairing_baseEquiv i) := by
    simp [p, e]
  have hpc : ∀ i j, typeF4CartanMatrix (p i) (p j) = typeF4CartanMatrix i j := by
    intro i j
    rw [← typeF4RootPairing_base_cartan_apply (p i) (p j),
      ← typeF4RootPairing_base_cartan_apply i j]
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    change algebraMap ℤ ℝ (typeF4RootPairing.pairingIn ℤ _ _) = algebraMap ℤ ℝ (typeF4RootPairing.pairingIn ℤ _ _)
    rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing.algebraMap_pairingIn]
    rw [hp, hp]
    exact RootPairing.Equiv.pairing_eq f _ _
  have hid : p = 1 := Equiv.ext (congrFun (cartan_stabilizer p hpc))
  have hfix (i : typeF4RootPairing_base.support) : f.indexEquiv i = i := by
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    simpa only [hid, Equiv.Perm.one_apply] using (hp j).symm
  apply RootPairing.Equiv.weightHom_injective typeF4RootPairing
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro i
  simp only [RootPairing.Base.toWeightBasis_apply]
  change f.weightMap (typeF4RootPairing.root i) = typeF4RootPairing.root i
  rw [RootPairing.Hom.root_weightMap_apply, hfix]

theorem aut_mem_weylGroup (f : RootPairing.Aut typeF4RootPairing) :
    f ∈ typeF4RootPairing.weylGroup := by
  let : MulAction.IsPretransitive typeF4RootPairing.weylGroup typeF4RootPairing.Base := Theory.AlgebraicGroup.weylGroup_action_on_bases_transitive typeF4RootPairing
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq typeF4RootPairing.weylGroup typeF4RootPairing_base (f • typeF4RootPairing_base)
  have he : w.val⁻¹ * f = 1 := by
    apply base_stabilizer
    rw [mul_smul, ← hw]
    change w.val⁻¹ • (w.val • typeF4RootPairing_base) = typeF4RootPairing_base
    exact inv_smul_smul w.val typeF4RootPairing_base
  have hf : f = w.val := (inv_mul_eq_one.mp he).symm
  rw [hf]
  exact w.property

/-- Root characters span the full integral weight lattice. -/
theorem addHom_ext_roots {M : Type*} [AddCommGroup M]
    (f g : Weight →+ M) (h : ∀ r, f (rootWeight r) = g (rootWeight r)) : f = g := by
  have he : f.toIntLinearMap.comp coordinateEquiv.toLinearMap =
      g.toIntLinearMap.comp coordinateEquiv.toLinearMap := by
    apply typeF4RootPairing_base.toWeightBasisInt.ext
    intro r
    have hr : typeF4RootPairing_base.toWeightBasisInt r = typeF4RootPairing.rootSpanMem ℤ r := by
      apply Subtype.ext
      simp
    rw [hr]
    have hc : coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r) = rootWeight r := by
      ext i
      simp [rootWeight]
    change f (coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r)) = g (coordinateEquiv (typeF4RootPairing.rootSpanMem ℤ r))
    rw [hc]
    exact h r
  apply AddMonoidHom.ext
  intro a
  obtain ⟨x, rfl⟩ := coordinateEquiv.surjective a
  exact LinearMap.congr_fun he x

end
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
