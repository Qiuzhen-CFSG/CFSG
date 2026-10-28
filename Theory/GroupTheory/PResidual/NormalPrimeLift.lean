module
public import Theory.GroupTheory.PResidual.NormalizedImageLift
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Normal odd-prime lifts through a two-kernel

For a surjection with two-group kernel, take the two-residual of the full
preimage of a normal odd-prime group. Surjections preserve residuals, so
this normal, two-perfect subgroup has the prescribed image. Its restricted
map has exactly its intrinsic two-core as kernel, giving an isomorphism
of the actual quotient with that image.

Source application: Aschbacher–Smith 14.7.6 and 14.7.27, printed
pp.1044–1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Subgroup
/-- Lift a normal odd-prime subgroup through a two-kernel, retaining its
exact image and intrinsic two-core quotient. -/
theorem exists_normal_prime_residual_lift {D E : Type*} [Group D] [Finite D]
    [Group E] [Finite E] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (q : D →* E) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (X : Subgroup E) [X.Normal] (hX : IsPGroup p X) :
    ∃ Y : Subgroup D, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 D ∧
      Y.map q = X ∧ (q.comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr (Ne.symm hp)
  let I := X.comap q
  let Y := (pResidual 2 I).map I.subtype
  have hpX : IsPPerfect 2 X := by
    apply (pResidual_eq_top_iff 2 X).mp
    apply top_unique
    intro x _
    obtain ⟨n,hn⟩ := hX.exists_card_eq
    exact mem_pResidual_of_orderOf_coprime
      ((hcop.pow_right n).of_dvd_right (hn ▸ _root_.orderOf_dvd_natCard x))
  have him : Y.map q = X := by
    rw [map_embedded_pResidual,show I.map q = X from map_comap_eq_self_of_surjective hq X,
      (pResidual_eq_top_iff 2 X).mpr hpX,←MonoidHom.range_eq_map,range_subtype]
  let f := q.comp Y.subtype
  have hf : IsPGroup 2 f.ker := hk.comap_of_injective _ Y.subtype_injective
  have hr : f.range = X := by rw [MonoidHom.range_comp,range_subtype,him]
  have hpr : IsPGroup p f.range := hr.symm ▸ hX
  have hcore : pCore 2 f.range = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hpr.to_subgroup ⊤) hcop).le_bot)
  have he := f.ker_eq_pCore_of_range_core_eq_bot 2 hf hcore
  refine ⟨Y,inferInstance,isPPerfect_embedded_pResidual 2 I,
    map_pResidual_le 2 I.subtype,him,he,?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq he.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))⟩
end Subgroup
