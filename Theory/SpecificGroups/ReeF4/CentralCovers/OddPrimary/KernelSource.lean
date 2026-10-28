module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Source
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.GroupTheory.Covering

/-!
# The Ree odd-center bound from the remaining unitary tori

All good-prime indices and the full three-primary configuration are proved.
The two literal unitary torus embeddings therefore suffice to exclude every
odd prime from a perfect central kernel. Composing the original center map
with the specified model equivalence gives the quasisimple source statement.
The unitary subsystem owner constructs these two torus witnesses separately.

Source: Aschbacher–Smith I.1.1–4 and A.3.6; GLS3 §6.1 and §4.10.
-/

public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary
open PerfectCentralCovering Subgroup Theory.GroupTheory

variable (m : ℕ) (hm : 1 ≤ m)
    (hnorm : Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)))
    (hsinger : Nonempty (CyclicTorusEmbedding m
      ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)))

include hm hnorm hsinger

theorem not_dvd_kernel_of_unitary_tori {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  apply not_dvd_kernel_of_geometry m _ (Three.Descent.nonempty_threeSylowData m hm) hp c
  intro q hq hlarge hd
  let : Fact q.Prime := ⟨hq⟩
  exact goodPrimeGeometry_of_unitary_tori m hm hnorm hsinger hlarge hd

theorem kernel_isPGroup_of_unitary_tori
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    IsPGroup 2 c.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have he : p = 2 := by
    by_contra h2
    let : Fact p.Prime := ⟨hprime⟩
    exact not_dvd_kernel_of_unitary_tori m hm hnorm hsinger h2 c hdiv
  norm_num [he]

theorem center_isPGroup_of_unitary_tori
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Model m) : IsPGroup 2 (center L) := by
  let f : L →* Model m := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let c : Cover L (Model m) := ⟨f, hf, inferInstance, le_of_eq hk⟩
  exact (kernel_isPGroup_of_unitary_tori m hm hnorm hsinger c).of_equiv
    (MulEquiv.subgroupCongr hk)

/-- The literal local-block marking used by the classification consumers. -/
theorem localBlock_center_isPGroup_of_unitary_tori
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (d : LocalBlockInput m) (e : L ⧸ center L ≃* d.fixedGroup) :
    IsPGroup 2 (center L) :=
  center_isPGroup_of_unitary_tori m hm hnorm hsinger (e.trans d.modelEquiv)

end ReeF4.CentralCovers.OddPrimary
