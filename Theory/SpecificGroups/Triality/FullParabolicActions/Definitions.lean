module

public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# The genuine full Levi complement and its radical action

The full Levi is the descent of the split subsystem together with the
original torus. In characteristic two it is disjoint from the root radical
and supplements it in the full parabolic. The canonical projection has
kernel the relative radical, already identified with the parabolic's
two-core. Consequently the full Levi has trivial two-core.

Conjugation defines its actual action on the root radical. The pointwise
formula and kernel are supplied here; faithfulness is a separate root
calculation. No normality in the ambient triality group is asserted.
Elementary fixed points and their own central quotient are retained, and
all the structural results include q = 2.

Source: GLS3 Theorem 2.6.5(e–g) (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.12(I)(4), pp.263–264 (`refs/quasithin.pdf`).
-/

public section
noncomputable section

private theorem core_eq_bot_of_surjective
    {G K : Type*} [Group G] [Group K] (p : ℕ) (f : G →* K)
    (hf : Function.Surjective f) (hk : f.ker = pCore p G) : pCore p K = ⊥ := by
  have hkerP : IsPGroup p f.ker := by rw [hk]; exact pCore_isPGroup
  have hpreP : IsPGroup p ((pCore p K).comap f) :=
    pCore_isPGroup.comap_of_ker_isPGroup f hkerP
  have hle : (pCore p K).comap f ≤ f.ker := by
    rw [hk]
    exact le_sSup ⟨inferInstance, hpreP⟩
  apply bot_unique
  intro k hk'
  obtain ⟨g, rfl⟩ := hf k
  exact MonoidHom.mem_ker.mp (hle hk')

namespace Triality.Standard.Parabolics
open RadicalCoordinates ConcreteBruhat

@[expose] def fullLevi (P : Parameters) (a : Node) : Subgroup (Carrier P) :=
  descendSubgroup P (splitFullLevi P a)

theorem fullLevi_eq (P : Parameters) (hp : P.prime = 2) (a : Node) :
    fullLevi P a = levi P a ⊔ torus P :=
  descendSubgroup_splitFullLevi P hp a

theorem fullLevi_le_parabolic (P : Parameters) (a : Node) :
    fullLevi P a ≤ parabolic P a :=
  descendSubgroup_mono P (splitFullLevi_le_splitParabolic P a)

theorem parabolic_eq_radical_sup_fullLevi (P : Parameters) (hp : P.prime = 2) (a : Node) :
    parabolic P a = radical P a ⊔ fullLevi P a := by
  rw [fullLevi_eq P hp a, radical_eq_descendedRootSubgroup P hp a]
  exact parabolic_eq_root_sup_levi_sup_torus P hp a

theorem disjoint_radical_fullLevi (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Disjoint (radical P a) (fullLevi P a) := by
  rw [radical_eq_descendedRootSubgroup P hp a]
  apply Subgroup.disjoint_def.mpr
  rintro g ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have hyx : y = x := ElementaryCentralKernel.toCarrier_injective P hp he
  subst y
  have hx1 : elementaryInclusion P x = 1 :=
    Subgroup.disjoint_def.mp (disjoint_rootSubgroup_splitFullLevi P hp a) hx hy
  have hx' : x = 1 := LeviCommutators.elementaryInclusion_injective P
    (hx1.trans (map_one (elementaryInclusion P)).symm)
  exact (congrArg (toCarrier P) hx').trans (map_one _)

@[expose] def fullLeviProjection (P : Parameters) (hp : P.prime = 2) (a : Node) :
    parabolic P a →* fullLevi P a :=
  Subgroup.relativeComplementProjection (radical_le_parabolic P a)
    (fullLevi_le_parabolic P a) (parabolic_eq_radical_sup_fullLevi P hp a).symm
    (disjoint_radical_fullLevi P hp a)

theorem fullLeviProjection_surjective (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Function.Surjective (fullLeviProjection P hp a) :=
  Subgroup.relativeComplementProjection_surjective _ _ _ _

theorem fullLeviProjection_ker (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (fullLeviProjection P hp a).ker = (radical P a).subgroupOf (parabolic P a) :=
  Subgroup.relativeComplementProjection_ker _ _ _ _

theorem parabolic_twoCore_eq (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (parabolic P a) = (radical P a).subgroupOf (parabolic P a) := by
  apply Subgroup.map_injective (parabolic P a).subtype_injective
  rw [parabolic_twoCore_map P hp a,
    Subgroup.map_subgroupOf_eq_of_le (radical_le_parabolic P a)]

theorem fullLevi_twoCore_eq_bot (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (fullLevi P a) = ⊥ :=
  core_eq_bot_of_surjective 2 (fullLeviProjection P hp a)
    (fullLeviProjection_surjective P hp a)
    ((fullLeviProjection_ker P hp a).trans (parabolic_twoCore_eq P hp a).symm)

theorem fullLevi_le_normalizer_radical (P : Parameters) (a : Node) :
    fullLevi P a ≤ Subgroup.normalizer (radical P a : Set (Carrier P)) :=
  (fullLevi_le_parabolic P a).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P a)).mp
      (radical_normal P a))

@[expose] def fullLeviRadicalAction (P : Parameters) (a : Node) :
    fullLevi P a →* MulAut (radical P a) :=
  (radical P a).normalizerMonoidHom.comp
    (Subgroup.inclusion (fullLevi_le_normalizer_radical P a))

theorem fullLeviRadicalAction_apply (P : Parameters) (a : Node)
    (c : fullLevi P a) (r : radical P a) :
    (fullLeviRadicalAction P a c r).val = c.val * r.val * c.val⁻¹ := rfl

theorem fullLeviRadicalAction_ker (P : Parameters) (a : Node) :
    (fullLeviRadicalAction P a).ker =
      (Subgroup.centralizer (radical P a : Set (Carrier P))).subgroupOf (fullLevi P a) := by
  change ((radical P a).normalizerMonoidHom.ker).comap
    (Subgroup.inclusion (fullLevi_le_normalizer_radical P a)) = _
  rw [Subgroup.normalizerMonoidHom_ker]
  rfl

end Triality.Standard.Parabolics
