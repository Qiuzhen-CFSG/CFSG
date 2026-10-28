module

public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Radical quotients of two-extensions

Let N be normal in a finite group G, with G/N a two-group. If N modulo
its solvable radical is nonabelian simple, its image in G modulo the
solvable radical is exactly the generalized Fitting subgroup there.

The radical of N is N intersected with the ambient radical. The first
isomorphism theorem therefore identifies the image with N/R(N). Its
quotient is still a two-group, while the ambient radical quotient has
trivial two-core. The simple-normal two-quotient theorem applies, and
Sylow surjectivity gives supplementation by every Sylow two-subgroup.
No splitting or specified outer action is required.

Source: standard solvable-radical and generalized-Fitting theory; the
parabolic reduction in Aschbacher--Smith, E.1.14(1), printed p.214.
-/

@[expose] public section
open Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The radical of a normal subgroup is its intersection with the ambient radical. -/
theorem radical_subgroupOf_normal (N : Subgroup G) [N.Normal] :
    (solvableRadical G).subgroupOf N = solvableRadical N := by
  apply le_antisymm
  · let f := N.subtype.subgroupComap (solvableRadical G)
    let : Group.IsSolvable ((solvableRadical G).subgroupOf N) :=
      Group.isSolvable_of_isSolvable_injective (f := f)
        (fun a b h => Subtype.ext (Subtype.ext
          (congrArg (fun r : solvableRadical G => (r : G)) h)))
    exact le_solvableRadical _ inferInstance inferInstance
  · exact map_le_iff_le_comap.mp (map_solvableRadical_subtype_le_of_normal N)

/-- The radical quotient of a normal subgroup is its actual image in the
ambient radical quotient, through the restricted quotient map. -/
noncomputable def normalRadicalQuotientEquivImage (N : Subgroup G) [N.Normal] :
    N ⧸ solvableRadical N ≃*
      N.map (QuotientGroup.mk' (solvableRadical G)) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  apply QuotientGroup.liftEquiv (φ := q.subgroupMap N)
    (solvableRadical N) (q.subgroupMap_surjective N)
  rw [← radical_subgroupOf_normal N]
  ext x
  change (x : G) ∈ solvableRadical G ↔ q.subgroupMap N x = 1
  rw [Subtype.ext_iff]
  exact (QuotientGroup.eq_one_iff (x : G)).symm

omit [Finite G] in
/-- Passing to the radical quotient preserves a two-group quotient by the image. -/
theorem normal_radical_image_two_quotient (N : Subgroup G) [N.Normal]
    (hquot : IsPGroup 2 (G ⧸ N)) :
    IsPGroup 2 ((G ⧸ solvableRadical G) ⧸
      N.map (QuotientGroup.mk' (solvableRadical G))) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let D := N.map q
  let : D.Normal := Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  have hle : N ≤ D.comap q := le_comap_map q N
  exact hquot.of_surjective (QuotientGroup.map N D q hle)
    (QuotientGroup.map_surjective_of_surjective N D q
      ((QuotientGroup.mk'_surjective D).comp (QuotientGroup.mk'_surjective _)) hle)

/-- A nonabelian simple radical quotient identifies the literal generalized
Fitting subgroup in every ambient two-extension. -/
theorem generalizedFitting_radical_quotient_eq_image (N : Subgroup G) [N.Normal]
    [IsSimpleGroup (N ⧸ solvableRadical N)]
    (ha : ¬ IsMulCommutative (N ⧸ solvableRadical N))
    (hquot : IsPGroup 2 (G ⧸ N)) :
    generalizedFitting (G ⧸ solvableRadical G) =
      N.map (QuotientGroup.mk' (solvableRadical G)) := by
  let Q := G ⧸ solvableRadical G
  let q := QuotientGroup.mk' (solvableRadical G)
  let D := N.map q
  let e := normalRadicalQuotientEquivImage N
  let : D.Normal := Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup D := e.symm.isSimpleGroup
  have hD : ¬ IsMulCommutative D := by
    intro hc
    apply ha
    exact isMulCommutative_iff.mpr (fun a b => e.injective (by
      simpa only [map_mul] using (isMulCommutative_iff.mp hc) (e a) (e b)))
  have hcore : pCore 2 Q = ⊥ := by
    let : Group.IsNilpotent (pCore 2 Q) := (pCore_isPGroup (p := 2) (G := Q)).isNilpotent
    have hle := le_solvableRadical (pCore 2 Q) inferInstance inferInstance
    exact le_bot_iff.mp (hle.trans solvableRadical_quotient_solvableRadical.le)
  exact (simple_two_quotient_structure D hD
    (normal_radical_image_two_quotient N hquot) hcore).1

/-- The generalized Fitting subgroup is the normal subgroup modulo its own radical. -/
noncomputable def radicalTwoExtensionFittingEquiv (N : Subgroup G) [N.Normal]
    [IsSimpleGroup (N ⧸ solvableRadical N)]
    (ha : ¬ IsMulCommutative (N ⧸ solvableRadical N))
    (hquot : IsPGroup 2 (G ⧸ N)) :
    generalizedFitting (G ⧸ solvableRadical G) ≃* N ⧸ solvableRadical N :=
  (MulEquiv.subgroupCongr (generalizedFitting_radical_quotient_eq_image N ha hquot)).trans
    (normalRadicalQuotientEquivImage N).symm

/-- Simplicity survives in the generalized Fitting subgroup of the ambient radical quotient. -/
theorem radicalTwoExtension_fitting_simple (N : Subgroup G) [N.Normal]
    [IsSimpleGroup (N ⧸ solvableRadical N)]
    (ha : ¬ IsMulCommutative (N ⧸ solvableRadical N))
    (hquot : IsPGroup 2 (G ⧸ N)) :
    IsSimpleGroup (generalizedFitting (G ⧸ solvableRadical G)) :=
  (radicalTwoExtensionFittingEquiv N ha hquot).isSimpleGroup

/-- The simple generalized Fitting subgroup supplements every Sylow two-subgroup. -/
theorem radicalTwoExtension_fitting_sup_sylow (N : Subgroup G) [N.Normal]
    [IsSimpleGroup (N ⧸ solvableRadical N)]
    (ha : ¬ IsMulCommutative (N ⧸ solvableRadical N))
    (hquot : IsPGroup 2 (G ⧸ N))
    (S : Sylow 2 (G ⧸ solvableRadical G)) :
    generalizedFitting (G ⧸ solvableRadical G) ⊔ (S : Subgroup _) = ⊤ := by
  rw [generalizedFitting_radical_quotient_eq_image N ha hquot, sup_comm]
  exact S.sup_eq_top_of_quotient_isPGroup _ (normal_radical_image_two_quotient N hquot)

end Theory.GroupTheory
