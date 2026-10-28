module
public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import ABG.ChapterII.Section2.QuaternionWeakCenter

/-!
# A normal quaternion kernel inside a wreathed group is a Q-group

Suppose a finite group has wreathed Sylow two-subgroup of height n and
normal subgroup K of index 2^n. If K has generalized quaternion Sylow
two-subgroups and no normal subgroup of index two, then K is a Q-group
in the enlarged ABG definition. No ambient fusion-pattern assumption is
needed beyond these explicit structural hypotheses.

Intersect the actual ambient Sylow subgroup with K. Its induced Sylow
subgroup embeds back into that same wreathed group, with image the unique
largest quaternion subgroup by the index calculation. Use the whole of K
as its own normal index-one witness. Quaternion central subgroups are
weakly closed, which supplies the remaining clause of the definition.

This is the final implicit kernel-identification step in ABG II.3 Lemma 3,
article page 30, using the enlarged definition in II.2 Definition 3.
-/

namespace ABG

public theorem normal_quaternion_kernel_isQGroup {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (hS : IsWreathedOfHeight S n)
    (K : Subgroup G) [K.Normal] (hindex : K.index = 2 ^ n)
    (hK : HasGeneralizedQuaternionSylowTwo K)
    (hno : HasNoNormalIndexTwoSubgroup K) : IsQGroup K := by
  let R := BenderSuzuki.External.hallSylowSubgroupOfNormal S K
  let Q := K.comap (S : Subgroup G).subtype
  let e : R ≃* Q := {
    toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let f : R →* S := Q.subtype.comp e.toMonoidHom
  have hQR := normal_sylow_intersection_isGeneralizedQuaternion S K hK
  have hR : IsGeneralizedQuaternionGroup R := by
    obtain ⟨m, hm, ⟨em⟩⟩ := hQR
    exact ⟨m, hm, ⟨e.trans em⟩⟩
  have htopno : HasNoNormalIndexTwoSubgroup (⊤ : Subgroup K) := by
    intro A hA hi
    let t : (⊤ : Subgroup K) ≃* K := Subgroup.topEquiv
    have hN : (A.map t.toMonoidHom).Normal :=
      Subgroup.Normal.map hA t.toMonoidHom t.surjective
    apply hno (A.map t.toMonoidHom) hN
    exact (Subgroup.index_map_of_bijective t.bijective A).trans hi
  apply Or.inr
  refine ⟨S, inferInstance, Or.inr ⟨n, hS⟩, R, f, Q, ⊤,
    Q.subtype_injective.comp e.injective, wreathed_intersection_largest S hS K hindex hK,
    inferInstance, ⟨0, by simp⟩, htopno, hasWeaklyClosedCenterSubgroups_of_quaternion _ hR, ?_⟩
  change ((⊤ : Subgroup K).comap (R : Subgroup K).subtype).map f = Q
  rw [Subgroup.comap_top, ← MonoidHom.range_eq_map]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e y).property
  · intro hx
    exact ⟨e.symm ⟨x, hx⟩, by simp [f]⟩


end ABG

