module
public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import ABG.ChapterII.Section1.WreathedCenter

/-!
# Normal quaternion witnesses for enlarged Q-groups

For a finite Q-group with a prescribed semidihedral or wreathed Sylow
subgroup S, there is a normal subgroup K with generalized quaternion Sylow
two-subgroups, no normal subgroup of index two, and index |Z(S)|.
This supplies the first paragraph of ABG II.3 Proposition 2 (article p22)
from the full enlarged definition, II.2 Definition 3 (article p14).

The definition embeds a Sylow subgroup R into a larger two-group and maps
R intersect K onto its largest quaternion subgroup Y. Normality makes the
intersections with R and S Sylow subgroups of K, of equal order. Any
quaternion subgroup of S maps through a Sylow equivalence and the embedding
to a quaternion subgroup of the overgroup; hence its order is at most |Y|.
Consequently S intersect K is the intrinsic largest quaternion subgroup of
S. Its semidihedral or wreathed presentation computes its index as |Z(S)|,
and the normal two-power-index restriction theorem gives the ambient index.
The overgroup need not equal the actual Sylow subgroup.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

private theorem intersection_equiv (R : Sylow 2 G) (K : Subgroup G) [K.Normal] :
    Nonempty ((K.comap (R : Subgroup G).subtype) ≃*
      BenderSuzuki.External.hallSylowSubgroupOfNormal R K) := by
  exact ⟨{
    toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }⟩

private theorem quaternion_map {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (Q : Subgroup A)
    (hQ : IsGeneralizedQuaternionGroup Q) : IsGeneralizedQuaternionGroup (Q.map f) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  exact ⟨n, hn, ⟨(Subgroup.equivMapOfInjective Q f hf).symm.trans e⟩⟩

private theorem largest_index (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (Q : Subgroup S) (hQ : IsGeneralizedQuaternionGroup Q)
    (hmax : ∀ T : Subgroup S, IsGeneralizedQuaternionGroup T →
      Nat.card T ≤ Nat.card Q) :
    Q.index = Nat.card (Subgroup.center S) := by
  rcases hS with hs | ⟨n, hn⟩
  · obtain ⟨Y, hY, hiY, hle⟩ := QuasiDihedral.exists_largest_quaternion hs
    have heq := Subgroup.eq_of_le_of_card_ge (hle Q hQ) (hmax Y hY)
    rw [heq, hiY, QuasiDihedral.card_center hs]
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hn
    have heq := Subgroup.eq_of_le_of_card_ge (P.quaternion_le_Y Q hQ)
      (hmax P.Y P.quaternion_subgroup.1)
    rw [heq, P.card_center]
    have hc := P.Y.card_mul_index
    rw [P.quaternion_subgroup.2.1, hn.2.1] at hc
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (n + 1))
    rw [hc, ← pow_add]
    congr 1
    omega

/-- The normal subgroup required by ABG II.3 Proposition 2 exists for the
full enlarged Q-group definition and any prescribed full Sylow subgroup. -/
public theorem qGroup_exists_normal_quaternion_witness
    (hQ : IsQGroup G) (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    ∃ K : Subgroup G, K.Normal ∧ HasGeneralizedQuaternionSylowTwo K ∧
      HasNoNormalIndexTwoSubgroup K ∧ K.index = Nat.card (Subgroup.center S) := by
  obtain ⟨A, instA, hA, R, f, Y, K, hf, hY, hKnormal, ⟨m, hi⟩, hno, hw, heq⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hQ
  let := instA
  let := hKnormal
  let QR := K.comap (R : Subgroup G).subtype
  let QS := K.comap (S : Subgroup G).subtype
  let eY : QR ≃* Y := (Subgroup.equivMapOfInjective QR f hf).trans
    (MulEquiv.subgroupCongr heq)
  have hQR : IsGeneralizedQuaternionGroup QR := by
    obtain ⟨n, hn, ⟨e⟩⟩ := hY.1
    exact ⟨n, hn, ⟨eY.trans e⟩⟩
  obtain ⟨eR⟩ := intersection_equiv R K
  have hK : HasGeneralizedQuaternionSylowTwo K := by
    obtain ⟨n, hn, ⟨e⟩⟩ := hQR
    exact ⟨BenderSuzuki.External.hallSylowSubgroupOfNormal R K,
      n, hn, ⟨eR.symm.trans e⟩⟩
  have hQS := normal_sylow_intersection_isGeneralizedQuaternion S K hK
  obtain ⟨eS⟩ := intersection_equiv S K
  have hcard : Nat.card QS = Nat.card Y :=
    (Nat.card_congr (eS.trans ((BenderSuzuki.External.hallSylowSubgroupOfNormal S K).equiv
      (BenderSuzuki.External.hallSylowSubgroupOfNormal R K))).toEquiv).trans
      ((Nat.card_congr eR.toEquiv).symm.trans (Nat.card_congr eY.toEquiv))
  refine ⟨K, hKnormal, hK, hno,
    (hi.trans (normal_sylow_intersection_index S K hi).symm).trans ?_⟩
  apply largest_index S hS QS hQS
  intro T hT
  let g : S →* A := f.comp (S.equiv R).toMonoidHom
  have hg : Function.Injective g := hf.comp (S.equiv R).injective
  have hbound := (hY.2 (T.map g) (quaternion_map g hg T hT)).1
  rw [Subgroup.card_map_of_injective hg, ← hcard] at hbound
  exact hbound

end ABG

