module
public import ABG.ChapterII.Section2.WeakCenterTransport
public import ABG.ChapterII.Section1.WreathedQuaternionUnique
public import ABG.ChapterII.Section1.LargestQuaternion

/-!
# The enlarged Q-group definition

For finite groups, the union defining Q-groups agrees with the quaternion
overgroup formulation of ABG Chapter II Section 2 Definition 3. In particular,
the original full-Sylow alternatives satisfy that enlarged definition.

Use the original Sylow subgroup itself as the overgroup, with the identity
embedding, and retain the normal subgroup K in its fusion pattern. Normality
identifies the Sylow intersection with a Sylow subgroup of K, so it is
generalized quaternion. The prescribed power-of-two index is preserved on
restriction to the Sylow subgroup. Thus its order is exactly the order of the
largest quaternion subgroup supplied by the quasi-dihedral or wreathed
structure theorem. Containment and equal orders identify the intersection
with that subgroup. Weak closure is supplied by the same Q-group witness.
The wreathed intersection result is also public for the quaternion-kernel
Q witness in II.3 Lemma 3; it retains the actual subgroup and Sylow maps.

Source: `refs/latex/alperin-brauer-gorenstein-pages/page-015.tex`, article p.14,
Definitions 1 and 3 and their connecting paragraph. This removes the redundant
original-class disjunct without altering the public source definitions.
-/

namespace ABG
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Restriction of an ambient Sylow subgroup to a normal subgroup with
generalized quaternion Sylow subgroups is generalized quaternion. -/
public theorem normal_sylow_intersection_isGeneralizedQuaternion
    (S : Sylow 2 G) (K : Subgroup G)
    [K.Normal] (hK : HasGeneralizedQuaternionSylowTwo K) :
    IsGeneralizedQuaternionGroup (K.comap (S : Subgroup G).subtype) := by
  obtain ⟨R, n, hn, ⟨e⟩⟩ := hK
  let T := BenderSuzuki.External.hallSylowSubgroupOfNormal S K
  let f : K.comap (S : Subgroup G).subtype ≃* T := {
    toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact ⟨n, hn, ⟨f.trans ((T.equiv R).trans e)⟩⟩

/-- A normal subgroup of two-power index retains its index on intersection
with any Sylow two-subgroup. -/
public theorem normal_sylow_intersection_index (S : Sylow 2 G) (K : Subgroup G)
    [K.Normal] {n : ℕ} (hK : K.index = 2 ^ n) :
    (K.comap (S : Subgroup G).subtype).index = 2 ^ n := by
  have hquot : IsPGroup 2 (G ⧸ K) := IsPGroup.of_card (by rwa [← K.index_eq_card])
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let Sq : Sylow 2 (G ⧸ K) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective K)
  have htop : (Sq : Subgroup (G ⧸ K)) = ⊤ :=
    (Sq.is_maximal' (hquot.to_subgroup ⊤) le_top).symm
  change K.relIndex (S : Subgroup G) = 2 ^ n
  calc
    K.relIndex (S : Subgroup G) = q.ker.relIndex (S : Subgroup G) := by
      rw [show q.ker = K from QuotientGroup.ker_mk' K]
    _ = Nat.card ((S : Subgroup G).map q) := Subgroup.relIndex_ker _ q
    _ = Nat.card (Sq : Subgroup (G ⧸ K)) := by rw [Sylow.coe_mapSurjective]
    _ = Nat.card (G ⧸ K) := by rw [htop, Subgroup.card_top]
    _ = 2 ^ n := by rwa [← K.index_eq_card]

/-- The actual Sylow intersection is the unique largest quaternion subgroup
when the normal subgroup has the prescribed wreathed two-power index. -/
public theorem wreathed_intersection_largest (S : Sylow 2 G) {n : ℕ}
    (hS : IsWreathedOfHeight S n) (K : Subgroup G) [K.Normal]
    (hindex : K.index = 2 ^ n) (hK : HasGeneralizedQuaternionSylowTwo K) :
    IsLargestQuaternionSubgroup (K.comap (S : Subgroup G).subtype) := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  have hQ := normal_sylow_intersection_isGeneralizedQuaternion S K hK
  have hI := normal_sylow_intersection_index S K hindex
  have hcard := (K.comap (S : Subgroup G).subtype).card_mul_index
  rw [hI, hS.2.1] at hcard
  have hcard' : Nat.card (K.comap (S : Subgroup G).subtype) = 2 ^ (n + 1) := by
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n)
    rw [hcard, ← pow_add]
    congr 1
    omega
  have heq := P.quaternion_unique _ hQ hcard'
  rw [heq]
  refine ⟨P.quaternion_subgroup.1, fun Z hZ => ?_⟩
  have hle := P.quaternion_le_Y Z hZ
  exact ⟨Subgroup.card_le_of_le hle,
    fun hc => Subgroup.eq_of_le_of_card_ge hle hc.ge⟩

private theorem semi_intersection_largest
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (K : Subgroup G) [K.Normal] (hindex : K.index = 2)
    (hK : HasGeneralizedQuaternionSylowTwo K) :
    IsLargestQuaternionSubgroup (K.comap (S : Subgroup G).subtype) := by
  obtain ⟨Y, hY, hiY, hmax⟩ := QuasiDihedral.exists_largest_quaternion hS
  have hQ := normal_sylow_intersection_isGeneralizedQuaternion S K hK
  have hI := normal_sylow_intersection_index S K (n := 1) (by simpa using hindex)
  have hcQ := (K.comap (S : Subgroup G).subtype).card_mul_index
  have hcY := Y.card_mul_index
  rw [hI] at hcQ
  rw [hiY] at hcY
  have heq : K.comap (S : Subgroup G).subtype = Y :=
    Subgroup.eq_of_le_of_card_ge (hmax _ hQ) (by omega)
  rw [heq]
  refine ⟨hY, fun Z hZ => ?_⟩
  have hle := hmax Z hZ
  exact ⟨Subgroup.card_le_of_le hle,
    fun hc => Subgroup.eq_of_le_of_card_ge hle hc.ge⟩

/-- For finite groups, Definition 3 already includes every Q-group from
Definition 1, so the enlarged union equals its overgroup formulation. -/
public theorem isQGroup_iff_quaternionOvergroup :
    IsQGroup G ↔ IsQuaternionOvergroupQGroup G := by
  refine ⟨?_, Or.inr⟩
  rintro (hfull | hover)
  · have hQ : IsQGroup G := Or.inl hfull
    rcases hfull with ⟨S, T, Q, hframe, hpattern⟩ | ⟨S, n, U, V, hframe, hpattern⟩
    · obtain ⟨K, hnormal, hindex, hK, hno⟩ := hpattern.1
      let := hnormal
      refine ⟨S, inferInstance, Or.inl hframe.1, S, MonoidHom.id S,
        K.comap (S : Subgroup G).subtype, K, Function.injective_id,
        semi_intersection_largest S hframe.1 K hindex hK,
        hnormal, ⟨1, by simpa using hindex⟩, hno,
        hQ.hasWeaklyClosedCenterSubgroups S, ?_⟩
      exact Subgroup.map_id _
    · obtain ⟨K, hnormal, hindex, hK, hno⟩ := hpattern.1
      let := hnormal
      refine ⟨S, inferInstance, Or.inr ⟨n, hframe.1⟩, S, MonoidHom.id S,
        K.comap (S : Subgroup G).subtype, K, Function.injective_id,
        wreathed_intersection_largest S hframe.1 K hindex hK,
        hnormal, ⟨n, hindex⟩, hno, hpattern.2.1, ?_⟩
      exact Subgroup.map_id _
  · exact hover

end ABG
