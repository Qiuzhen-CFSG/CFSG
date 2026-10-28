module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.M10Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer

/-!
# The marked normalizer configuration and braid adjustment

The compatible Aut(A₆) normalizer of the marked S₆ supplies its genuine
M₁₀ subgroup L and K = L ∩ N_G(D), with the three-transitive action on
L/K. The ambient nine-group normalizer and the marked Q_b calculation
construct the involution v and identify the cube of vr.

Write b = uz. The normalizer of P fixes b because its line is the
characteristic center of P. If (vr)³ = b, replace r by br. Since b commutes
with v and r and lies in K, this replacement makes the cube trivial and
preserves KrK. Two involutions with product cube one satisfy the braid
relation required by the final double-coset construction.

The cube relation for vz also excludes v from L: in N_G(L)/L the image of
vz would otherwise have both square and cube one, forcing z into L.
The resulting theorem consumes the literal normalizer K = L ∩ N_G(D).
The final assembly constructs all three normalizer contracts from the
original local hypotheses and the explicit symmetric-six marking. It leaves
only the earlier construction of that marking to the eleven-subgroup owner.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.8–4.9 and the local calculation in 4.10, pp.41–42.
-/

open Subgroup DoubleCoset
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
variable {G : Type*} [Group G]

private theorem braid_of_cube {v r : G} (hv : v * v = 1) (hr : r * r = 1)
    (hc : (v * r) ^ 3 = 1) : v * r * v = r * v * r := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have he : v * r * v * (r * v * r) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hc
  have hi := eq_inv_of_mul_eq_one_left he
  simpa only [mul_inv_rev, hv', hr', mul_assoc] using hi

private theorem adjust_braid (L K : Subgroup G) (hKL : K ≤ L) (b r v : G)
    (hbK : b ∈ K) (hb : b * b = 1) (hrL : r ∈ L)
    (hr : r * r = 1) (hv : v * v = 1)
    (hbr : Commute b r) (hbv : Commute b v)
    (hcover : ∀ l ∈ L, l ∈ K ∨ l ∈ doubleCoset r K K)
    (hc : (v * r) ^ 3 = 1 ∨ (v * r) ^ 3 = b) :
    ∃ r' ∈ L, (∀ l ∈ L, l ∈ K ∨ l ∈ doubleCoset r' K K) ∧
      v * r' * v = r' * v * r' := by
  rcases hc with hc | hc
  · exact ⟨r, hrL, hcover, braid_of_cube hv hr hc⟩
  · have hb2 : b ^ 2 = 1 := by simpa only [pow_two] using hb
    have hbr2 : (b * r) * (b * r) = 1 := by
      simpa only [pow_two, hb, hr, one_mul] using hbr.mul_pow 2
    have hbcube : b ^ 3 = b := by rw [pow_succ, hb2, one_mul]
    have hc' : (v * (b * r)) ^ 3 = 1 := by
      rw [← mul_assoc, hbv.eq.symm, mul_assoc, (hbv.mul_right hbr).mul_pow,
        hbcube, hc, hb]
    refine ⟨b * r, L.mul_mem (hKL hbK) hrL, ?_, braid_of_cube hv hbr2 hc'⟩
    intro l hl
    rcases hcover l hl with hk | hd
    · exact Or.inl hk
    · apply Or.inr
      have he : doubleCoset (b * r) K K = doubleCoset r K K := by
        apply doubleCoset_eq_of_mem
        exact mem_doubleCoset.mpr ⟨b, hbK, 1, K.one_mem, by simp⟩
      rwa [he]

variable [Finite G] {z : G} {h : Hypotheses z} {a : SourceGeometry h}

/-- The center of the actual semidihedral complement fixes the adjustment
involution under the action of r. -/
public theorem M10NormalizerGeometry.b_commutes_r {s : SymmetricSixData h a}
    (m : M10NormalizerGeometry s) : Commute (s.u * z) m.r := by
  have hc := normalizer_le_centralizer_of_characteristic_involution
    m.P (center m.P) (s.u * z) s.uz_order m.center_P m.r_normalizes_P
  exact (mem_centralizer_singleton_iff.mp hc).symm

/-- The distinguished coset has order two; its product with v cannot have
cube one when v lies in L. This gives the strictness without a model tag. -/
public theorem NormalizerCubeData.v_not_mem {s : SymmetricSixData h a}
    {m : M10NormalizerGeometry s} (c : NormalizerCubeData s m) : c.v ∉ m.L := by
  intro hv
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two, h.involution] using pow_orderOf_eq_one z)
  have hconj : z * c.v * z ∈ m.L := by
    simpa only [hz] using (mem_normalizer_iff.mp m.z_normalizes c.v).mp hv
  have hw2 : (c.v * z) ^ 2 ∈ m.L := by
    simpa only [pow_two, mul_assoc] using m.L.mul_mem hv hconj
  have hw : c.v * z ∈ m.L := by
    have he : (c.v * z) ^ 2 * (c.v * z) = 1 := by
      simpa only [pow_succ] using c.vz_cube
    rw [← inv_eq_of_mul_eq_one_right he]
    exact m.L.inv_mem hw2
  apply m.z_not_mem
  simpa only [inv_mul_cancel_left] using m.L.mul_mem (m.L.inv_mem hv) hw

/-- Complete the local adjustment and provide the exact input used by the
already-built eleven-point double-coset construction. The geometry and cube
input have independent producers, whose premises must still be discharged. -/
public theorem nonempty_markedLocalData_of_normalizerCubeData
    {s : SymmetricSixData h a} (m : M10NormalizerGeometry s)
    (c : NormalizerCubeData s m) : Nonempty (MarkedLocalData z) := by
  obtain ⟨r, hr, hcover, hbraid⟩ := adjust_braid m.L (s.markedK m.L)
    (s.markedK_le m.L) (s.u * z) m.r c.v m.b_mem_K
    (by simpa only [pow_two] using s.uz_sq) m.r_mem m.r_sq c.v_sq
    m.b_commutes_r c.v_commutes_b m.cover c.vr_cube
  exact ⟨{
    L := m.L
    K := s.markedK m.L
    le := s.markedK_le m.L
    card_L := m.card_L
    card_K := m.card_K
    transitive := m.transitive
    v := c.v
    v_sq := c.v_sq
    v_not_mem := c.v_not_mem
    v_normalizes := c.v_normalizes
    r := r
    r_mem := hr
    cover := hcover
    braid := hbraid
    z_normalizes := m.z_normalizes
    z_not_mem := m.z_not_mem
    vz_cube := c.vz_cube }⟩

/-- The marked local configuration of 4.8–4.10 from the supplied S₆.
The compatible full normalizer, marked M₁₀ geometry, and exact cube
alternative are constructed here, and the adjustment of r supplies the
braid relation. No additional normalizer or local-relation premise remains. -/
public theorem nonempty_markedLocalData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) (s : SymmetricSixData h a) :
    Nonempty (MarkedLocalData z) := by
  obtain ⟨n⟩ := nonempty_symmetricNormalizerData h hn d a s
  obtain ⟨m⟩ := n.nonempty_m10NormalizerGeometry
  obtain ⟨c⟩ := nonempty_normalizerCubeData h hn d a s n m
  exact nonempty_markedLocalData_of_normalizerCubeData m c

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
