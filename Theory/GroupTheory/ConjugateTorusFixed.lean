module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Free action of a conjugate torus on a local center

Conjugate a fixed point back into the original Sylow subgroup. If every
nonidentity element of the original torus has only central fixed points,
the point centralizes both tori. Their joint fixed-point subgroup is
trivial, so the conjugate torus acts freely on the nonidentity center.
Source: Aschbacher–Smith, Lemma 2.4.8(4), printed p.530.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G]
lemma conjugate_torus_free_on_center
    (L R D B : Subgroup G) (x : G)
    (hR : x ∈ normalizer (R : Set G))
    (hZR : (center L).map L.subtype ≤ R)
    (hDL : D ≤ L)
    (hB : B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom)
    (hfix : R ⊓ centralizer (B : Set G) = ⊥)
    (hlocal : ∀ d ∈ D, d ≠ 1 → ∀ r ∈ R, Commute d r → r ∈ centralizer (L : Set G)) :
    ∀ a ∈ D.map (MulAut.conj x⁻¹).toMonoidHom, a ≠ 1 →
      ∀ z ∈ (center L).map L.subtype, Commute a z → z = 1 := by
  intro a ha ha1 z hz haz
  obtain ⟨d,hd,rfl⟩ := ha
  have hd1 : d ≠ 1 := by rintro rfl; exact ha1 (map_one _)
  have hzR := hZR hz
  have hxzR : x*z*x⁻¹ ∈ R := (mem_normalizer_iff.mp hR z).mp hzR
  have hxcomm : Commute d (x*z*x⁻¹) := by
    have hh := haz.map (MulAut.conj x).toMonoidHom
    change Commute (x*(x⁻¹*d*(x⁻¹)⁻¹)*x⁻¹) (x*z*x⁻¹) at hh
    simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using hh
  have hxcentral := hlocal d hd hd1 _ hxzR hxcomm
  have hzDx : z ∈ centralizer (D.map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
    apply mem_centralizer_iff.mpr
    rintro b ⟨e,he,rfl⟩
    have hh := congrArg (MulAut.conj x⁻¹) ((mem_centralizer_iff.mp hxcentral) e (hDL he))
    simp only [MulAut.conj_apply, inv_inv] at hh
    change (x⁻¹*e*(x⁻¹)⁻¹)*z = z*(x⁻¹*e*(x⁻¹)⁻¹)
    rw [inv_inv]
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel, inv_mul_cancel, mul_one] using hh
  have hzD : z ∈ centralizer (D : Set G) := by
    obtain ⟨z,hz,rfl⟩ := hz
    apply mem_centralizer_iff.mpr
    intro d hd
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨d,hDL hd⟩ : L))
  have hzB : z ∈ centralizer (B : Set G) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    have hz : B ≤ centralizer ({z} : Set G) := by
      rw [hB]
      exact sup_le ((le_centralizer_iff.mp (show zpowers z ≤ centralizer (D : Set G) from zpowers_le.mpr hzD)).trans (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers z))))
        ((le_centralizer_iff.mp (show zpowers z ≤ centralizer (D.map (MulAut.conj x⁻¹).toMonoidHom : Set G) from zpowers_le.mpr hzDx)).trans (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers z))))
    exact ((mem_centralizer_iff.mp (hz hb)) z (Set.mem_singleton z)).symm
  exact mem_bot.mp (hfix ▸ (show z ∈ R ⊓ centralizer (B : Set G) from ⟨hzR,hzB⟩))

end Subgroup
