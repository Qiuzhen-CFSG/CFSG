module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import Theory.SpecificGroups.SU3.SylowFixedInvolutions

/-!
# Fixed involutions and the unitary root-generated subgroup

The intrinsic fixed-involution theorem for SU₃ and PSU₃ transports through
actual model isomorphisms. If an automorphism of square one fixes a
nonidentity involution in P, it fixes Ω₁(P) pointwise. If it also fixes t,
it therefore fixes the literal subgroup `rootGenerated P t = ⟨Ω₁(P),t⟩`.
There is no condition placing t outside the Sylow normalizer.

Source: GLS, Volume 4, Chapter 4, Lemma 3.4(f), applied in Chapter 2,
Lemma 16.2(b3), Lemma 16.4 and Proposition 16.5. The descent through SU₃'s
actual odd scalar kernel and the arbitrary outer-automorphism case are
proved in `Theory.SpecificGroups.SU3.SylowFixedInvolutions`.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup BenderSuzuki.MatrixGroups

private theorem omega_fixed_of_equiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H)
    (hH : ∀ (P : Sylow 2 H) (z : H), z ∈ P → z ≠ 1 → z ^ 2 = 1 →
      ∀ (a : MulAut H), a ^ 2 = 1 → a z = z → omegaOneAmbient (P : Subgroup H) ≤ a.fixedSubgroup)
    (P : Sylow 2 G) (z : G) (hz : z ∈ P) (hne : z ≠ 1) (hz2 : z ^ 2 = 1)
    (a : MulAut G) (ha : a ^ 2 = 1) (hfix : a z = z) :
    omegaOneAmbient (P : Subgroup G) ≤ a.fixedSubgroup := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb2 : b ^ 2 = 1 := by
    dsimp only [b]
    rw [← map_pow, ha, map_one]
  have hbz : b (e z) = e z := by
    change e (a (e.symm (e z))) = e z
    rw [e.symm_apply_apply, hfix]
  have hQ := hH Q (e z) (mem_map_of_mem e.toMonoidHom hz)
    (fun h => hne (e.injective (h.trans (map_one _).symm)))
    (by rw [← map_pow, hz2, map_one]) b hb2 hbz
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  have hbx := (omegaOneAmbient_le_iff _ _).mp hQ (e x)
    (mem_map_of_mem e.toMonoidHom hx) (by rw [← map_pow, hx2, map_one])
  rw [MulAut.mem_fixedSubgroup] at hbx ⊢
  apply e.injective
  change e (a (e.symm (e x))) = e x at hbx
  simpa only [e.symm_apply_apply] using hbx

variable {G : Type*} [Group G] [Finite G]
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hn hJ hcard hfixed in
/-- The unitary fixed-involution implication transported through an actual PSU₃ isomorphism. -/
public theorem unitary_projective_omega_fixed
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 G) (z : G) (hz : z ∈ P) (hne : z ≠ 1) (hz2 : z ^ 2 = 1)
    (a : MulAut G) (ha : a ^ 2 = 1) (hfix : a z = z) :
    omegaOneAmbient (P : Subgroup G) ≤ a.fixedSubgroup :=
  omega_fixed_of_equiv e
    (HermitianForm.SylowFixedInvolutions.projective_omega_le_fixed J hn hJ hcard hfixed)
    P z hz hne hz2 a ha hfix

include hn hJ hcard hfixed in
/-- The same implication transported through an actual SU₃ isomorphism. -/
public theorem unitary_special_omega_fixed
    (e : G ≃* J.specialSubgroup)
    (P : Sylow 2 G) (z : G) (hz : z ∈ P) (hne : z ≠ 1) (hz2 : z ^ 2 = 1)
    (a : MulAut G) (ha : a ^ 2 = 1) (hfix : a z = z) :
    omegaOneAmbient (P : Subgroup G) ≤ a.fixedSubgroup :=
  omega_fixed_of_equiv e
    (HermitianForm.SylowFixedInvolutions.special_omega_le_fixed J hn hJ hcard hfixed)
    P z hz hne hz2 a ha hfix

include hn hJ hcard hfixed in
/-- The Section 16 root-generated subgroup is fixed when its additional generator is fixed. -/
public theorem unitary_projective_rootGenerated_fixed
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 G) (z : G) (hz : z ∈ P) (hne : z ≠ 1) (hz2 : z ^ 2 = 1)
    (a : MulAut G) (ha : a ^ 2 = 1) (hfix : a z = z)
    (t : G) (ht : a t = t) :
    rootGenerated (P : Subgroup G) t ≤ a.fixedSubgroup :=
  sup_le (unitary_projective_omega_fixed J hn hJ hcard hfixed e P z hz hne hz2 a ha hfix)
    (zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mpr ht))

include hn hJ hcard hfixed in
/-- The root-generated conclusion for SU₃, retaining its possible odd scalar center. -/
public theorem unitary_special_rootGenerated_fixed
    (e : G ≃* J.specialSubgroup)
    (P : Sylow 2 G) (z : G) (hz : z ∈ P) (hne : z ≠ 1) (hz2 : z ^ 2 = 1)
    (a : MulAut G) (ha : a ^ 2 = 1) (hfix : a z = z)
    (t : G) (ht : a t = t) :
    rootGenerated (P : Subgroup G) t ≤ a.fixedSubgroup :=
  sup_le (unitary_special_omega_fixed J hn hJ hcard hfixed e P z hz hne hz2 a ha hfix)
    (zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mpr ht))

end BenderSuzuki.ZD.RankOneModelGeometry
