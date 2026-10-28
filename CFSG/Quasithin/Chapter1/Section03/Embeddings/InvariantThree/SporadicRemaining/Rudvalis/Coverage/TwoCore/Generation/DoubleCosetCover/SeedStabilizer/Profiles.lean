module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SeedStabilizer.ProfileData

/-!
# Invariance of seed-profile multiplicity

An element preserving the seed carries equal profiles to equal profiles:
it permutes the seed and preserves the certified orbital relation. Hence
it bijects their fibers and preserves the number of points with each profile.
Combining this invariant with fixed points supplies the initial colors for
the stabilizer calculation.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. The seed and action conventions are those of
`SectorGeometry`; `ProfileData` certifies the finite profile calculation.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover.SeedStabilizerCertificate
open OuterNormalizer OuterNormalizer.RigidityCertificate
open OuterNormalizer.InvarianceCertificate
open scoped Pointwise

private theorem profile_bit_iff (x : Fin 4060) (j : Fin 28) :
    (profileMask (profileId x)).testBit j.val = true ↔ adj (seedPoint j) x := by
  rw [profile_bits]
  exact cachedAdj_iff_adj _ _

/-- The numerical class labels mean equality of the actual seed profiles. -/
public theorem profileId_eq_iff (x y : Fin 4060) :
    profileId x = profileId y ↔ ∀ z, z ∈ seed → (adj z x ↔ adj z y) := by
  constructor
  · intro h z hz
    obtain ⟨j, rfl⟩ := (seed_mem_iff z).mp hz
    rw [← profile_bit_iff, ← profile_bit_iff, h]
  · intro h
    apply profileMask_injective
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 28
    · exact Bool.eq_iff_iff.mpr ((profile_bit_iff x ⟨j, hj⟩).trans
        ((h (seedPoint ⟨j, hj⟩) (seedPoint_mem _)).trans
          (profile_bit_iff y ⟨j, hj⟩).symm))
    · have hb : 2 ^ 28 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow ((profileMask_bound _).trans_le hb),
        Nat.testBit_lt_two_pow ((profileMask_bound _).trans_le hb)]

private theorem model_preserves_adj (g : Model) : g.val ∈ relationAut :=
  model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.property

private theorem seed_mem_smul (g : Model) (hg : g ∈ seedStabilizer) (x : Fin 4060) :
    g • x ∈ seed ↔ x ∈ seed := by
  change g • seed = seed at hg
  simpa only [hg] using (Finset.smul_mem_smul_finset_iff g (b := x) (s := seed))

/-- Setwise seed preservation permutes the profile classes. -/
public theorem profileId_eq_preserved (g : Model) (hg : g ∈ seedStabilizer)
    (x y : Fin 4060) :
    profileId (g • x) = profileId (g • y) ↔ profileId x = profileId y := by
  rw [profileId_eq_iff, profileId_eq_iff]
  constructor
  · intro h z hz
    exact (model_preserves_adj g z x).symm.trans
      ((h (g • z) ((seed_mem_smul g hg z).mpr hz)).trans
        (model_preserves_adj g z y))
  · intro h z hz
    obtain ⟨w, rfl⟩ := MulAction.surjective g z
    exact (model_preserves_adj g w x).trans
      ((h w ((seed_mem_smul g hg w).mp hz)).trans
        (model_preserves_adj g w y).symm)

/-- The size of a profile fiber is an invariant of the seed stabilizer. -/
public theorem profileSize_preserved (g : Model) (hg : g ∈ seedStabilizer)
    (x : Fin 4060) : profileSize (profileId (g • x)) = profileSize (profileId x) := by
  have hv : vertices.Nodup := List.nodup_ofFn.mpr Function.injective_id
  have he : (vertices.map (fun y => g • y)).Perm vertices := by
    apply (List.perm_ext_iff_of_nodup (hv.map (MulAction.injective g)) hv).mpr
    intro y
    have hv' (z : Fin 4060) : z ∈ vertices := List.mem_ofFn.mpr ⟨z, rfl⟩
    constructor
    · intro _
      exact hv' y
    · intro _
      exact List.mem_map.mpr ⟨g⁻¹ • y, hv' _, smul_inv_smul g y⟩
  rw [profileSize_eq, profileSize_eq, ← he.countP_eq, List.countP_map]
  apply List.countP_congr
  intro y _
  simpa only [Function.comp_apply, beq_iff_eq] using profileId_eq_preserved g hg y x

/-- Fixed points combined with the intrinsic profile multiplicity. -/
@[expose] public def seedColor (k : Nat) (x : Fin 4060) : Nat :=
  initial k x * 100 + profileSize (profileId x)

public theorem seedColor_preserved (k : Nat) (g : Model) (hg : g ∈ seedStabilizer)
    (hf : ∀ x : Fin 4060, x.val < k → g • x = x) :
    ∀ x, seedColor k (g • x) = seedColor k x := by
  intro x
  exact congrArg₂ (fun m n : Nat => m * 100 + n)
    (initial_preserved k g.val hf x) (profileSize_preserved g hg x)

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover.SeedStabilizerCertificate
