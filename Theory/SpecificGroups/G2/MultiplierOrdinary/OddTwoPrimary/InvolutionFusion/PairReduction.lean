module

public import Theory.AtlasPort.LinearGroups.G2.VectorStabilizer
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# Conjugating an involution that fixes a singular octonion

Root and Weyl automorphisms carry the fixed singular vector to the first
coordinate line. Averaging the opposite basis vector gives a fixed vector with
polar pairing one; subtracting its norm times the first vector makes it singular.
The existing partner reduction then conjugates the involution into the actual
opposite-pair stabilizer SL₂. Its only nonidentity involution is minus identity.
All conjugators are multiplication-preserving linear automorphisms of the
original octonion model.

The finite-field fixed-vector premise is discharged in `InvolutionFusion`.
Application: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
The root, Weyl and partner reductions are from Gerald Höhn and the ATLAS
contributors' licensed port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion
open Atlas.SplitOctonion Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {F : Type*} [Field F]

private theorem twice_apply (g : Model F) (hg : g ^ 2 = 1) (v : Carrier F) :
    g.val (g.val v) = v := congrArg (fun a : Model F => a.val v) hg

private theorem exists_fixed_partner (hF : (2 : F) ≠ 0)
    (g : Model F) (hg : g ^ 2 = 1) (hfix : g.val (basisVector 0) = basisVector 0) :
    ∃ v : SingularPartners F, g.val v.val = v.val := by
  let z : Carrier F := (2 : F)⁻¹ • (basisVector 7 + g.val (basisVector 7))
  have hgz : g.val z = z := by
    dsimp [z]
    rw [map_smul, map_add, twice_apply g hg, add_comm]
  have ht : trace z = 0 := by
    have h := automorphism_trace g (basisVector 7)
    have ht7 : trace (basisVector 7 : Carrier F) = 0 := by simp [trace, basisVector]
    rw [ht7] at h
    change g.val (basisVector 7) 3 + g.val (basisVector 7) 4 = 0 at h
    dsimp [z, trace]
    simp [basisVector] at h ⊢
    linear_combination (2 : F)⁻¹ * h
  have hz7 : z 7 = 1 := by
    have h := fixingFirstVector_partner_last (⟨g,hfix⟩ : fixingFirstVector)
    change g.val (basisVector 7) 7 = 1 at h
    change (2 : F)⁻¹ * (basisVector 7 7 + g.val (basisVector 7) 7) = 1
    rw [h]
    norm_num [basisVector, Pi.single_apply]
    exact inv_mul_cancel₀ hF
  let v : Carrier F := z - norm z • basisVector 0
  have htv : trace v = 0 := by simpa [v, trace, basisVector] using ht
  have hnv : norm v = 0 := by
    simp only [v, norm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp [basisVector, Fin.ext_iff]
    rw [hz7]
    ring
  refine ⟨⟨v, htv, hnv, by simp [v, basisVector, hz7]⟩, ?_⟩
  change g.val v = v
  simp only [v, map_sub, map_smul, hgz, hfix]

private theorem pair_involution_eq (hF : (2 : F) ≠ 0)
    (g : PairStabilizer.fixingPair (F := F)) (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    g.val = PairStabilizer.blockHom (-1 : SL(2,F)) := by
  let a := PairStabilizer.imageSL g
  have ha : PairStabilizer.blockToPair a = g := PairStabilizer.block_imageSL g
  have hsq : a ^ 2 = 1 := by
    apply PairStabilizer.blockToPair_injective
    rw [map_pow, ha, hg, map_one]
  have hd : (toGL a).det = 1 := by
    apply Units.ext
    exact a.property
  have hs : (toGL a) ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (toGL a) hs hd with h | h
  · have he : a = 1 := toGL_injective (by simpa using h)
    exact (hne (by rw [← ha, he, map_one])).elim
  · have he : a = -1 := Subtype.ext (congrArg Units.val h)
    exact congrArg Subtype.val (ha.symm.trans (congrArg PairStabilizer.blockToPair he))

/-- A fixed singular vector places a nontrivial involution in the single SL₂ class. -/
theorem conjugate_of_fixed_singular (hF : (2 : F) ≠ 0) (g : Model F)
    (hg : g ^ 2 = 1) (hne : g ≠ 1) (v : Carrier F)
    (ht : trace v = 0) (hn : norm v = 0) (hv : v ≠ 0) (hfix : g.val v = v) :
    ∃ a : Model F, a * g * a⁻¹ = PairStabilizer.blockHom (-1 : SL(2,F)) := by
  obtain ⟨a, _, r, hr, hav⟩ := singular_vector_reduction_first v ht hn hv
  let k := a * g * a⁻¹
  have hk : k ^ 2 = 1 := by
    change ((MulAut.conj a) g) ^ 2 = 1
    rw [← map_pow, hg, map_one]
  have hkne : k ≠ 1 := by
    intro h
    apply hne
    have : g = a⁻¹ * k * a := by dsimp [k]; group
    rw [this, h]; group
  have hkfix : k.val (basisVector 0) = basisVector 0 := by
    have h : k.val (r • basisVector 0) = r • basisVector 0 := by
      rw [← hav]
      change a.val (g.val (a.val.symm (a.val v))) = a.val v
      rw [a.val.symm_apply_apply, hfix]
    rw [map_smul] at h
    exact (smul_right_injective _ hr) h
  obtain ⟨w, hw⟩ := exists_fixed_partner hF k hk hkfix
  let b := partnerSection w
  let q : PairStabilizer.fixingPair (F := F) := ⟨b.val * k * b.val⁻¹, by
    constructor
    · change b.val.val (k.val (b.val.val.symm (basisVector 0))) = basisVector 0
      have hi : b.val.val.symm (basisVector 0) = basisVector 0 := by
        apply b.val.val.injective
        rw [b.val.val.apply_symm_apply, b.property]
      rw [hi, hkfix, b.property]
    · change b.val.val (k.val (b.val.val.symm (basisVector 7))) = basisVector 7
      have hi : b.val.val.symm (basisVector 7) = w.val := by
        apply b.val.val.injective
        rw [b.val.val.apply_symm_apply, partnerSection_action]
      rw [hi, hw, partnerSection_action]⟩
  have hqs : q ^ 2 = 1 := by
    apply Subtype.ext
    change ((MulAut.conj b.val) k) ^ 2 = 1
    rw [← map_pow, hk, map_one]
  have hqn : q ≠ 1 := by
    intro h
    apply hkne
    have he : b.val * k * b.val⁻¹ = 1 := congrArg Subtype.val h
    have : k = b.val⁻¹ * (b.val * k * b.val⁻¹) * b.val := by group
    rw [this, he]; group
  refine ⟨b.val * a, ?_⟩
  have he := pair_involution_eq hF q hqs hqn
  change b.val * (a * g * a⁻¹) * b.val⁻¹ = _ at he
  convert he using 1
  group
end Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion

end
