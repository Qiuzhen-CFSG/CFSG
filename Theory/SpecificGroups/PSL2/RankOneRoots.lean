module

public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Binary PSL₂ root involutions and their centralizers

Sylow conjugacy puts every involution in the actual upper unipotent subgroup.
For a nonzero parameter, commuting with its transvection forces the lower-left
entry to vanish and the two diagonal entries to be one. Thus the centralizer
is the root group, a two-group contained in the corresponding Borel.
The long-root predicate records conjugacy to this explicit matrix element.

Source: the rank-one matrix calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 16.1.4(1) and 16.1.6,
printed pp.1171–1172.
-/

public section

open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups

namespace Theory.PSL2
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem unipotent_sylow :
    ∃ P : Sylow 2 (PSL2MatrixGroup K), (P : Subgroup _) = PUnip K := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  refine ⟨U.mapSurjective (f := pi K) pi_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective]
  change (Matrix.SpecialLinearGroup.upperUnipotent K).map (pi K) =
    (Unip K).map (pi K)
  congr 1
  ext g
  rw [Matrix.SpecialLinearGroup.mem_upperUnipotent, mem_Unip_iff]
  have htu (t : K) :
      Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t =
        uni t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]
  simp only [htu, eq_comm]

omit [Finite K] in
private theorem eq_uni_of_commute_uni {t : K} (ht : t ≠ 0) (g : SL2 K)
    (h : g * uni t = uni t * g) : g = uni (g.val 0 1) := by
  have h00 := congrArg (fun x : SL2 K => x.val 0 0) h
  have h01 := congrArg (fun x : SL2 K => x.val 0 1) h
  have hc : g.val 1 0 = 0 := by
    have he : t * g.val 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00.symm
    exact (mul_eq_zero.mp he).resolve_left ht
  have hd : g.val 0 0 = g.val 1 1 := by
    have he : g.val 0 0 * t = t * g.val 1 1 := by
      have he' : g.val 0 0 * t + g.val 0 1 = g.val 0 1 + t * g.val 1 1 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
      exact add_right_cancel (he'.trans (add_comm _ _))
    exact mul_right_cancel₀ ht (he.trans (mul_comm _ _))
  have ha : g.val 0 0 = 1 := by
    apply CharTwo.sq_injective
    simpa only [Matrix.det_fin_two, hc, ← hd, mul_zero, sub_zero, pow_two, one_mul]
      using g.property
  have hd1 : g.val 1 1 = 1 := hd.symm.trans ha
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, ha, hd1]

omit [Finite K] in
/-- The centralizer of a nonidentity upper root element is the upper root group. -/
theorem centralizer_root_eq {t : K} (ht : t ≠ 0) :
    centralizer {pi K (uni t)} = PUnip K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := pi_surjective x
    have hg : g * uni t = uni t * g := by
      apply pi_injective
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hx
    exact ⟨g, (mem_Unip_iff _).mpr ⟨g.val 0 1, eq_uni_of_commute_uni ht g hg⟩, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_Unip_iff g).mp hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      uni_mul_uni, uni_mul_uni, add_comm]

/-- A long-root involution is conjugate to a genuine nonzero upper transvection. -/
@[expose] def IsLongRootInvolution (x : PSL2MatrixGroup K) : Prop :=
  orderOf x = 2 ∧
    ∃ g : PSL2MatrixGroup K, ∃ t : K, t ≠ 0 ∧ MulAut.conj g x = pi K (uni t)

/-- Every involution is an actual long-root element up to conjugacy, and its
centralizer is a two-group contained in the corresponding proper Borel. -/
theorem involution_root_geometry (x : PSL2MatrixGroup K) (hx : orderOf x = 2) :
    ∃ (g : PSL2MatrixGroup K) (t : K), t ≠ 0 ∧
      MulAut.conj g x = pi K (uni t) ∧
      centralizer {x} ≤ (PBorel K).comap (MulAut.conj g).toMonoidHom ∧
      IsPGroup 2 (centralizer {x}) := by
  obtain ⟨P, hP⟩ := unipotent_sylow (K := K)
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, hx]
    exact dvd_refl 2
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup K) Q P
  have hroot : MulAut.conj g x ∈ PUnip K := by
    rw [← hP, ← hg]
    exact ⟨x, hQ (mem_zpowers x), rfl⟩
  obtain ⟨u, hu, he⟩ := hroot
  obtain ⟨t, rfl⟩ := (mem_Unip_iff u).mp hu
  have ht : t ≠ 0 := by
    intro ht
    have h : MulAut.conj g x = 1 := by simpa [ht, uni_zero] using he.symm
    have hx1 : x = 1 := (MulAut.conj g).injective (h.trans (map_one _).symm)
    simp [hx1] at hx
  have hle : centralizer {x} ≤ (PUnip K).comap (MulAut.conj g).toMonoidHom := by
    intro y hy
    rw [mem_comap, ← centralizer_root_eq ht, mem_centralizer_singleton_iff, he]
    exact (show Commute y x from mem_centralizer_singleton_iff.mp hy).map (MulAut.conj g)
  refine ⟨g, t, ht, he.symm, hle.trans (comap_mono PUnip_le_PBorel), ?_⟩
  have hU : IsPGroup 2 (PUnip K) := hP ▸ P.isPGroup'
  exact (hU.comap_of_injective _ (MulAut.conj g).injective).to_le hle

end Theory.PSL2
