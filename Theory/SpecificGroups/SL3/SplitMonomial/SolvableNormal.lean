module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.SpecificGroups.SL3.SplitMonomial.InvariantBasis
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal.NormalizerBound
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal.WeightKernel
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SL3.InvolutionBlock

/-!
# Noncentral abelian normal subgroups of solvable SL₃ overgroups

Suppose every abelian subgroup normal in a solvable subgroup H is scalar.
The center of each prime core is characteristic in H, so the scalar-center
order bound forces all prime cores other than O₃(H) to vanish. Thus F(H) is
O₃(H). Fitting self-centralization shows that O₃(H) is nonabelian whenever
H is nonabelian. Its ambient image is normal relative to H.

The determinant-corrected GL₂ block embedding also shows that every Sylow
two-subgroup of SL₃ over an odd finite field has order divisible by sixteen.
Consequently a bound of eight on two-subgroups of nonabelian three-group
normalizers suffices for a noncentral abelian normal subgroup of H. The
weight-kernel and normalizer-orbit theorems prove this bound in characteristic
different from three. Combining these results gives the required subgroup
for a solvable overgroup of a full ambient Sylow two-subgroup containing a
nonabelian three-subgroup.

This is an alternative Fitting reduction for the solvable case of GLS3,
Theorem 6.5.3(a–d), `refs/KGroup/GLS3/chapter6.tex`, used in Aschbacher–Smith,
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`). It does
not assume that the initially supplied nonabelian three-subgroup is normal.
-/

public section

open Subgroup
open scoped IsMulCommutative
private theorem other_core_eq_bot
    {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Z : Subgroup G) (hZ : IsPGroup p Z)
    (hA : ∀ A : Subgroup G, A.Normal → IsMulCommutative A → A ≤ Z)
    (hqp : q ≠ p) : pCore q G = ⊥ := by
  classical
  let P := pCore q G
  let C := (center P).map P.subtype
  have hc : C ≤ Z := hA C inferInstance inferInstance
  have hcp : IsPGroup q C := (pCore_isPGroup.to_subgroup (center P)).map P.subtype
  have hd := IsPGroup.disjoint_of_ne q p hqp C Z hcp hZ
  have hc0 : C = ⊥ := bot_unique ((le_inf le_rfl hc).trans hd.le_bot)
  have hz0 : center P = ⊥ := (map_eq_bot_iff_of_injective _ P.subtype_injective).mp hc0
  by_contra hp0
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hp0
  exact (Subgroup.nontrivial_iff_ne_bot _).mp
    (IsPGroup.center_nontrivial (pCore_isPGroup (p := q) (G := G))) hz0

private theorem fitting_eq_pCore_of_abelian_normals_le_pgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Z : Subgroup G) (hZ : IsPGroup p Z)
    (hA : ∀ A : Subgroup G, A.Normal → IsMulCommutative A → A ≤ Z) :
    fittingSubgroup G = pCore p G := by
  apply le_antisymm _ (pCore_le_fitting G p)
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun q => ?_
  by_cases heq : q.val.val = p
  · rw [heq]
  · rw [other_core_eq_bot Z hZ hA heq]
    exact bot_le

private theorem nonabelian_pCore_of_abelian_normals_le_central_pgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Z : Subgroup G) (hZ : IsPGroup p Z) (hZc : Z ≤ center G)
    (hA : ∀ A : Subgroup G, A.Normal → IsMulCommutative A → A ≤ Z)
    (hs : Group.IsSolvable G) (hn : ¬ IsMulCommutative G) :
    ¬ IsMulCommutative (pCore p G) := by
  intro hcomm
  have hP : pCore p G ≤ center G := (hA _ inferInstance hcomm).trans hZc
  have hF : fittingSubgroup G ≤ center G := by
    rwa [fitting_eq_pCore_of_abelian_normals_le_pgroup Z hZ hA]
  have hc : centralizer (fittingSubgroup G : Set G) = ⊤ := by
    apply top_unique
    intro x _ a ha
    exact (mem_center_iff.mp (hF ha) x).symm
  have htop : fittingSubgroup G = ⊤ := top_unique (hc ▸
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
  have hcent : center G = ⊤ := top_unique (htop ▸ hF)
  exact hn ⟨⟨fun a b => mem_center_iff.mp (hcent ▸ mem_top b) a⟩⟩

namespace Matrix.SL3.SplitMonomial
variable {F : Type*} [Field F] [Finite F]

/-- If every abelian normal subgroup of H is scalar, its three-core is
nonabelian as soon as H is nonabelian. -/
theorem pCore_three_nonabelian_of_not_hasNoncentralAbelianNormal
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
    (hs : Group.IsSolvable H) (hn : ¬ IsMulCommutative H)
    (hno : ¬ HasNoncentralAbelianNormal H) :
    ¬ IsMulCommutative (pCore 3 H) := by
  let Z := (center (Matrix.SpecialLinearGroup (Fin 3) F)).subgroupOf H
  have hZ : IsPGroup 3 Z :=
    (IsPGroup.of_card_dvd_pow (n := 1) (by simpa using card_center_dvd_three F)).comap_of_injective
      H.subtype H.subtype_injective
  have hA : ∀ A : Subgroup H, A.Normal → IsMulCommutative A → A ≤ Z := by
    intro A hAn hAc
    let := hAn
    let := hAc
    apply map_le_iff_le_comap.mp
    by_contra h
    apply hno
    refine ⟨A.map H.subtype, map_subtype_le A, ?_, inferInstance, h⟩
    change (comap H.subtype (A.map H.subtype)).Normal
    rw [comap_map_eq_self (by simp)]
    infer_instance
  have hZc : Z ≤ center H := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y.val)
  exact nonabelian_pCore_of_abelian_normals_le_central_pgroup Z hZ hZc hA hs hn

/-- Failure of a noncentral abelian normal subgroup supplies an actual
nonabelian three-subgroup normal relative to H. -/
theorem exists_nonabelian_normal_three_of_not_hasNoncentralAbelianNormal
    (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hs : Group.IsSolvable H) (hn : ¬ IsMulCommutative H)
    (hno : ¬ HasNoncentralAbelianNormal H) :
    ∃ Q : Subgroup (SpecialLinearGroup (Fin 3) F), Q ≤ H ∧
      (Q.subgroupOf H).Normal ∧ IsPGroup 3 Q ∧ ¬ IsMulCommutative Q := by
  let P := pCore 3 H
  let Q := P.map H.subtype
  have hnP := pCore_three_nonabelian_of_not_hasNoncentralAbelianNormal H hs hn hno
  refine ⟨Q, map_subtype_le P, ?_, pCore_isPGroup.map H.subtype, ?_⟩
  · change (comap H.subtype (P.map H.subtype)).Normal
    rw [comap_map_eq_self (by simp)]
    infer_instance
  · intro hc
    let := hc
    apply hnP
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Q => x.val)
      (mul_comm (⟨a.val.val, mem_map_of_mem H.subtype a.property⟩ : Q)
        ⟨b.val.val, mem_map_of_mem H.subtype b.property⟩)

/-- Reduce the solvable overgroup problem to excluding normalization of a
nonabelian three-subgroup by the full ambient Sylow two-subgroup. -/
theorem hasNoncentralAbelianNormal_of_normalizer_exclusion
    (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hs : Group.IsSolvable H) (hT : (T : Subgroup _) ≤ H)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hexclude : ∀ Q : Subgroup (SpecialLinearGroup (Fin 3) F),
      IsPGroup 3 Q → ¬ IsMulCommutative Q →
      ¬ (T : Subgroup _) ≤ normalizer (Q : Set (SpecialLinearGroup (Fin 3) F))) :
    HasNoncentralAbelianNormal H := by
  have hn : ¬ IsMulCommutative H := by
    intro hc
    let := hc
    obtain ⟨U, hUH, _, hUn⟩ := hU
    apply hUn
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact congrArg (fun x : H => x.val)
      (mul_comm (⟨a.val, hUH a.property⟩ : H) ⟨b.val, hUH b.property⟩)
  by_contra hno
  obtain ⟨Q, hQH, hQn, hQ, hQna⟩ :=
    exists_nonabelian_normal_three_of_not_hasNoncentralAbelianNormal H hs hn hno
  exact hexclude Q hQ hQna
    (hT.trans ((normal_subgroupOf_iff_le_normalizer hQH).mp hQn))

private theorem sixteen_dvd_gl_two_order {q : ℕ} (hq : Odd q) :
    16 ∣ (q ^ 2 - 1) * (q ^ 2 - q) := by
  have hodd := Nat.odd_iff.mp hq
  have hsquare := Nat.odd_iff.mp (show Odd (q ^ 2) from hq.pow)
  have he : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  have hm : q ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    rcases he with h | h | h | h <;> simp [h]
  have h8 : 8 ∣ q ^ 2 - 1 := by omega
  have h2 : 2 ∣ q ^ 2 - q := by omega
  exact Nat.mul_dvd_mul h8 h2

/-- Every Sylow two-subgroup of SL₃ over an odd finite field has order
divisible by sixteen. Only the actual GL₂ block embedding is needed. -/
theorem sixteen_dvd_card_sylow (hF : Odd (Nat.card F))
    (T : Sylow 2 (SpecialLinearGroup (Fin 3) F)) : 16 ∣ Nat.card T := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hgl : 16 ∣ Nat.card (GL (Fin 2) F) := by
    rw [Matrix.card_GL_field]
    simpa [Fin.prod_univ_two, ← Nat.card_eq_fintype_card] using sixteen_dvd_gl_two_order hF
  have hsl : 16 ∣ Nat.card (SpecialLinearGroup (Fin 3) F) :=
    hgl.trans (Subgroup.card_dvd_of_injective (blockEmbedding F) (blockEmbedding_injective F))
  exact T.pow_dvd_card_of_pow_dvd_card (n := 4) hsl

/-- A bound of eight for two-subgroups of nonabelian three-group normalizers
completes the solvable reduction. The bound is an explicit proof obligation. -/
theorem hasNoncentralAbelianNormal_of_normalizer_two_subgroup_bound
    (hF : Odd (Nat.card F))
    (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hs : Group.IsSolvable H) (hT : (T : Subgroup _) ≤ H)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hbound : ∀ Q : Subgroup (SpecialLinearGroup (Fin 3) F),
      IsPGroup 3 Q → ¬ IsMulCommutative Q →
      ∀ P : Subgroup (SpecialLinearGroup (Fin 3) F), IsPGroup 2 P →
      P ≤ normalizer (Q : Set (SpecialLinearGroup (Fin 3) F)) → Nat.card P ≤ 8) :
    HasNoncentralAbelianNormal H := by
  apply hasNoncentralAbelianNormal_of_normalizer_exclusion T H hs hT hU
  intro Q hQ hn hTQ
  have hsmall := hbound Q hQ hn T T.isPGroup' hTQ
  have hlarge := Nat.le_of_dvd (Nat.card_pos (α := T)) (sixteen_dvd_card_sylow hF T)
  omega

/-- A solvable subgroup of SL₃ over the source prime field that contains a
full ambient Sylow two-subgroup and a nonabelian three-subgroup has a
noncentral abelian subgroup normal relative to the solvable overgroup.
The supplied three-subgroup need not itself be normal. -/
theorem hasNoncentralAbelianNormal_of_solvable_sylow
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : 3 < p) (_hpmod : p % 3 = 1)
    (hF : Nat.card F = p) (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (SpecialLinearGroup (Fin 3) F)) (hs : Group.IsSolvable H)
    (hT : (T : Subgroup _) ≤ H)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    HasNoncentralAbelianNormal H := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply hasNoncentralAbelianNormal_of_normalizer_two_subgroup_bound
    (by simpa only [hF] using hpodd) T H hs hT hU
  intro Q hQ hn
  exact two_subgroup_card_le_eight_of_odd_weight_kernels p (ne_of_lt hp3) Q hQ hn
    (odd_card_weightCentralizer_normalizer (ne_of_lt hp3) Q hQ hn)

end Matrix.SL3.SplitMonomial
