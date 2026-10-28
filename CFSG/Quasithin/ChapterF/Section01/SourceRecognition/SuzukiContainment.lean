module
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import Theory.SpecificGroups.Suzuki.SylowSupplement
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.ReeFour
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Suzuki containment reductions for F.1.12

The nondegenerate Suzuki outer automorphism group has odd order. Hence an
ambient Sylow normalizing R factors as O₂(RT)(T ∩ R), and its normality in
T N_R(T ∩ R) is automatic. Containment in R is equivalent to equality of
the two embedded cores. Failure of containment produces a specific element
of O₂(RT) outside R in the kernel of the literal action on R/O₂(R).

For the recognition endpoint, an isomorphism of the Suzuki-side parabolic
with a Ree parabolic suffices; no marking of the original R is needed.
Every two-element of a nonbinary Ree parabolic belongs to its perfect
O^{2′} subgroup, hence to its solvable residual. The source F.1.1 factor
contains that residual. The binary Suzuki-side parabolic is solvable, so
the nondegenerate Suzuki quotient excludes that parameter automatically.

These are reductions and a conditional recognition endpoint. Constructing
the parabolic isomorphism from the linear–Suzuki source pair remains open;
no recognition or comparison with DGS85 Hypothesis A is asserted here.

Source: Aschbacher–Smith, F.1.10 and F.1.12, printed pp.262–264,
especially the core equality and containment argument on p.264. The
application is 5.1.16(2), printed pp.639–640, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.SuzukiContainment

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {R : Subgroup G}

/-- The Suzuki outer-action calculation on the literal join R T. -/
private theorem sylow_factorization
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (T : Subgroup G) = twoCore (R ⊔ (T : Subgroup G)) ⊔ ((T : Subgroup G) ⊓ R) :=
  BenderSuzuki.MatrixGroups.suzuki_quotient_sylow_factorization R T hn (by omega) e

/-- The source normality premise follows already from the Suzuki quotient. -/
theorem sylow_normal_in_borel_join
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ((T : Subgroup G).subgroupOf
      ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal :=
  normal_of_core_decomposition R (T : Subgroup G) (sylow_factorization hn hm e)

/-- Only the placement of the extended two-core remains after the Suzuki factorization. -/
theorem sylow_le_iff_join_core_le
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (T : Subgroup G) ≤ R ↔ twoCore (R ⊔ (T : Subgroup G)) ≤ R := by
  constructor
  · intro h
    rw [sup_eq_left.mpr h]
    exact map_subtype_le _
  · intro h
    rw [sylow_factorization hn hm e]
    exact sup_le h inf_le_right

/-- The p.264 core equality is exactly the remaining containment condition. -/
theorem sylow_le_iff_join_core_eq
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (T : Subgroup G) ≤ R ↔ twoCore (R ⊔ (T : Subgroup G)) = twoCore R := by
  constructor
  · intro h
    rw [sup_eq_left.mpr h]
  · intro h
    apply (sylow_le_iff_join_core_le hn hm e).mpr
    rw [h]
    exact map_subtype_le _

/-- Noncontainment gives an original Sylow element in the extended core, outside R,
acting trivially on the original quotient R/O₂(R). -/
theorem escaping_core_element
    (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hout : ¬ (T : Subgroup G) ≤ R) :
    ∃ x : (R ⊔ (T : Subgroup G) : Subgroup G),
      x ∈ pCore 2 (R ⊔ (T : Subgroup G) : Subgroup G) ∧
      (x : G) ∈ (T : Subgroup G) ∧ (x : G) ∉ R ∧
      pCoreJoinAction 2 hn x = 1 := by
  have hnot : ¬ twoCore (R ⊔ (T : Subgroup G)) ≤ R :=
    fun h => hout ((sylow_le_iff_join_core_le hn hm e).mpr h)
  obtain ⟨x, hx, hxR⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨y, hy, rfl⟩ := hx
  have hc : twoCore (R ⊔ (T : Subgroup G)) ≤ (T : Subgroup G) :=
    le_sup_left.trans_eq (sylow_factorization hn hm e).symm
  exact ⟨y, hy, hc (mem_map_of_mem _ hy), hxR,
    pCore_le_pCoreJoinAction_kernel 2 hn hy⟩

open ReeF4.LargeLocalSeeds

/-- Every two-element of either nonbinary Ree parabolic lies in its solvable residual. -/
private theorem ree_two_element_mem_residual {m : ℕ} (hm : 1 ≤ m) (s : Side)
    (x : ReeF4.Parabolics.parabolic m s) (k : ℕ) (hx : x ^ (2 ^ k) = 1) :
    x ∈ solvableResidual (ReeF4.Parabolics.parabolic m s) := by
  let := ReeF4.Parabolics.OuterLocal.localFactor_perfect hm s
  have hxL : (x : ReeF4.Model m) ∈ ReeF4.Parabolics.localFactor m s :=
    ReeF4.Parabolics.mem_localFactor_of_pow m s x x.property k
      (congrArg Subtype.val hx)
  have hr := le_map_solvableResidual_of_isPerfect
    (ReeF4.Parabolics.localFactor m s) (ReeF4.Parabolics.parabolic m s)
    (ReeF4.Parabolics.localFactor_le_parabolic m s) hxL
  obtain ⟨y, hy, hyx⟩ := hr
  exact (Subtype.ext hyx : y = x) ▸ hy

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

omit [Finite G] in
/-- An actual Ree parabolic isomorphism suffices for source containment.
The original local factor is retained through its intrinsic residual containment. -/
theorem sylow_le_local_of_ree_parabolic
    (h : HypothesisF11 L S) (i : Fin 2) {m : ℕ} (hm : 1 ≤ m) (s : Side)
    (e : parabolic L S i ≃* ReeF4.Parabolics.parabolic m s) : S ≤ L i := by
  intro x hx
  let p : parabolic L S i :=
    ⟨x, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) hx⟩
  obtain ⟨k, hk⟩ := h.S_isP ⟨x, hx⟩
  have hkG : x ^ (2 ^ k) = 1 := congrArg (fun z : S => (z : G)) hk
  have hp : p ^ (2 ^ k) = 1 := Subtype.ext hkG
  have he : e p ^ (2 ^ k) = 1 := by rw [← map_pow, hp, map_one]
  have hr := ree_two_element_mem_residual hm s (e p) k he
  have hr' : p ∈ solvableResidual (parabolic L S i) := by
    have ht := map_solvableResidual_le e.symm.toMonoidHom (mem_map_of_mem _ hr)
    change e.symm (e p) ∈ solvableResidual (parabolic L S i) at ht
    simpa only [e.symm_apply_apply] using ht
  exact h.parabolic_residual_le_local i (mem_map_of_mem _ hr')

/-- The binary Suzuki-side parabolic is solvable, including its full two-core. -/
private theorem binary_ree_suzuki_parabolic_solvable :
    Group.IsSolvable (ReeF4.Parabolics.parabolic 0 .suzuki) := by
  rw [← GreenBook.LieModels.ReeFour.binary_localFactor .suzuki]
  let A := ReeF4.Parabolics.localFactor 0 .suzuki
  let := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
  let e := ReeF4.Parabolics.suzukiLocalQuotientEquiv 0
  let : Group.IsSolvable (A ⧸ pCore 2 A) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr
    ⟨inferInstance, inferInstance⟩

omit [Finite G] in
/-- A nondegenerate source Suzuki quotient rules out the binary Ree parabolic. -/
theorem ree_parameter_positive_of_suzuki_quotient
    (h : HypothesisF11 L S) (i : Fin 2) {m k : ℕ} (hm : 1 ≤ m)
    (f : (L i ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (e : parabolic L S i ≃* ReeF4.Parabolics.parabolic k .suzuki) : 1 ≤ k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst k
  let := binary_ree_suzuki_parabolic_solvable
  have hP : Group.IsSolvable (parabolic L S i) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let := (h.parabolic_solvable_iff_local_quotient i).mp hP
  exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m (by omega)
    (Group.isSolvable_of_isSolvable_injective (f := f.symm.toMonoidHom) f.symm.injective)

omit [Finite G] in
/-- The Suzuki containment consequence conditional on an actual parabolic
isomorphism. Its existence, rather than parameter or subgroup marking, remains to prove. -/
theorem sylow_le_suzuki_of_ree_parabolic
    (h : HypothesisF11 L S) (i : Fin 2) {m k : ℕ} (hm : 1 ≤ m)
    (f : (L i ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (e : parabolic L S i ≃* ReeF4.Parabolics.parabolic k .suzuki) : S ≤ L i :=
  sylow_le_local_of_ree_parabolic h i
    (ree_parameter_positive_of_suzuki_quotient h i hm f e) .suzuki e

end CFSG.Quasithin.ChapterF.Source.SuzukiContainment
