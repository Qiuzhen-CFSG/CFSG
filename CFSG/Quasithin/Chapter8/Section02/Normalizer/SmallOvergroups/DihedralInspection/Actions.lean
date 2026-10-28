module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.FinCases

/-!
# Commuting actions in the dihedral branch of 8.2.8

The literal dihedral quotient makes O²(I)/O₂(O²(I)) cyclic. A perfect
normalizing component therefore acts trivially on that cyclic quotient.
Its commutators with X = O²(I) lie in O₂(X). Since P/U is abelian and
O₂(X) lies in P, the original K- and X-actions on P/U commute.

This supplies the group-theoretic input to scalar refinement of the actual
quotient action. It does not assume a T-action on X; in the code row such
normalization is excluded by 8.2.8(6).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
8.2.8(1), final paragraph on printed p.719 (PDF p.736).
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups

private def parity : DihedralGroup 5 →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (match g with | .r _ => 0 | .sr _ => 1)
  map_one' := rfl
  map_mul' a b := by cases a <;> cases b <;> decide +revert

private theorem parity_ker : parity.ker = zpowers (DihedralGroup.r 1 : DihedralGroup 5) := by
  ext x
  cases x with
  | r i =>
    constructor
    · intro _
      exact ⟨(i.val : ℤ), by simp [DihedralGroup.r_zpow]⟩
    · intro _; rfl
  | sr i =>
    constructor
    · intro h; change (1 : ZMod 2) = 0 at h; exact (one_ne_zero h).elim
    · rintro ⟨n, hn⟩
      simp [DihedralGroup.r_zpow] at hn

private theorem dihedral_residual_cyclic : IsCyclic (pResidual 2 (DihedralGroup 5)) := by
  have hP : IsPGroup 2 (Multiplicative (ZMod 2)) :=
    IsPGroup.of_card (p := 2) (n := 1) (by simp)
  have h := pResidual_le_ker_of_isPGroup 2 parity hP
  rw [parity_ker] at h
  exact Subgroup.isCyclic_of_le h

private theorem cyclic_core_quotient_of_cyclic_image
    {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hk : IsPGroup 2 f.ker) [IsCyclic f.range] : IsCyclic (A ⧸ pCore 2 A) := by
  have hle : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance, hk⟩
  let : IsCyclic (A ⧸ f.ker) :=
    (QuotientGroup.quotientKerEquivRange f).isCyclic.mpr inferInstance
  let g := QuotientGroup.map f.ker (pCore 2 A) (MonoidHom.id A) hle
  exact isCyclic_of_surjective g
    (QuotientGroup.map_surjective_of_surjective _ _ _ QuotientGroup.mk_surjective hle)

/-- The genuine dihedral quotient makes the residual quotient cyclic. -/
theorem dihedralResidualQuotient_isCyclic {G : Type*} [Group G] [Finite G]
    (e : (G ⧸ pCore 2 G) ≃* DihedralGroup 5) :
    IsCyclic (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  let g := f.comp (pResidual 2 G).subtype
  have hker : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hgker : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.ker.comap (pResidual 2 G).subtype)
    rw [hker]
    exact pCore_isPGroup.comap_subtype
  have hgr : g.range ≤ pResidual 2 (DihedralGroup 5) := by
    rw [MonoidHom.range_comp, range_subtype]
    exact map_pResidual_le 2 f
  let : IsCyclic (pResidual 2 (DihedralGroup 5)) := dihedral_residual_cyclic
  let : IsCyclic g.range := Subgroup.isCyclic_of_le hgr
  exact cyclic_core_quotient_of_cyclic_image g hgker

variable {G : Type*} [Group G]

/-- A perfect actor centralizes every cyclic two-core quotient. -/
theorem perfectActor_commutator_le_core (K X : Subgroup G) [Group.IsPerfect K]
    [IsCyclic (X ⧸ pCore 2 X)]
    (hKX : K ≤ normalizer (X : Set G)) :
    ⁅K, X⁆ ≤ X.pCoreIn 2 := by
  have hc : (X.pCoreIn 2).subgroupOf X = pCore 2 X := by
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => (Subtype.ext he : y = x) ▸ hy,
      fun hx => ⟨x, hx, rfl⟩⟩
  have hXP : X ≤ normalizer (X.pCoreIn 2 : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  let : ((X.pCoreIn 2).subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXP
  let : IsCyclic (X ⧸ (X.pCoreIn 2).subgroupOf X) :=
    (QuotientGroup.quotientMulEquivOfEq hc).isCyclic.mpr inferInstance
  let φ := sectionAction K X (X.pCoreIn 2) hKX
    (hKX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  let : CommGroup (MulAut (X ⧸ (X.pCoreIn 2).subgroupOf X)) :=
    (IsCyclic.mulAutMulEquiv _).toMonoidHom.commGroupOfInjective
      (IsCyclic.mulAutMulEquiv _).injective
  have hk (k : K) : k ∈ φ.ker :=
    Abelianization.commutator_subset_ker φ Group.IsPerfect.mem_commutator
  apply commutator_le.mpr
  intro k hkK x hx
  exact (mem_sectionAction_ker K X (X.pCoreIn 2) _ _ ⟨k, hkK⟩).mp (hk ⟨k, hkK⟩) ⟨x, hx⟩

/-- Actions on an abelian section commute when actor commutators lie in its numerator. -/
theorem sectionAction_commute_of_commutator_le (K X P U : Subgroup G) [(U.subgroupOf P).Normal]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hXP : X ≤ normalizer (P : Set G)) (hXU : X ≤ normalizer (U : Set G))
    (hKX : ⁅K, X⁆ ≤ P) (hPP : ⁅P, P⁆ ≤ U)
    (k : K) (x : X) :
    Commute (sectionAction K P U hKP hKU k) (sectionAction X P U hXP hXU x) := by
  let D := normalizer (P : Set G) ⊓ normalizer (U : Set G)
  let kd : D := ⟨k, hKP k.property, hKU k.property⟩
  let xd : D := ⟨x, hXP x.property, hXU x.property⟩
  let φ := sectionAction D P U inf_le_left inf_le_right
  have hh : ⁅kd, xd⁆ ∈ φ.ker := by
    apply (mem_sectionAction_ker D P U _ _ _).mpr
    intro p
    exact hPP (commutator_mem_commutator
      (hKX (commutator_mem_commutator k.property x.property)) p.property)
  have he : Commute (φ kd) (φ xd) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact hh
  exact he

/-- Transport cyclicity to the embedded residual used throughout the source argument. -/
theorem embedded_dihedralResidualQuotient_isCyclic [Finite G] (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* DihedralGroup 5) :
    IsCyclic ((pResidual 2 I).map I.subtype ⧸
      pCore 2 ((pResidual 2 I).map I.subtype)) := by
  let f := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let q := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  let : IsCyclic (pResidual 2 I ⧸ pCore 2 (pResidual 2 I)) :=
    dihedralResidualQuotient_isCyclic e
  exact q.isCyclic.mp inferInstance

/-- The containing component centralizes the dihedral residual modulo its two-core. -/
theorem component_twoResidual_commutator_le_core [Finite G]
    (K I : Subgroup G) [Group.IsPerfect K]
    (e : (I ⧸ pCore 2 I) ≃* DihedralGroup 5)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) :
    ⁅K, (pResidual 2 I).map I.subtype⁆ ≤
      ((pResidual 2 I).map I.subtype).pCoreIn 2 := by
  let : IsCyclic ((pResidual 2 I).map I.subtype ⧸
      pCore 2 ((pResidual 2 I).map I.subtype)) :=
    embedded_dihedralResidualQuotient_isCyclic I e
  exact perfectActor_commutator_le_core K _
    (component_normalizes_twoResidual K I hQI hKI)

/-- The original residual action on the literal P/U, with no choice of coordinates. -/
@[expose] def pairResidualQuotientAction (I U : Subgroup G)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    (hIC : I ≤ centralizer (U : Set G)) :
    (pResidual 2 I).map I.subtype →*
      MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) :=
  sectionAction _ _ _
    ((map_subtype_le _).trans (I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
    ((map_subtype_le _).trans (hIC.trans (centralizer_le_normalizer _)))

/-- The actual K- and X-actions on P/U commute, using the genuine D₁₀ quotient
and the abelianness of P/U. These are the operators needed for the F₁₆ refinement. -/
theorem componentCoreQuotientAction_commute [Finite G] (K I U : Subgroup G)
    [Group.IsPerfect K] [(U.subgroupOf (I.pCoreIn 2)).Normal]
    (e : (I ⧸ pCore 2 I) ≃* DihedralGroup 5)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hIC : I ≤ centralizer (U : Set G))
    (hPP : ⁅I.pCoreIn 2, I.pCoreIn 2⁆ ≤ U)
    (k : K) (x : (pResidual 2 I).map I.subtype) :
    Commute (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k)
      (pairResidualQuotientAction I U hIC x) := by
  apply sectionAction_commute_of_commutator_le K _ _ _ _ _ _ _ ?_ hPP
  exact (component_twoResidual_commutator_le_core K I e hQI hKI).trans
    (le_sup_left.trans (twoResidual_core_sup_eq I U hUP hfull).le)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
