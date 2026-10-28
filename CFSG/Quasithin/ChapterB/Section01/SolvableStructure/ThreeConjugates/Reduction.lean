module

public import Theory.Representation.BinaryOffender.Stability
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableNormalSup

/-!
# The local group and quotient in the cyclic-three argument

For `H = K ⊔ T`, the subgroup `K₀ = ⟨Kᵀ⟩` is normal in `H` and
`H = K₀ T`. If `K` has order three and is subnormal inside `H`, then `K₀`
is a three-group. The two-group supplement implies both `K₀ = O₃(H)` and
`K₀ = O²(H)`, and makes `H` solvable. All cores and residuals are computed
inside `H` and mapped into the original ambient group.

The best offenders in `T` generate a subgroup normalized by `T`. Consequently
`M = J(T,V) K₀` is normal in `H`. Subnormal monotonicity of the two-core
identifies the kernel of `M → H/O₂(H)` with the intrinsic `O₂(M)`, giving
an explicit first-isomorphism equivalence compatible with quotient maps.

These reductions do not assert the direct-product conclusions of B.1.12.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
open Subgroup Representation.BinaryOffender
open scoped Pointwise
variable {G : Type*} [Group G]

def conjugateFamily (K T : Subgroup G) : Set (Subgroup G) :=
  Set.range fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom

def conjugateClosure (K T : Subgroup G) : Subgroup G :=
  ⨆ t : T, K.map (MulAut.conj (t : G)).toMonoidHom

theorem le_conjugateClosure (K T : Subgroup G) : K ≤ conjugateClosure K T :=
  le_iSup_conjugates K T

theorem conjugateClosure_le_sup (K T : Subgroup G) : conjugateClosure K T ≤ K ⊔ T :=
  iSup_conjugates_le_sup K T

theorem le_normalizer_conjugateClosure (K T : Subgroup G) :
    T ≤ normalizer (conjugateClosure K T) := le_normalizer_iSup_conjugates K T

theorem conjugateClosure_normal (K T : Subgroup G) :
    ((conjugateClosure K T).subgroupOf (K ⊔ T)).Normal :=
  normal_iSup_conjugates_subgroupOf_sup K T

theorem conjugateClosure_sup (K T : Subgroup G) : conjugateClosure K T ⊔ T = K ⊔ T :=
  le_antisymm (sup_le (conjugateClosure_le_sup K T) le_sup_right)
    (sup_le ((le_conjugateClosure K T).trans le_sup_left) le_sup_right)

theorem sup_product (K T : Subgroup G) :
    (↑(K ⊔ T) : Set G) = (conjugateClosure K T : Set G) * (T : Set G) := by
  rw [← conjugateClosure_sup K T]
  exact coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_conjugateClosure K T)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

def localOffenderSubgroup (T : Subgroup G) : Subgroup G :=
  generatedBy {A | IsBestOffender ρ A} T

theorem localOffenderSubgroup_le (T : Subgroup G) : localOffenderSubgroup ρ T ≤ T :=
  iSup_le fun _ => iSup_le fun h => h.2

theorem le_normalizer_localOffenderSubgroup (T : Subgroup G) :
    T ≤ normalizer (localOffenderSubgroup ρ T) := by
  apply le_normalizer_iff.mpr
  intro t ht a ha
  have hm : (localOffenderSubgroup ρ T).map (MulAut.conj t).toMonoidHom ≤
      localOffenderSubgroup ρ T := by
    unfold localOffenderSubgroup generatedBy
    simp only [Subgroup.map_iSup]
    refine iSup_le fun A => iSup_le fun hA => ?_
    have hAT : A.map (MulAut.conj t).toMonoidHom ≤ T := by
      rintro x ⟨y, hy, rfl⟩
      exact T.mul_mem (T.mul_mem ht (hA.2 hy)) (T.inv_mem ht)
    exact le_iSup_of_le (A.map (MulAut.conj t).toMonoidHom)
      (le_iSup_of_le ⟨hA.1.map_conj ρ t, hAT⟩ le_rfl)
  exact hm (mem_map_of_mem _ ha)

def mixedSubgroup (K T : Subgroup G) : Subgroup G :=
  localOffenderSubgroup ρ T ⊔ conjugateClosure K T

theorem mixedSubgroup_le (K T : Subgroup G) : mixedSubgroup ρ K T ≤ K ⊔ T :=
  sup_le ((localOffenderSubgroup_le ρ T).trans le_sup_right)
    (conjugateClosure_le_sup K T)

theorem mixedSubgroup_product (K T : Subgroup G) :
    (mixedSubgroup ρ K T : Set G) =
      (localOffenderSubgroup ρ T : Set G) * (conjugateClosure K T : Set G) :=
  coe_mul_of_left_le_normalizer_right _ _
    ((localOffenderSubgroup_le ρ T).trans (le_normalizer_conjugateClosure K T))

theorem le_normalizer_mixedSubgroup (K T : Subgroup G) :
    K ⊔ T ≤ normalizer (mixedSubgroup ρ K T) := by
  rw [← conjugateClosure_sup K T]
  apply sup_le
  · exact (show conjugateClosure K T ≤ mixedSubgroup ρ K T from le_sup_right).trans
      (mixedSubgroup ρ K T).le_normalizer
  · exact (le_inf (le_normalizer_localOffenderSubgroup ρ T)
      (le_normalizer_conjugateClosure K T)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem mixedSubgroup_normal (K T : Subgroup G) :
    ((mixedSubgroup ρ K T).subgroupOf (K ⊔ T)).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_mixedSubgroup ρ K T)

section Finite
variable [Finite G]

/-- Relative subnormality puts the entire conjugate closure in the relative three-core. -/
theorem conjugateClosure_le_threeCore (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3) :
    conjugateClosure K T ≤ (pCore 3 (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype := by
  have hthree : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hle := isPGroup_le_pCoreAmbient_of_isSubnormalIn (K ⊔ T) K 3 le_sup_left hK hthree
  apply iSup_conjugates_le_of_le_normalizer K T _ hle
  apply le_normalizer_iff.mpr
  intro t ht x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let tH : (K ⊔ T : Subgroup G) := ⟨t, (show T ≤ K ⊔ T from le_sup_right) ht⟩
  exact ⟨tH * y * tH⁻¹, (pCore_normal (p := 3)).conj_mem y hy tH, rfl⟩

theorem conjugateClosure_isThreeGroup (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3) :
    IsPGroup 3 (conjugateClosure K T) :=
  (pCore_isPGroup.map (K ⊔ T).subtype).to_le
    (conjugateClosure_le_threeCore K T hK hcard)

omit [Finite G] in
/-- The local group is generated by its normal conjugate closure and its two-subgroup. -/
theorem internal_sup (K T : Subgroup G) :
    (conjugateClosure K T).subgroupOf (K ⊔ T) ⊔ T.subgroupOf (K ⊔ T) = ⊤ := by
  rw [← subgroupOf_sup (conjugateClosure_le_sup K T) le_sup_right,
    conjugateClosure_sup, subgroupOf_self]

omit [Finite G] in
theorem quotient_conjugateClosure_isTwoGroup (K T : Subgroup G) (hT : IsPGroup 2 T) :
    let := conjugateClosure_normal K T
    IsPGroup 2 ((K ⊔ T : Subgroup G) ⧸ (conjugateClosure K T).subgroupOf (K ⊔ T)) := by
  let := conjugateClosure_normal K T
  exact isPGroup_quotient_of_sup_eq_top _ _ hT.comap_subtype (internal_sup K T)

/-- Subnormality is relative to the join, not to the ambient group. -/
theorem local_solvable (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) : Group.IsSolvable (K ⊔ T : Subgroup G) := by
  let := conjugateClosure_normal K T
  let : Group.IsNilpotent ((conjugateClosure K T).subgroupOf (K ⊔ T)) :=
    (conjugateClosure_isThreeGroup K T hK hcard).comap_subtype.isNilpotent
  let : Group.IsNilpotent (T.subgroupOf (K ⊔ T)) := hT.comap_subtype.isNilpotent
  exact Group.isSolvable_of_normal_sup_eq_top _ _ (internal_sup K T)

/-- The three-core equality uses the fact that the remaining quotient is a two-group. -/
theorem conjugateClosure_eq_threeCore (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    conjugateClosure K T = (pCore 3 (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype := by
  apply le_antisymm (conjugateClosure_le_threeCore K T hK hcard)
  let N := (conjugateClosure K T).subgroupOf (K ⊔ T)
  let : N.Normal := conjugateClosure_normal K T
  let q := QuotientGroup.mk' N
  have hq := quotient_conjugateClosure_isTwoGroup K T hT
  have hb : (pCore 3 (K ⊔ T : Subgroup G)).map q = ⊥ :=
    disjoint_self.mp ((pCore_isPGroup.map q).disjoint_of_coprime
      (hq.to_subgroup _) (by decide : Nat.Coprime 3 2))
  rintro x ⟨y, hy, rfl⟩
  apply (QuotientGroup.eq_one_iff (N := N) y).mp
  exact mem_bot.mp (hb ▸ mem_map_of_mem q hy)

/-- Here the superscript in O² means the two-residual, not the two-core. -/
theorem conjugateClosure_eq_twoResidual (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    conjugateClosure K T = (pResidual 2 (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype := by
  let N := (conjugateClosure K T).subgroupOf (K ⊔ T)
  let : N.Normal := conjugateClosure_normal K T
  have hthree : IsPGroup 3 N := (conjugateClosure_isThreeGroup K T hK hcard).comap_subtype
  have he : pResidual 2 (K ⊔ T : Subgroup G) = N := by
    apply le_antisymm
    · exact sInf_le ⟨inferInstance, quotient_conjugateClosure_isTwoGroup K T hT⟩
    · intro x hx
      apply mem_pResidual_of_orderOf_coprime
      have hc := (hthree.orderOf_coprime (by decide : Nat.Coprime 3 2) ⟨x, hx⟩).symm
      simpa only [Subgroup.orderOf_mk] using hc
  rw [he]
  exact (map_subgroupOf_eq_of_le (conjugateClosure_le_sup K T)).symm

/-- The two-core of M is the pullback of the two-core of H along the inclusion. -/
theorem mixed_twoCore_eq_comap (K T : Subgroup G) :
    pCore 2 (mixedSubgroup ρ K T) =
      (pCore 2 (K ⊔ T : Subgroup G)).comap (inclusion (mixedSubgroup_le ρ K T)) := by
  apply le_antisymm
  · have hm := pCoreAmbient_mono_of_isSubnormalIn (mixedSubgroup ρ K T) (K ⊔ T) 2
      (mixedSubgroup_le ρ K T) (mixedSubgroup_normal ρ K T).isSubnormal
    intro x hx
    obtain ⟨y, hy, he⟩ := hm (mem_map_of_mem (mixedSubgroup ρ K T).subtype hx)
    change inclusion (mixedSubgroup_le ρ K T) x ∈ pCore 2 (K ⊔ T : Subgroup G)
    have he' : inclusion (mixedSubgroup_le ρ K T) x = y := Subtype.ext he.symm
    rwa [he']
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective _
      (inclusion_injective (mixedSubgroup_le ρ K T))⟩

/-- The actual map from M to H/O₂(H). -/
def mixedQuotientMap (K T : Subgroup G) :
    mixedSubgroup ρ K T →* ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)) :=
  (QuotientGroup.mk' (pCore 2 (K ⊔ T : Subgroup G))).comp
    (inclusion (mixedSubgroup_le ρ K T))

/-- This kernel is the intrinsic two-core of M. -/
theorem mixedQuotientMap_ker (K T : Subgroup G) :
    (mixedQuotientMap ρ K T).ker = pCore 2 (mixedSubgroup ρ K T) := by
  rw [mixed_twoCore_eq_comap ρ K T]
  ext x
  exact QuotientGroup.eq_one_iff (N := pCore 2 (K ⊔ T : Subgroup G)) _

/-- A concrete first-isomorphism equivalence, with domain M/O₂(M). -/
noncomputable def mixedQuotientEquiv (K T : Subgroup G) :
    (mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T)) ≃*
      (mixedQuotientMap ρ K T).range :=
  (QuotientGroup.quotientMulEquivOfEq (mixedQuotientMap_ker ρ K T).symm).trans
    (QuotientGroup.quotientKerEquivRange (mixedQuotientMap ρ K T))

theorem mixedQuotientEquiv_mk (K T : Subgroup G) (x : mixedSubgroup ρ K T) :
    (mixedQuotientEquiv ρ K T (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) x) :
      (K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)) = mixedQuotientMap ρ K T x := by
  simp [mixedQuotientEquiv, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivRange]
  rfl

end Finite
end CFSG.Quasithin.ChapterB.ThreeConjugates
