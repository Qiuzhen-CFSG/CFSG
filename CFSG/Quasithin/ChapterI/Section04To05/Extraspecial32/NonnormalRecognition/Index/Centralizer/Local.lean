module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction
public import Theory.GroupTheory.UniqueFixedCosetFusion
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The local intersection of the second involution centralizer

The marked A₈ subgroup controls its two ambient involution classes. Its full
centralizer of z therefore gives a unique fixed coset. The normalizer condition
in a finite two-group puts a Sylow two-subgroup of K = C_G(t) inside L. Hence
K ∩ L has odd index in K, every involution of K is K-conjugate into L, and
the two-residual J supplements K ∩ L. In particular K ⊈ L implies J ⊈ L.

All subgroup maps are literal inclusions. The marked i = (45)(67) satisfies
i*t=z, which bounds C_J(i) by J ∩ L. Identifying this intersection by transfer
and recognizing J remain separate steps.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, using the unique-fixed-point arguments of *Sporadic Groups* 7.3–7.4.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup Equiv Equiv.Perm

/-- The second double transposition, on the last four of the eight points. -/
def i8 : Eight := ⟨swap 4 5 * swap 6 7, by simp [mem_alternatingGroup, map_mul]⟩

theorem i8_order : orderOf i8 = 2 := orderOf_eq_prime (by decide) (by decide)
theorem i8_mul_t8 : i8 * t8 = z8 := by decide
theorem z8_commutes_t8 : Commute z8 t8 := by change z8 * t8 = t8 * z8; decide

namespace InvolutionData
variable {G : Type*} [Group G] {z : G} {L : Subgroup G} (d : InvolutionData z L)

/-- The literal subgroup K ∩ L, viewed inside K. -/
abbrev M : Subgroup d.K := L.subgroupOf d.K

/-- The marked involution `(45)(67)` inside L. -/
def i : L := d.equiv.symm i8

theorem i_order : orderOf d.i = 2 := (d.equiv.symm.orderOf_eq i8).trans i8_order

theorem i_mul_t : (d.i : G) * d.t = z := by
  have he : d.i * d.t = (⟨z, d.z_mem⟩ : L) := by
    apply d.equiv.injective
    simpa only [map_mul, i, t, d.equiv.apply_symm_apply, d.z_image] using i8_mul_t8
  exact congrArg Subtype.val he

theorem z_mem_K : z ∈ d.K := by
  apply mem_centralizer_singleton_iff.mpr
  have he : (⟨z, d.z_mem⟩ : L) * d.t = d.t * ⟨z, d.z_mem⟩ := by
    apply d.equiv.injective
    simpa only [map_mul, d.z_image, t, d.equiv.apply_symm_apply] using z8_commutes_t8.eq
  exact congrArg Subtype.val he

include d in
/-- Fusion control in L and the full centralizer bound give the source's
unique fixed point, without assuming a permutation action on nine points. -/
theorem unique_fixed_coset (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    ∃! q : G ⧸ L, z • q = q := by
  apply UniqueFixedCoset.unique_of_fusion_and_centralizer d.z_mem hCL
  intro g hg
  have hc : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨a, ha⟩ := isConj_iff.mp ((d.controls_z hz ⟨_, hg⟩).mpr hc)
  exact ⟨a, a.property, (congrArg Subtype.val ha).symm⟩

variable [Finite G]

/-- A Sylow two-subgroup of K containing z lies in L by unique fixation.
This is the odd-index step of the second-centralizer argument. -/
theorem exists_sylow_K_le_M (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    ∃ T : Sylow 2 d.K, (T : Subgroup d.K) ≤ d.M := by
  let zk : d.K := ⟨z, d.z_mem_K⟩
  have hzord : orderOf zk = 2 := (Subgroup.orderOf_coe zk).symm.trans hz
  have hp : IsPGroup 2 (zpowers zk) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hzord, pow_one])
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hzT : z ∈ (T : Subgroup d.K).map d.K.subtype :=
    mem_map.mpr ⟨zk, hT (mem_zpowers zk), rfl⟩
  have hTL := (UniqueFixedCoset.p_overgroup_and_normalizer_le d.z_mem
    (d.unique_fixed_coset hz hCL) (T.isPGroup'.map d.K.subtype) hzT).1
  exact ⟨T, fun a ha => hTL (mem_map.mpr ⟨a, ha, rfl⟩)⟩

theorem local_index_odd (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    Odd d.M.index := by
  obtain ⟨T, hT⟩ := d.exists_sylow_K_le_M hz hCL
  exact Nat.not_even_iff_odd.mp (fun he =>
    T.not_dvd_index ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hT)))

/-- Every involution of K can be moved into its actual intersection with L
by a conjugator in K. -/
theorem involution_conjugate_into_M (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (a : d.K) (ha : orderOf a = 2) :
    ∃ k : d.K, k * a * k⁻¹ ∈ d.M := by
  obtain ⟨T, hT⟩ := d.exists_sylow_K_le_M hz hCL
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨U, hU⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq d.K U T
  refine ⟨k, hT ?_⟩
  rw [← hk]
  exact ⟨a, hU (mem_zpowers a), rfl⟩

omit [Finite G] in
theorem J_le_K : d.J ≤ d.K := map_subtype_le _

omit [Finite G] in
theorem X_le_L : d.X ≤ L := map_subtype_le _

omit [Finite G] in
/-- The two successive inclusions in X agree with the literal inclusion into K. -/
theorem X_le_J : d.X ≤ d.J := by
  let C : Subgroup L := centralizer ({d.t} : Set L)
  let f : C →* d.K :=
    { toFun := fun a => ⟨(a : L), by
        apply mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
  exact mem_map.mpr ⟨f b, map_pResidual_le 2 f (mem_map.mpr ⟨b, hb, rfl⟩), rfl⟩

theorem J_twoPerfect : IsPPerfect 2 d.J := isPPerfect_embedded_pResidual 2 d.K

/-- K is generated by its two-residual and K ∩ L. -/
theorem residual_sup_local (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    d.J ⊔ (d.K ⊓ L) = d.K := by
  obtain ⟨T, hT⟩ := d.exists_sylow_K_le_M hz hCL
  have hs : pResidual 2 d.K ⊔ d.M = ⊤ :=
    top_unique ((pResidual_sup_sylow_eq_top T).ge.trans (sup_le_sup_left hT _))
  have he := congrArg (fun U : Subgroup d.K => U.map d.K.subtype) hs
  simpa only [J, Subgroup.map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype,
    inf_comm] using he

theorem J_not_le (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (hK : ¬ d.K ≤ L) :
    ¬ d.J ≤ L := by
  intro hJ
  exact hK ((d.residual_sup_local hz hCL).ge.trans (sup_le hJ inf_le_right))

omit [Finite G] in
/-- Since i*t=z and J centralizes t, centralizing i in J forces membership
in L. This is the source's key centralizer bound before transfer identifies J ∩ L. -/
theorem J_centralizer_i_le_local (hCL : Centralizer z ≤ L) :
    d.J ⊓ Centralizer (d.i : G) ≤ d.J ⊓ L := by
  intro a ha
  refine ⟨ha.1, hCL ?_⟩
  apply mem_centralizer_singleton_iff.mpr
  have hi : Commute a (d.i : G) := mem_centralizer_singleton_iff.mp ha.2
  have ht : Commute a (d.t : G) := mem_centralizer_singleton_iff.mp (d.J_le_K ha.1)
  simpa only [d.i_mul_t] using (hi.mul_right ht).eq

omit [Finite G] in
theorem J_centralizer_i_le_X (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) : d.J ⊓ Centralizer (d.i : G) ≤ d.X :=
  (d.J_centralizer_i_le_local hCL).trans_eq htransfer

end InvolutionData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
end
