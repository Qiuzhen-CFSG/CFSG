module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# The containing component's action on O²(I) and O₂(I)/U

The normalizing two-core Q = O₂(K_U) does not change the embedded residual:
O²(IQ) = O²(I). The bound [K_U,I] ≤ Q makes IQ invariant under K_U, so its
characteristic residual X is invariant. The source equality P = [P,X]U
identifies P with O₂(X)U, giving the action on P as well. Conjugation then
defines an action on the literal quotient P/U with its exact kernel.

These are the structural steps preceding the F₁₆ multiplicity-space
inspection. The construction and classification of that representation
remain separate obligations. In particular no T-action on X or on a
multiplicity space is assumed: source 8.2.8(6) excludes T-normalization of
X in the code branch. The simultaneous marked action on U must be retained
in any remaining overgroup argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Proposition 8.2.8(1), final paragraph on printed p.719 (PDF p.736).
The input P = [P,O²(I)]U appears in the setup on printed p.717.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

/-- Adjoining a normalizing two-subgroup does not change the embedded two-residual. -/
theorem residual_adjoin_twoGroup [Finite G] (I Q : Subgroup G)
    (hQ : IsPGroup 2 Q) (hQI : Q ≤ normalizer (I : Set G)) :
    (pResidual 2 (I ⊔ Q : Subgroup G)).map (I ⊔ Q).subtype =
      (pResidual 2 I).map I.subtype := by
  let D := I ⊔ Q
  have hID : I ≤ D := le_sup_left
  let : (I.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hQI)
  have hgen : I.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup hID (show Q ≤ D from le_sup_right)]
    exact subgroupOf_self D
  have hp := isPGroup_quotient_of_sup_eq_top (I.subgroupOf D) (Q.subgroupOf D)
    hQ.comap_subtype hgen
  have hr : pResidual 2 D ≤ I.subgroupOf D := sInf_le ⟨inferInstance, hp⟩
  have hRI : (pResidual 2 D).map D.subtype ≤ I := by
    simpa only [map_subgroupOf_eq_of_le hID] using map_mono (f := D.subtype) hr
  apply le_antisymm ?_ (embedded_pResidual_mono 2 hID)
  have hm := embedded_pResidual_mono 2 hRI
  rw [(pResidual_eq_top_iff 2 _).mpr (isPPerfect_embedded_pResidual 2 D),
    ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- A commutator bound modulo an invariant subgroup makes the join invariant. -/
theorem normalizes_join_of_commutator (K I Q : Subgroup G)
    (hKQ : K ≤ normalizer (Q : Set G)) (hKI : ⁅K, I⁆ ≤ Q) :
    K ≤ normalizer ((I ⊔ Q : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hi : I.map (MulAut.conj k).toMonoidHom ≤ I ⊔ Q := by
    rintro _ ⟨i, hi, rfl⟩
    have hm := (I ⊔ Q).mul_mem (mem_sup_right (hKI (commutator_mem_commutator hk hi)))
      (mem_sup_left hi)
    change k * i * k⁻¹ ∈ _
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
  have hq : Q.map (MulAut.conj k).toMonoidHom ≤ I ⊔ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_sup_right ((mem_normalizer_iff.mp (hKQ hk) q).mp hq)
  have hm : (I ⊔ Q).map (MulAut.conj k).toMonoidHom ≤ I ⊔ Q := by
    rw [Subgroup.map_sup]
    exact sup_le hi hq
  exact hm (mem_map_of_mem _ hx)

/-- The containing component acts on the actual X = O²(I), using its two-core action on I. -/
theorem component_normalizes_twoResidual [Finite G] (K I : Subgroup G)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) :
    K ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) := by
  rw [← residual_adjoin_twoGroup I (K.pCoreIn 2) (isPGroup_pCoreIn 2 K) hQI]
  apply (normalizes_join_of_commutator K I (K.pCoreIn 2) ?_ hKI).trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  exact K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))

/-- The source equation P = [P,X]U gives the literal product P = O₂(X)U. -/
theorem twoResidual_core_sup_eq (I U : Subgroup G)
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) :
    ((pResidual 2 I).map I.subtype).pCoreIn 2 ⊔ U = I.pCoreIn 2 := by
  let X := (pResidual 2 I).map I.subtype
  have hXI : X ≤ I := map_subtype_le _
  have hIX : I ≤ normalizer (X : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcap : I.pCoreIn 2 ⊓ X ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 I).to_le inf_le_left) inf_le_right
    ((le_inf (hXI.trans hIP) X.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hcomm : ⁅I.pCoreIn 2, X⁆ ≤ X.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp (hXI.trans hIP))
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 I).trans hIX))).trans hcap
  apply le_antisymm (sup_le (pCoreIn_mono_of_normalizes hXI hIX) hUP)
  rw [hfull]
  exact sup_le_sup_right hcomm U

/-- The containing component acts on P = O₂(I), using P = [P,X]U and its action on U. -/
theorem component_normalizes_pair_core [Finite G] (K I U : Subgroup G)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) :
    K ≤ normalizer (I.pCoreIn 2 : Set G) := by
  rw [← twoResidual_core_sup_eq I U hUP hfull]
  exact (le_inf ((component_normalizes_twoResidual K I hQI hKI).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hKU).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Conjugation on the literal P/U; only relative normality is used. -/
@[expose] def sectionAction (K P U : Subgroup G) [(U.subgroupOf P).Normal]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G)) :
    K →* MulAut (P ⧸ U.subgroupOf P) where
  toFun k := QuotientGroup.congr _ _ (P.normalizerMonoidHom (inclusion hKP k)) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp (hKU k.property) y.val).mp hy
    · intro hx
      let a := P.normalizerMonoidHom (inclusion hKP k)
      refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
      exact (mem_normalizer_iff.mp (hKU (K.inv_mem k.property)) x.val).mp hx)
  map_one' := by
    ext x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) x
    change QuotientGroup.mk' (U.subgroupOf P)
      ((P.normalizerMonoidHom.comp (inclusion hKP)) 1 p) = _
    rw [map_one]
    rfl
  map_mul' a b := by
    ext x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) x
    change QuotientGroup.mk' (U.subgroupOf P)
      ((P.normalizerMonoidHom.comp (inclusion hKP)) (a * b) p) = _
    rw [map_mul]
    rfl

/-- The quotient action agrees with the original conjugation on every representative. -/
theorem sectionAction_apply (K P U : Subgroup G) [(U.subgroupOf P).Normal]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (k : K) (p : P) :
    sectionAction K P U hKP hKU k (QuotientGroup.mk' (U.subgroupOf P) p) =
      QuotientGroup.mk' (U.subgroupOf P) (P.normalizerMonoidHom (inclusion hKP k) p) := rfl

/-- The quotient-action kernel is exactly the elements commuting with P modulo U. -/
theorem mem_sectionAction_ker (K P U : Subgroup G) [(U.subgroupOf P).Normal]
    (hKP : K ≤ normalizer (P : Set G)) (hKU : K ≤ normalizer (U : Set G)) (k : K) :
    k ∈ (sectionAction K P U hKP hKU).ker ↔
      ∀ p : P, ⁅(k : G), (p : G)⁆ ∈ U := by
  constructor
  · intro hk p
    have he := MulEquiv.congr_fun hk (QuotientGroup.mk' (U.subgroupOf P) p)
    rw [sectionAction_apply] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    change (k : G) * (p : G) * (k : G)⁻¹ / (p : G) ∈ U at hm
    simpa only [div_eq_mul_inv, commutatorElement_def] using hm
  · intro hk
    apply MulEquiv.ext
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) x
    rw [sectionAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (k : G) * (p : G) * (k : G)⁻¹ / (p : G) ∈ U
    simpa only [div_eq_mul_inv, commutatorElement_def] using hk p

/-- The action needed for the dihedral multiplicity argument, constructed
on the original O₂(I)/U from the source commutator and core identities. -/
@[expose] def componentCoreQuotientAction [Finite G] (K I U : Subgroup G)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) :
    K →* MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) :=
  sectionAction K (I.pCoreIn 2) U
    (component_normalizes_pair_core K I U hQI hKI hKU hUP hfull) hKU

/-- The actual component action on P/U retains its original commutator kernel. -/
theorem mem_componentCoreQuotientAction_ker [Finite G] (K I U : Subgroup G)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) (k : K) :
    k ∈ (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull).ker ↔
      ∀ p : I.pCoreIn 2, ⁅(k : G), (p : G)⁆ ∈ U :=
  mem_sectionAction_ker K (I.pCoreIn 2) U _ hKU k

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
