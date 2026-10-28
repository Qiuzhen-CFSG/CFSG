module
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.CComponent.TwoComponent.CoreQuotient
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Solvable core intersections in local Cartan products

Let K be perfect with simple two-core quotient and normalized by a full
Sylow two-subgroup P. Suppose a cubic actor A permutes with P and meets a
normal solvable subgroup R only inside K. Then A and K both normalize
P ∩ R. The radical of KP is a two-group. In AP, the marked intersection
makes A disjoint from R, and the product-order formula forces R ∩ AP to
be a two-group. Normality places both intersections in the supplied P.

Thus the actual perfect residual of N_J(P ∩ R) contains K and is normalized
by A whenever A normalizes J. The final definitions retain the source
three-stage core O_{2,2′,2}, including its solvability and radical identity.
No normalization of the full Sylow subgroup by A is assumed.

Source application: Aschbacher–Smith, Proposition 9.3.1, the noncentral
odd-core containing-component reduction, printed p.732.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory.LocalSolvableCoreNormalizer
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem card_sup_permutable_disjoint (A P : Subgroup X)
    (hp : (A : Set X) * (P : Set X) = (P : Set X) * (A : Set X))
    (hd : Disjoint A P) : Nat.card (A ⊔ P : Subgroup X) = Nat.card A * Nat.card P := by
  let f : A × P → (A ⊔ P : Subgroup X) :=
    fun x => ⟨x.1 * x.2,mul_mem_sup x.1.property x.2.property⟩
  have hi : Function.Injective f := fun _ _ h => mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro x
    have hx : (x : X) ∈ (A : Set X) * (P : Set X) := coe_sup_of_set_mul_comm A P hp ▸ x.property
    obtain ⟨a,ha,p,hp,h⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨p,hp⟩),Subtype.ext h⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans (Nat.card_prod A P)

private theorem normal_disjoint_complement_isTwoGroup
    (A P R : Subgroup X) [R.Normal] (hP : IsPGroup 2 P)
    (hd : Disjoint R A) (hc : Nat.card X = Nat.card A * Nat.card P) : IsPGroup 2 R := by
  have hm : Nat.card R * Nat.card A ∣ Nat.card P * Nat.card A := by
    rw [← card_sup_eq_mul_of_normalizes_of_disjoint R A le_normalizer_of_normal hd,
      mul_comm (Nat.card P),←hc]
    exact card_subgroup_dvd_card _
  have hdvd : Nat.card R ∣ Nat.card P := (Nat.mul_dvd_mul_iff_right Nat.card_pos).mp hm
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  rw [hn] at hdvd
  exact IsPGroup.of_card_dvd_pow hdvd

omit [Finite X] in
private theorem normal_intersection_is_sylow_intersection
    (P : Sylow 2 X) (R Y : Subgroup X) [R.Normal]
    (hPY : (P : Subgroup X) ≤ Y) (hR : IsPGroup 2 (R.subgroupOf Y)) :
    Y ≤ normalizer (((P : Subgroup X) ⊓ R : Subgroup X) : Set X) := by
  have hp := hR.le_sylow_of_normal (P.subtype hPY)
  have he : Y ⊓ R = (P : Subgroup X) ⊓ R := by
    apply le_antisymm
    · intro x hx
      exact ⟨hp (show (⟨x,hx.1⟩ : Y) ∈ R.subgroupOf Y from hx.2),hx.2⟩
    · exact inf_le_inf_right R hPY
  rw [←he]
  exact (le_inf Y.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

private theorem normal_solvable_intersection_isTwoGroup
    (K R : Subgroup X) [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)]
    [R.Normal] [Group.IsSolvable R] : IsPGroup 2 (R.subgroupOf K) := by
  have hh : R.subgroupOf K ≤ solvableRadical K :=
    le_solvableRadical _ inferInstance (Group.isSolvable_of_isSolvable_injective
      (f := K.subtype.subgroupComap R) (fun a b h => Subtype.ext (Subtype.ext
        (congrArg (fun x : R => (x : X)) h))))
  rw [PerfectCoreTwoExtension.radical_eq_core] at hh
  exact pCore_isPGroup.to_le hh

/-- Both the cubic actor and the perfect local subgroup preserve the actual
Sylow intersection with a normal solvable core. -/
theorem cartan_and_local_normalize_sylow_core
    (P : Sylow 2 X) (K A R : Subgroup X)
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)] [R.Normal] [Group.IsSolvable R]
    (hPK : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hA : IsPGroup 3 A) (hAR : A ⊓ R ≤ K)
    (hperm : (A : Set X) * (P : Set X) = (P : Set X) * (A : Set X)) :
    A ≤ normalizer (((P : Subgroup X) ⊓ R : Subgroup X) : Set X) ∧
    K ≤ normalizer (((P : Subgroup X) ⊓ R : Subgroup X) : Set X) := by
  have hRK := normal_solvable_intersection_isTwoGroup K R
  have hARd : Disjoint A R := by
    apply disjoint_def.mpr
    intro x hxA hxR
    have hxK := hAR ⟨hxA,hxR⟩
    have htwo : IsPGroup 2 ((R.subgroupOf K).map K.subtype) := hRK.map K.subtype
    exact disjoint_def.mp (hA.disjoint_of_coprime htwo (by decide)) hxA ⟨⟨x,hxK⟩,hxR,rfl⟩
  have hAc : Nat.card (A ⊔ (P : Subgroup X) : Subgroup X) = Nat.card A * Nat.card P :=
    card_sup_permutable_disjoint A P hperm (hA.disjoint_of_coprime P.isPGroup' (by decide))
  let Y := A ⊔ (P : Subgroup X)
  have hRY : IsPGroup 2 (R.subgroupOf Y) := by
    apply normal_disjoint_complement_isTwoGroup (A.subgroupOf Y) ((P : Subgroup X).subgroupOf Y)
      (R.subgroupOf Y) P.isPGroup'.comap_subtype
    · apply disjoint_def.mpr
      intro x hxR hxA
      apply Subtype.ext
      exact disjoint_def.mp hARd hxA hxR
    · rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ Y from le_sup_left)).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe (show (P : Subgroup X) ≤ Y from le_sup_right)).toEquiv]
      exact hAc
  have hAN := le_sup_left.trans
    (normal_intersection_is_sylow_intersection P R Y le_sup_right hRY)
  let V := K ⊔ (P : Subgroup X)
  let D := K.subgroupOf V
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hPK)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ V from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ V from le_sup_left)).symm.surjective
  let d : D ≃* K := subgroupOfEquivOfLe (show K ≤ V from le_sup_left)
  let ed : (D ⧸ pCore 2 D) ≃* (K ⧸ pCore 2 K) := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let : IsSimpleGroup (D ⧸ pCore 2 D) := ed.isSimpleGroup
  have hg : D ⊔ (P : Subgroup X).subgroupOf V = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ V from le_sup_left) (show (P : Subgroup X) ≤ V from le_sup_right)]
    exact subgroupOf_self _
  have hq : IsPGroup 2 (V ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D _ P.isPGroup'.comap_subtype hg
  have hr : solvableRadical V = pCore 2 V := PerfectCoreTwoExtension.extension_radical_eq_core D hq
  have hRV : IsPGroup 2 (R.subgroupOf V) := by
    have hh : R.subgroupOf V ≤ solvableRadical V :=
      le_solvableRadical _ inferInstance (Group.isSolvable_of_isSolvable_injective
        (f := V.subtype.subgroupComap R) (fun a b h => Subtype.ext (Subtype.ext
          (congrArg (fun x : R => (x : X)) h))))
    rw [hr] at hh
    exact pCore_isPGroup.to_le hh
  exact ⟨hAN,le_sup_left.trans (normal_intersection_is_sylow_intersection P R V le_sup_right hRV)⟩

/-- The embedded terminal derived subgroup of the local normalizer N_J(Q). -/
def localNormalizerResidual (J Q : Subgroup X) : Subgroup X :=
  (solvableResidual (J ⊓ normalizer (Q : Set X) : Subgroup X)).map (J ⊓ normalizer (Q : Set X)).subtype

/-- The local subgroup lies in the perfect residual of N_J(P ∩ R), and the
original cubic actor normalizes that same residual. -/
theorem cartan_invariant_localNormalizerResidual
    (P : Sylow 2 X) (K A J R : Subgroup X)
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)] [R.Normal] [Group.IsSolvable R]
    (hPK : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hA : IsPGroup 3 A) (hAR : A ⊓ R ≤ K)
    (hperm : (A : Set X) * (P : Set X) = (P : Set X) * (A : Set X))
    (hKJ : K ≤ J) (hAJ : A ≤ normalizer (J : Set X)) :
    K ≤ localNormalizerResidual J ((P : Subgroup X) ⊓ R) ∧
    A ≤ normalizer (localNormalizerResidual J ((P : Subgroup X) ⊓ R) : Set X) := by
  obtain ⟨hAQ,hKQ⟩ := cartan_and_local_normalize_sylow_core P K A R hPK hA hAR hperm
  refine ⟨le_map_solvableResidual_of_isPerfect K _ (le_inf hKJ hKQ),?_⟩
  exact ((le_inf hAJ (hAQ.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
end Theory.GroupTheory.LocalSolvableCoreNormalizer

namespace Subgroup
variable {X : Type*} [Group X]

/-- The source O_{2,2′,2}(X), with both quotient maps retained literally. -/
abbrev twoOddTwoCore (X : Type*) [Group X] : Subgroup X :=
  (oddTwoCore (X ⧸ pCore 2 X)).comap (QuotientGroup.mk' (pCore 2 X))

instance twoOddTwoCore_characteristic : (twoOddTwoCore X).Characteristic :=
  Characteristic.comap_quotient_mk inferInstance

/-- A solvable middle odd core makes the full three-stage core solvable. -/
theorem twoOddTwoCore_isSolvable [Finite X]
    [Group.IsSolvable (pPrimeCore 2 (X ⧸ pCore 2 X))] :
    Group.IsSolvable (twoOddTwoCore X) := by
  let : Group.IsSolvable (oddTwoCore (X ⧸ pCore 2 X)) := oddTwoCore_isSolvable
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    let := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
    infer_instance
  exact isSolvable_comap_of_solvable_ker (QuotientGroup.mk' (pCore 2 X)) _

/-- In the quasisimple odd-core quotient case, the three-stage core is exactly
the solvable radical. -/
theorem twoOddTwoCore_eq_solvableRadical [Finite X]
    [Group.IsSolvable (pPrimeCore 2 (X ⧸ pCore 2 X))]
    [IsQuasisimple ((X ⧸ pCore 2 X) ⧸ pPrimeCore 2 (X ⧸ pCore 2 X))] :
    twoOddTwoCore X = solvableRadical X := by
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    let := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
    infer_instance
  change (oddTwoCore (X ⧸ pCore 2 X)).comap _ = _
  rw [oddTwoCore_eq_solvableRadical_of_quasisimple]
  exact comap_solvableRadical_eq_of_solvable_ker _ (QuotientGroup.mk'_surjective _)
end Subgroup

