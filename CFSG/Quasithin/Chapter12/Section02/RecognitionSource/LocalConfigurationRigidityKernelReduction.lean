module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelCommon
public import Theory.Frattini.CentralElementarySupplement
public import Theory.Frattini.BinarySquares

/-!
# The common elementary radical and the second splitting in 12.2.25

The order of the original natural module and the index-two hyperplane show
C_V(U)=U∩V. Once the dimension branch proves Q=V C_T(L), the first splitting
R=U C_T(I) therefore gives R=U C_T(L), retaining the original subgroups.

Elementarity needs no dimension split. The kernel displacement [Q,L]=V
lies in a central elementary subgroup, so L fixes Φ(Q). The already proved
R=U×C_T(I) gives Φ(R)=Φ(C_T(I))≤Φ(Q). Thus Φ(R) lies in the common factor
C_T(L)∩C_T(I)=1. All normality remains relative to the indicated groups.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.25, printed p.805, using C.1.13(a), p.124.
The kernel-splitting premise of `centralizer_split_of_kernel_split` is
supplied in dimensions four and five by `LocalConfigurationRigidityKernelD45`;
its dimension-three discharge stays with qt-d-12225-common-centralizers.
Final source assembly remains with qt-d-12213-local-rigidity.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

omit [Finite G] in
/-- The source natural marking gives the order of the original chosen subgroup. -/
theorem chosen_card (A : NaturalLocalAnalysis T L V d) : Nat.card V = 2 ^ d := by
  obtain ⟨e,f,hf⟩ := A.natural
  rw [Nat.card_congr f.toEquiv]
  simp

/-- The two modules have the same centralizer intersection, with their
roles reversed. The index-two hyperplane and nontrivial commutator are used. -/
theorem chosen_centralizer_core
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    V ⊓ centralizer (U : Set G) = U ⊓ V := by
  let := C.elementary
  let W := U ⊓ V
  let X := V ⊓ centralizer (U : Set G)
  have hWX : W ≤ X := le_inf inf_le_right (inf_le_left.trans (le_centralizer U))
  have hWV : W ≤ V := inf_le_right
  have hWcard : Nat.card W = 2 ^ (d - 1) := C.hyperplane
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hd : 1 ≤ d := by have := A.dimension.1; omega
  have hvcard : Nat.card V = 2 * Nat.card W := by
    rw [chosen_card A, hWcard]
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) (by omega)
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ, Nat.mul_comm]
  have hindex : W.relIndex V = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) W V bot_le hWV
    rw [relIndex_bot_left, relIndex_bot_left, hvcard] at hh
    nlinarith
  have htower := relIndex_mul_relIndex W X V hWX inf_le_left
  rw [hindex] at htower
  rcases (Nat.dvd_prime Nat.prime_two).mp
    (show W.relIndex X ∣ 2 from ⟨X.relIndex V, htower.symm⟩) with hone | htwo
  · exact le_antisymm (relIndex_eq_one.mp hone) hWX
  · rw [htwo] at htower
    have hXV : X = V := le_antisymm inf_le_left
      (relIndex_eq_one.mp (show X.relIndex V = 1 from by omega))
    have hv : V ≤ centralizer (U : Set G) := hXV ▸ (inf_le_right : X ≤ _)
    have hzero : W = ⊥ := C.transvections.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hv))
    have hlarge : 1 < 2 ^ (d - 1) := one_lt_pow₀ (by decide) (by have := A.dimension.1; omega)
    rw [hzero, card_bot] at hWcard
    omega

/-- Once the dimension branch splits Q, the same original factors split R.
The branch premise remains with qt-d-12225-common-centralizers. -/
theorem centralizer_split_of_kernel_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hQ : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let := C.elementary
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hZU : Z ≤ centralizer (U : Set G) := component_centralizer_le_core_centralizer D A C
  have hZV : Z ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le D.le_component)).trans (Subgroup.centralizer_le_normalizer _)
  have hEQ : E ≤ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊓
      centralizer (U : Set G) := le_inf
    (le_inf inf_le_left (inf_le_right.trans (centralizer_le
      (show V ≤ cyclicPairJoin P U V from le_sup_right))))
    (inf_le_right.trans (centralizer_le
      (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  have hE : E ≤ U ⊔ Z := by
    rw [hQ, sup_comm V Z, inf_centralizer_sup_of_centralizing Z V U hZV hZU,
      chosen_centralizer_core A C] at hEQ
    exact hEQ.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  apply le_antisymm
  · rw [C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural G T L h).2.2 V D).1) D.le_sylow hnone]
    exact sup_le le_sup_left hE
  · exact sup_le (le_inf C.core_le_sylow (le_centralizer U)) (le_inf inf_le_left hZU)

/-- The actual kernel's Frattini subgroup is fixed by L. Every displacement
lies in the central elementary subgroup V, so conjugation preserves squares. -/
theorem kernel_frattini_centralizes
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    (frattini ↥((T : Subgroup G) ⊓ centralizer (V : Set G))).map
      ((T : Subgroup G) ⊓ centralizer (V : Set G)).subtype ≤ centralizer (L : Set G) := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let := D.elementary
  have hQ : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  rw [map_le_iff_le_comap, hQ.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro x ⟨q,rfl⟩ l hl
  change l * (q : G) ^ 2 = (q : G) ^ 2 * l
  let v := l * (q : G) * l⁻¹ * (q : G)⁻¹
  have hv : v ∈ V := (kernel_commutator_eq D A C).le
    ((commutator_comm L Q).le (commutator_mem_commutator hl q.property))
  have hc : Commute v (q : G) := q.property.2 v hv
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
  have he : l * (q : G) ^ 2 * l⁻¹ = (q : G) ^ 2 := by
    calc
      _ = (l * (q : G) * l⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
      _ = (v * (q : G)) ^ 2 := by simp only [v, inv_mul_cancel_right]
      _ = v ^ 2 * (q : G) ^ 2 := hc.mul_pow 2
      _ = (q : G) ^ 2 := by rw [hv2, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp he

/-- R is elementary in every dimension, without first splitting Q. The
Frattini subgroup of R equals that of C_T(I), embeds in Φ(Q), and therefore
lies in the common central factor already eliminated by uniqueness. -/
theorem radical_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    IsElementaryAbelian 2 ↥((T : Subgroup G) ⊓ centralizer (U : Set G)) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hR : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hQ : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hEQ : E ≤ Q := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right)))
  have hE : IsPGroup 2 E := T.isPGroup'.to_le inf_le_left
  let : Fact (IsPGroup 2 E) := ⟨hE⟩
  have hfEQ : (frattini E).map E.subtype ≤ (frattini Q).map Q.subtype := by
    have hh := map_mono (f := Q.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hEQ))
    rw [map_map] at hh
    exact hh
  have hfE := frattini_map_eq_of_central_elementary_supplement R E U hR C.elementary
    (le_centralizer_iff.mp inf_le_right)
    (C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural G T L h).2.2 V D).1) D.le_sylow hnone)
  have hf : (frattini R).map R.subtype = ⊥ := by
    apply bot_unique
    rw [← common_trivial h D C, hfE]
    exact le_inf (le_inf ((map_subtype_le _).trans inf_le_left)
      (hfEQ.trans (kernel_frattini_centralizes D A C))) (map_subtype_le _)
  apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
  exact map_injective R.subtype_injective (hf.trans (Subgroup.map_bot R.subtype).symm)

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
