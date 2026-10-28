module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.ElementaryAbelian.BinaryKernelRankDrop
public import Theory.GroupTheory.SolvableRadical

/-!
# Centralizing local subgroups for large outer PSL₃ actors

A central nonidentity element of A lies in the intrinsic solvable radical of
any subgroup K centralizing it. Thus rank(A) ≤ f+1 implies that the radical
quotient image has rank at most f. The odd E-case already has rank one.
This supplies E.1.5 after the actual local E.1.2 conditions have been proved.

The residual supplement defined below uses C_G(z)^∞ and C_T(z), both with
their literal inclusions. It need not contain T. When C_T(z) is Sylow in
C_G(z), its intersection with the supplement is Sylow as well. Trivial
ambient two-core and z ∈ A give precisely the E0 tau containment needed by
this construction. No centralizer is asserted to satisfy E1 or E2 here.

Source: Aschbacher--Smith E.1.1--5, printed pp.209--210, for the
PSL₃ branch of E.1.14(1), p.214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G : Type*} [Group G] [Finite G]

/-- The remaining local calculation for an outer actor. The witness is a
conjugate of the whole actor, so a conjugation-invariant family retains it.
The final clause is generation of the socle by K and T, not E-generation.
This interface lives below the family assembly to allow independent model
implementations without a cyclic import. -/
@[expose] def HasCentralizerLocalWitness (L : Subgroup G) (T : Sylow 2 G)
    (A : Subgroup G) : Prop :=
  ∃ g z : G,
    let B := A.map (MulAut.conj g).toMonoidHom
    B ≤ (T : Subgroup G) ∧ z ∈ B ∧ z ∉ L ∧
    ∃ S : Sylow 2 (centralizer ({z} : Set G)),
      (S : Subgroup (centralizer ({z} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)) ∧
    ∃ K : Subgroup G,
      (T : Subgroup G) ⊓ centralizer ({z} : Set G) ≤ K ∧
      K ≤ centralizer ({z} : Set G) ∧
      (ECaseOdd B K ∨ ECaseComponent (T : Subgroup G) B K) ∧
      L ≤ K ⊔ (T : Subgroup G)

/-- The intrinsic solvable residual of the centralizer, supplemented only by
its intersection with the fixed ambient Sylow subgroup. -/
@[expose] def centralizerResidualSupplement (T : Sylow 2 G) (z : G) : Subgroup G :=
  (solvableResidual (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype ⊔
    ((T : Subgroup G) ⊓ centralizer ({z} : Set G))

omit [Finite G] in
/-- Both terms of the residual supplement centralize the chosen actor. -/
theorem centralizerResidualSupplement_le (T : Sylow 2 G) (z : G) :
    centralizerResidualSupplement T z ≤ centralizer ({z} : Set G) :=
  sup_le (map_subtype_le _) inf_le_right

omit [Finite G] in
/-- With trivial ambient two-core, tau centralizes every element of A. -/
theorem tau_le_actor_centralizer (hcore : pCore 2 G = ⊥)
    (T A : Subgroup G) {z : G} (hzA : z ∈ A) :
    tau T A ≤ T ⊓ centralizer ({z} : Set G) := by
  intro x hx
  obtain ⟨hxT, hxA⟩ := mem_centralizerModulo_iff.mp hx
  refine ⟨hxT, mem_centralizer_singleton_iff.mpr ?_⟩
  have hc := hxA z hzA
  rw [hcore, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

/-- E.1.5 follows from the central actor, the sharp outer rank bound, and
the literal E.1.2 clauses on the chosen local subgroup. -/
theorem isEMemberAt_of_central_actor {f : ℕ} (hf : 0 < f)
    {T A K : Subgroup G} (hmember : IsEMember T A K)
    (hrank : Group.rank A ≤ f + 1) {z : G} (hzA : z ∈ A) (hz : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G)) : IsEMemberAt f T A K := by
  refine ⟨hmember, ?_⟩
  rcases hmember.2.2.2.2.2 with hodd | hcomp
  · refine Or.inl ⟨hodd, ?_⟩
    obtain ⟨p, _, _, _, _, _, hr⟩ := hodd
    exact hr.le.trans hf
  · let := hmember.1
    have hAK := hmember.2.2.1
    let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
    let w : K := ⟨z, hAK hzA⟩
    have hwC : w ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKz k.property))
    let : Group.IsSolvable (center K) := Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
    have hwR : w ∈ solvableRadical K :=
      le_solvableRadical (center K) inferInstance inferInstance hwC
    refine Or.inr ⟨hcomp, ?_⟩
    apply IsElementaryAbelian.rank_map_le_of_nontrivial_kernel (A.subgroupOf K)
      (QuotientGroup.mk' (solvableRadical K))
      ((Group.rank_congr (subgroupOfEquivOfLe hAK)).le.trans hrank) w hzA
      (fun h => hz (congrArg Subtype.val h))
    exact (QuotientGroup.eq_one_iff _).mpr hwR

omit [Finite G] in
/-- An intermediate subgroup containing the centralizer's chosen Sylow has
the literal ambient Sylow intersection as a Sylow subgroup. -/
theorem sylow_intersection_of_centralizer_intermediate (T : Sylow 2 G) (z : G)
    (S : Sylow 2 (centralizer ({z} : Set G)))
    (hS : (S : Subgroup (centralizer ({z} : Set G))) =
      (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)))
    (K : Subgroup G) (hSK : (T : Subgroup G) ⊓ centralizer ({z} : Set G) ≤ K)
    (hKC : K ≤ centralizer ({z} : Set G)) :
    ∃ R : Sylow 2 K, (R : Subgroup K) = (T : Subgroup G).subgroupOf K := by
  refine ⟨{ toSubgroup := (T : Subgroup G).subgroupOf K
            isPGroup' := T.isPGroup'.comap_subtype
            is_maximal' := ?_ }, rfl⟩
  intro Q hQ hTQ
  have he : Q.map (inclusion hKC) = (S : Subgroup (centralizer ({z} : Set G))) := by
    apply S.is_maximal' (hQ.map _)
    intro c hc
    have hcT : (c : G) ∈ (T : Subgroup G) := by
      rw [hS] at hc
      exact hc
    exact ⟨⟨c, hSK ⟨hcT, c.property⟩⟩, hTQ hcT, rfl⟩
  apply le_antisymm _ hTQ
  intro k hk
  have h := he ▸ mem_map_of_mem (inclusion hKC) hk
  rw [hS] at h
  exact h

/-- The centralizer construction discharges E0, Sylow-ness and quotient
rank. Only the actual E1/E2 local structure remains an input. -/
theorem isEMemberAt_of_centralizer_intermediate {f : ℕ} (hf : 0 < f)
    (hcore : pCore 2 G = ⊥) (T : Sylow 2 G)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hrank : Group.rank A ≤ f + 1)
    (z : G) (hzA : z ∈ A) (hz : z ≠ 1)
    (S : Sylow 2 (centralizer ({z} : Set G)))
    (hS : (S : Subgroup (centralizer ({z} : Set G))) =
      (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)))
    (K : Subgroup G) (hSK : (T : Subgroup G) ⊓ centralizer ({z} : Set G) ≤ K)
    (hKC : K ≤ centralizer ({z} : Set G))
    (hcase : ECaseOdd A K ∨ ECaseComponent (T : Subgroup G) A K) :
    IsEMemberAt f (T : Subgroup G) A K := by
  let := hA
  have hAC : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨z, hzA⟩))
  apply isEMemberAt_of_central_actor hf _ hrank hzA hz hKC
  exact ⟨hA, hAT, (le_inf hAT hAC).trans hSK,
    le_inf (tau_le _ _) ((tau_le_actor_centralizer hcore _ _ hzA).trans hSK),
    sylow_intersection_of_centralizer_intermediate T z S hS K hSK hKC, hcase⟩

/-- Literal application to C_G(z)^∞ C_T(z). In particular, the supplement
uses C_T(z), and no assertion that it contains the whole Sylow is needed. -/
theorem isEMemberAt_centralizerResidualSupplement {f : ℕ} (hf : 0 < f)
    (hcore : pCore 2 G = ⊥) (T : Sylow 2 G)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hrank : Group.rank A ≤ f + 1)
    (z : G) (hzA : z ∈ A) (hz : z ≠ 1)
    (S : Sylow 2 (centralizer ({z} : Set G)))
    (hS : (S : Subgroup (centralizer ({z} : Set G))) =
      (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)))
    (hcase : ECaseComponent (T : Subgroup G) A (centralizerResidualSupplement T z)) :
    IsEMemberAt f (T : Subgroup G) A (centralizerResidualSupplement T z) :=
  isEMemberAt_of_centralizer_intermediate hf hcore T A hA hAT hrank z hzA hz S hS _
    le_sup_right (centralizerResidualSupplement_le T z) (Or.inr hcase)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
