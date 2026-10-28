module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.PPrimeCore

/-!
# Comparing images of a group with quasisimple two-core quotient

For a subnormal subgroup C of H, O₂(C) lies in O₂(H), hence in O₃′(H).
Thus its image R in H/O₃′(H) is a quotient of C/O₂(C). If three divides
|C| then R is nontrivial, so a quasisimple C/O₂(C) makes R quasisimple.

Two nontrivial images of one quasisimple group have canonically isomorphic
central quotients. We retain compatibility on representatives, so this
comparison can be used for an action image as well as an ambient quotient.
The Chapter 13 application supplies subnormality and quasisimplicity
separately; neither follows merely from an arbitrary perfect subgroup.
Source: the quotient step in Aschbacher–Smith A.3.18, pp.51–52, and
its application in 13.6.20, p.931 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {H Q R P : Type*} [Group H] [Group Q] [Group R] [Group P]

/-- The center pulls back to the center under a nontrivial quasisimple image. -/
theorem IsQuasisimple.comap_center_of_surjective [IsQuasisimple Q] [Nontrivial R]
    (f : Q →* R) (hf : Function.Surjective f) :
    (center R).comap f = center Q := by
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective hf
  apply le_antisymm
  · rcases IsQuasisimple.normal_le_center_or_eq_top ((center R).comap f) with hc | ht
    · exact hc
    · have hc : center R = ⊤ := by
        apply comap_injective hf
        simpa using ht
      exact (Group.IsPerfect.not_isMulCommutative R (center_eq_top_iff.mp hc)).elim
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)

/-- A central quotient isomorphism retaining the original surjection. -/
noncomputable def IsQuasisimple.centralQuotientEquiv [IsQuasisimple Q] [Nontrivial R]
    (f : Q →* R) (hf : Function.Surjective f) : Q ⧸ center Q ≃* R ⧸ center R := by
  let q := (QuotientGroup.mk' (center R)).comp f
  have hk : q.ker = center Q := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact IsQuasisimple.comap_center_of_surjective f hf
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf))

theorem IsQuasisimple.centralQuotientEquiv_mk [IsQuasisimple Q] [Nontrivial R]
    (f : Q →* R) (hf : Function.Surjective f) (x : Q) :
    IsQuasisimple.centralQuotientEquiv f hf (QuotientGroup.mk' (center Q) x) =
      QuotientGroup.mk' (center R) (f x) := rfl

/-- Compare two images through their common quasisimple source. -/
noncomputable def IsQuasisimple.imageCentralQuotientEquiv [IsQuasisimple Q]
    [Nontrivial R] [Nontrivial P] (f : Q →* R) (hf : Function.Surjective f)
    (g : Q →* P) (hg : Function.Surjective g) : R ⧸ center R ≃* P ⧸ center P :=
  (IsQuasisimple.centralQuotientEquiv f hf).symm.trans
    (IsQuasisimple.centralQuotientEquiv g hg)

theorem IsQuasisimple.imageCentralQuotientEquiv_mk [IsQuasisimple Q]
    [Nontrivial R] [Nontrivial P] (f : Q →* R) (hf : Function.Surjective f)
    (g : Q →* P) (hg : Function.Surjective g) (x : Q) :
    IsQuasisimple.imageCentralQuotientEquiv f hf g hg (QuotientGroup.mk' (center R) (f x)) =
      QuotientGroup.mk' (center P) (g x) := by
  change (IsQuasisimple.centralQuotientEquiv g hg)
    ((IsQuasisimple.centralQuotientEquiv f hf).symm
      (QuotientGroup.mk' (center R) (f x))) = _
  rw [← IsQuasisimple.centralQuotientEquiv_mk f hf x, MulEquiv.symm_apply_apply,
    IsQuasisimple.centralQuotientEquiv_mk]

variable [Finite H]

/-- A subnormal subgroup's two-core is killed by the ambient three-prime quotient. -/
theorem twoCore_le_ker_threePrime_image (C : Subgroup H) (hC : C.IsSubnormal) :
    pCore 2 C ≤ ((QuotientGroup.mk' (pPrimeCore 3 H)).subgroupMap C).ker := by
  have hcore : pCore 2 H ≤ pPrimeCore 3 H := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  rw [ker_subgroupMap, QuotientGroup.ker_mk', pCore_subnormal_eq_comap 2 hC]
  exact comap_mono hcore

/-- The induced surjection from the intrinsic two-core quotient. -/
noncomputable def twoCoreToThreePrimeImage (C : Subgroup H) (hC : C.IsSubnormal) :
    (C ⧸ pCore 2 C) →* C.map (QuotientGroup.mk' (pPrimeCore 3 H)) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (pPrimeCore 3 H)).subgroupMap C)
    (twoCore_le_ker_threePrime_image C hC)

theorem twoCoreToThreePrimeImage_surjective (C : Subgroup H) (hC : C.IsSubnormal) :
    Function.Surjective (twoCoreToThreePrimeImage C hC) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    ((QuotientGroup.mk' (pPrimeCore 3 H)).subgroupMap_surjective C) _

theorem twoCoreToThreePrimeImage_mk (C : Subgroup H) (hC : C.IsSubnormal) (c : C) :
    twoCoreToThreePrimeImage C hC (QuotientGroup.mk' (pCore 2 C) c) =
      (QuotientGroup.mk' (pPrimeCore 3 H)).subgroupMap C c := rfl

/-- Divisibility by three prevents the entire subgroup disappearing in O₃′. -/
theorem threePrime_image_nontrivial (C : Subgroup H) (h3 : 3 ∣ Nat.card C) :
    Nontrivial (C.map (QuotientGroup.mk' (pPrimeCore 3 H))) := by
  apply (nontrivial_iff_ne_bot _).mpr
  intro he
  have hle : C ≤ pPrimeCore 3 H := by
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  exact Nat.prime_three.coprime_iff_not_dvd.mp
    (pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le hle)) h3

/-- The actual image used by A.3.18 is quasisimple. -/
theorem quasisimple_threePrime_image (C : Subgroup H) (hC : C.IsSubnormal)
    [IsQuasisimple (C ⧸ pCore 2 C)] (h3 : 3 ∣ Nat.card C) :
    IsQuasisimple (C.map (QuotientGroup.mk' (pPrimeCore 3 H))) := by
  let := threePrime_image_nontrivial C h3
  exact IsQuasisimple.of_surjective (twoCoreToThreePrimeImage C hC)
    (twoCoreToThreePrimeImage_surjective C hC)

end Theory.GroupTheory
