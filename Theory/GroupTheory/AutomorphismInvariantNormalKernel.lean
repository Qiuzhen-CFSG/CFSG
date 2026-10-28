module
public import Theory.GroupTheory.SylowCharacteristicKernelLifting
public import Theory.PGroupCore

/-!
# The largest automorphism-invariant ambient normal kernel

For an automorphism of a subgroup S, take the join of intrinsic subgroups
whose images are ambient-normal and invariant under that automorphism.
This constructs its largest invariant normal kernel. The induced automorphism
on the literal quotient image of S fixes no nontrivial ambient-normal subgroup.
Its centralizer maximality supplies the original premise of Niles Lemma 7.3.

The final intersection argument of Niles Theorem 7.2 is also proved: the
explicit cyclic-orbit formula of Lemma 7.6 makes the intersection of these
kernels characteristic in S. The no-characteristic-normal hypothesis then
forces some kernel to omit any specified nontrivial subgroup.

Source: Niles, *Pushing-up in finite groups* (1979), printed pp.60–62.
Lemma 7.6's orbit formula and the other Main Hypothesis inheritance conditions
remain separate mathematical inputs; no source theorem is assumed here.
-/

public section
open Subgroup

namespace NilesRankOneKernel
variable {H : Type*} [Group H]

/-- Intrinsic subgroups with ambient-normal image which are fixed by α. -/
@[expose] def Admissible (S : Subgroup H) (α : MulAut S) (A : Subgroup S) : Prop :=
  (A.map S.subtype).Normal ∧ A.map α.toMonoidHom = A

/-- The largest α-invariant subgroup of S which is normal in H. -/
@[expose] def invariantNormalKernel (S : Subgroup H) (α : MulAut S) : Subgroup S :=
  ⨆ A : {A : Subgroup S // Admissible S α A}, A.val

theorem le_invariantNormalKernel (S : Subgroup H) (α : MulAut S)
    (A : Subgroup S) (hA : (A.map S.subtype).Normal)
    (ha : A.map α.toMonoidHom = A) : A ≤ invariantNormalKernel S α :=
  le_iSup_of_le ⟨A, hA, ha⟩ le_rfl

instance invariantNormalKernel_image_normal (S : Subgroup H) (α : MulAut S) :
    ((invariantNormalKernel S α).map S.subtype).Normal := by
  unfold invariantNormalKernel
  rw [Subgroup.map_iSup]
  let _ : ∀ A : {A : Subgroup S // Admissible S α A},
      (A.val.map S.subtype).Normal := fun A => A.property.1
  infer_instance

instance invariantNormalKernel_normal (S : Subgroup H) (α : MulAut S) :
    (invariantNormalKernel S α).Normal := by
  have h := (invariantNormalKernel_image_normal S α).comap S.subtype
  rwa [comap_map_eq_self_of_injective S.subtype_injective] at h

theorem invariantNormalKernel_fixed (S : Subgroup H) (α : MulAut S) :
    (invariantNormalKernel S α).map α.toMonoidHom = invariantNormalKernel S α := by
  unfold invariantNormalKernel
  rw [Subgroup.map_iSup]
  congr 1
  funext A
  exact A.property.2

private theorem centralizer_map_equiv {G : Type*} [Group G]
    (e : MulAut G) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- The intrinsic centralizer embedded in the original ambient group. -/
theorem centralizer_map_subtype (S : Subgroup H) (A : Subgroup S) :
    (centralizer (A : Set S)).map S.subtype =
      S ⊓ centralizer (A.map S.subtype : Set H) := by
  apply le_antisymm
  · exact le_inf (map_subtype_le _) (map_centralizer_le_centralizer_image _ _)
  · intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    intro a ha
    apply Subtype.ext
    exact hx.2 a (mem_map_of_mem S.subtype ha)

/-- The exact maximality step in the proof of Niles 7.3. Containment in a
normal Q≤S makes the Sylow centralizer ambient-normal; α-invariance follows
from α-invariance of Nα. -/
theorem centralizer_le_kernel_of_le_normal
    (S : Subgroup H) (α : MulAut S) (Q : Subgroup H) [Q.Normal]
    (hQS : Q ≤ S)
    (hCQ : (centralizer (invariantNormalKernel S α : Set S)).map S.subtype ≤ Q) :
    centralizer (invariantNormalKernel S α : Set S) ≤ invariantNormalKernel S α := by
  let N := invariantNormalKernel S α
  let C := centralizer (N : Set S)
  have hCN : (C.map S.subtype).Normal := by
    have he : C.map S.subtype = Q ⊓ centralizer (N.map S.subtype : Set H) := by
      apply le_antisymm
      · exact le_inf hCQ (map_centralizer_le_centralizer_image _ _)
      · intro x hx
        refine ⟨⟨x, hQS hx.1⟩, ?_, rfl⟩
        intro n hn
        apply Subtype.ext
        exact hx.2 n (mem_map_of_mem S.subtype hn)
    rw [he]
    infer_instance
  apply le_invariantNormalKernel S α C hCN
  rw [centralizer_map_equiv, invariantNormalKernel_fixed]

/-- The original source 7.3 premise, with the literal two-core. -/
theorem centralizer_le_kernel_of_le_twoCore [Finite H]
    (S : Sylow 2 H) (α : MulAut S)
    (hC : (centralizer (invariantNormalKernel (S : Subgroup H) α : Set S)).map
      (S : Subgroup H).subtype ≤ pCore 2 H) :
    centralizer (invariantNormalKernel (S : Subgroup H) α : Set S) ≤
      invariantNormalKernel (S : Subgroup H) α :=
  centralizer_le_kernel_of_le_normal (S : Subgroup H) α (pCore 2 H)
    (pCore_isPGroup.le_sylow_of_normal S) hC

/-- The literal ambient hmax premise consumed by the parent's Niles 7.3
normal-centralizer argument. -/
theorem sylow_inf_centralizer_le_kernel_of_le_twoCore [Finite H]
    (S : Sylow 2 H) (α : MulAut S)
    (hC : (S : Subgroup H) ⊓ centralizer
      ((invariantNormalKernel (S : Subgroup H) α).map
        (S : Subgroup H).subtype : Set H) ≤ pCore 2 H) :
    (S : Subgroup H) ⊓ centralizer
      ((invariantNormalKernel (S : Subgroup H) α).map
        (S : Subgroup H).subtype : Set H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype := by
  rw [← centralizer_map_subtype] at hC ⊢
  exact map_mono (centralizer_le_kernel_of_le_twoCore S α hC)

/-- The original subgroup map into the ambient quotient has exactly the
intrinsic invariant normal kernel. -/
theorem quotient_subtype_ker (S : Subgroup H) (α : MulAut S) :
    ((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).comp
      S.subtype).ker = invariantNormalKernel S α := by
  ext x
  change QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype) (x : H) = 1 ↔ _
  constructor
  · intro hx
    have hm := (QuotientGroup.eq_one_iff (N := (invariantNormalKernel S α).map S.subtype)
      (x : H)).mp hx
    obtain ⟨y, hy, he⟩ := hm
    have he' : y = x := S.subtype_injective he
    exact he' ▸ hy
  · intro hx
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem S.subtype hx)

/-- A normal subgroup of the quotient lying in the actual image of S lifts
to an admissible intrinsic subgroup when its lift is α-invariant. -/
theorem quotient_normal_eq_bot_of_fixed_preimage
    (S : Subgroup H) (α : MulAut S)
    (P : Subgroup (H ⧸ (invariantNormalKernel S α).map S.subtype)) [P.Normal]
    (hPS : P ≤ S.map (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)))
    (hα : (P.comap ((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).comp
      S.subtype)).map α.toMonoidHom =
      P.comap ((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).comp
        S.subtype)) : P = ⊥ := by
  let N := invariantNormalKernel S α
  let L := N.map S.subtype
  let q := QuotientGroup.mk' L
  let A := P.comap (q.comp S.subtype)
  have he : A.map S.subtype = P.comap q := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      obtain ⟨y, hy, he⟩ := hPS hx
      have hxy : x * y⁻¹ ∈ L := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (x * y⁻¹) = 1
        rw [map_mul, map_inv, he, mul_inv_cancel]
      have hxS : x ∈ S := by
        have hh := S.mul_mem ((map_subtype_le N) hxy) hy
        simpa only [inv_mul_cancel_right] using hh
      exact ⟨⟨x, hxS⟩, hx, rfl⟩
  have hAN : (A.map S.subtype).Normal := by rw [he]; infer_instance
  have hle : A ≤ N := le_invariantNormalKernel S α A hAN hα
  apply le_bot_iff.mp
  intro z hz
  obtain ⟨x, hxS, rfl⟩ := hPS hz
  have hx : (⟨x, hxS⟩ : S) ∈ A := hz
  exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem S.subtype (hle hx))

/-- Quotienting by the maximal invariant normal kernel induces an
automorphism on the literal ambient image of S. The formula is retained
as part of the public interface. -/
theorem exists_quotientImageAut (S : Subgroup H) (α : MulAut S) :
    ∃ β : MulAut (S.map
        (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype))),
      ∀ x : S,
        β (((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).subgroupMap S) x) =
        ((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).subgroupMap S) (α x) := by
  let N := invariantNormalKernel S α
  let q := QuotientGroup.mk' (N.map S.subtype)
  let j := q.subgroupMap S
  have hj : N = j.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    rw [← Subtype.val_inj]
    change x ∈ N ↔ q (x : H) = 1
    exact (SetLike.ext_iff.mp (quotient_subtype_ker S α) x).symm
  let e := QuotientGroup.liftEquiv N (q.subgroupMap_surjective S) hj
  let a := QuotientGroup.congr N N α (invariantNormalKernel_fixed S α)
  refine ⟨(e.symm.trans a).trans e, ?_⟩
  intro x
  have he (x : S) : e (QuotientGroup.mk' N x) = j x := by
    exact QuotientGroup.liftEquiv_coe N (q.subgroupMap_surjective S) hj x
  change e (a (e.symm (j x))) = j (α x)
  rw [← he x, e.symm_apply_apply]
  change e (QuotientGroup.mk' N (α x)) = j (α x)
  exact he (α x)

/-- The induced quotient automorphism fixes no nontrivial subgroup of its
domain which is normal in the actual ambient quotient. -/
theorem quotient_normal_eq_bot_of_imageAut_fixed
    (S : Subgroup H) (α : MulAut S)
    (β : MulAut (S.map
      (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype))))
    (hβ : ∀ x : S,
      β (((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).subgroupMap S) x) =
      ((QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)).subgroupMap S) (α x))
    (P : Subgroup (H ⧸ (invariantNormalKernel S α).map S.subtype)) [P.Normal]
    (hPS : P ≤ S.map (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)))
    (hPβ : (P.subgroupOf
      (S.map (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)))).map
        β.toMonoidHom = P.subgroupOf
      (S.map (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype)))) : P = ⊥ := by
  let N := invariantNormalKernel S α
  let q := QuotientGroup.mk' (N.map S.subtype)
  let j := q.subgroupMap S
  let B := P.subgroupOf (S.map q)
  have hfix (x : S) : j x ∈ B ↔ j (α x) ∈ B := by
    have he : (B.map β.toMonoidHom).comap β.toMonoidHom = B :=
      comap_map_eq_self_of_injective β.injective _
    rw [hPβ] at he
    have hh := SetLike.ext_iff.mp he (j x)
    change β (j x) ∈ B ↔ j x ∈ B at hh
    rw [hβ] at hh
    exact hh.symm
  apply quotient_normal_eq_bot_of_fixed_preimage S α P hPS
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hfix y).mp hy
  · intro hx
    have hx' : j x ∈ B := hx
    refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
    exact (hfix (α.symm x)).mpr (by simpa only [α.apply_symm_apply] using hx')

/-- The characteristic core of Q inside its original group. -/
@[expose] def automorphismCore {G : Type*} [Group G] (Q : Subgroup G) : Subgroup G :=
  ⨅ β : MulAut G, Q.map β.toMonoidHom

instance automorphismCore_characteristic {G : Type*} [Group G] (Q : Subgroup G) :
    (automorphismCore Q).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro β
  apply le_iInf
  intro γ
  have hh := map_mono (f := β.toMonoidHom)
    (iInf_le (fun δ : MulAut G => Q.map δ.toMonoidHom) (β⁻¹ * γ))
  change (automorphismCore Q).map β.toMonoidHom ≤ _ at hh
  rw [map_map] at hh
  have he : β.toMonoidHom.comp (β⁻¹ * γ).toMonoidHom = γ.toMonoidHom := by
    ext x
    change β (β⁻¹ (γ x)) = γ x
    exact β.apply_symm_apply _
  rwa [he] at hh

/-- This is precisely the equality of intersections in the final paragraph
of Niles 7.2, with Lemma 7.6 supplied as hformula. -/
theorem iInf_kernels_eq_automorphismCore
    {G : Type*} [Group G] (Q : Subgroup G) (N : MulAut G → Subgroup G)
    (hformula : ∀ α, N α = ⨅ n : ℤ, Q.map ((α ^ n).toMonoidHom)) :
    (⨅ α, N α) = automorphismCore Q := by
  apply le_antisymm
  · apply le_iInf
    intro α
    calc
      (⨅ β, N β) ≤ N α := iInf_le _ α
      _ = ⨅ n : ℤ, Q.map ((α ^ n).toMonoidHom) := hformula α
      _ ≤ Q.map α.toMonoidHom := by
        simpa only [zpow_one] using
          (iInf_le (fun n : ℤ => Q.map ((α ^ n).toMonoidHom)) 1)
  · apply le_iInf
    intro α
    rw [hformula]
    apply le_iInf
    intro n
    exact iInf_le (fun β : MulAut G => Q.map β.toMonoidHom) (α ^ n)

/-- The characteristic-intersection contradiction of source 7.2. The only
source-dependent premise here is the explicit Lemma 7.6 formula, and it is
only required in the branch where V lies in the particular kernel. -/
theorem exists_not_le_invariantNormalKernel
    (S : Subgroup H)
    (hno : Theory.GroupTheory.NoCharacteristicNormal S)
    (Q V : Subgroup S) (hne : V ≠ ⊥)
    (hformula : ∀ α : MulAut S, V ≤ invariantNormalKernel S α →
      invariantNormalKernel S α = ⨅ n : ℤ, Q.map ((α ^ n).toMonoidHom)) :
    ∃ α : MulAut S, ¬ V ≤ invariantNormalKernel S α := by
  classical
  by_contra hall
  push Not at hall
  let A : Subgroup S := ⨅ α : MulAut S, invariantNormalKernel S α
  have he : A = automorphismCore Q :=
    iInf_kernels_eq_automorphismCore Q (invariantNormalKernel S)
      (fun α => hformula α (hall α))
  have hc : A.Characteristic := by rw [he]; infer_instance
  have hn : (A.map S.subtype).Normal := by
    dsimp only [A]
    rw [Subgroup.map_iInf _ S.subtype_injective]
    exact normal_iInf_normal (fun α => invariantNormalKernel_image_normal S α)
  have hb := hno A hc hn
  apply hne
  apply le_bot_iff.mp
  rw [← hb]
  exact le_iInf hall

end NilesRankOneKernel
