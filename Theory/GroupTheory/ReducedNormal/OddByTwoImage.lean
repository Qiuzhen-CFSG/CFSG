module
public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Reduced subgroups in odd-by-two action images

Let an actual centralizer quotient act on a normal elementary abelian
2-subgroup. If that quotient has a normal subgroup of odd order and a
2-group quotient, its two-core centralizes the odd subgroup. The P × Q
fixed-space kernel theorem shows that the vectors fixed by the two-core
have precisely that two-core as kernel. Transferring these vectors to the
original elementary subgroup therefore gives a reduced subgroup and keeps
its exact centralizer visible.

Source application: the minimal-parabolic step of Aschbacher–Smith 14.1.4,
using the solvable Thompson image from B.1.8 and B.2.16.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G A : Type*} [Group G] [Group A] [Finite G] [Finite A]

theorem exists_reduced_le_of_odd_by_two_image
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup A) [L.Normal] (hodd : Odd (Nat.card L))
    (hquot : IsPGroup 2 (A ⧸ L)) :
    ∃ W : Subgroup G, W ≤ U ∧ IsPReduced 2 W ∧
      centralizer (W : Set G) = (pCore 2 A).comap q := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let Q := pCore 2 A
  let F := fixedSpace ρ Q
  let D : Subgroup U := F.toAddSubgroup.toSubgroup'
  let W := D.map U.subtype
  have hWU : W ≤ U := map_subtype_le D
  have hnorm : W.Normal := by
    constructor
    rintro _ ⟨v,hv,rfl⟩ g
    let w : U := ⟨g * (v : G) * g⁻¹,(inferInstance : U.Normal).conj_mem _ v.property g⟩
    refine ⟨w,?_,rfl⟩
    have hh := ((fixedSpace_stable_of_normal ρ Q (mem_top (q g)))
      (Additive.ofMul v)).mpr (show Additive.ofMul v ∈ F from hv)
    have he : (ρ (q g) (Additive.ofMul v)).toMul = w := by
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply U q hq hker g _
    change (ρ (q g) (Additive.ofMul v)).toMul ∈ D at hh
    rwa [he] at hh
  let := hnorm
  have hcomm : Q ≤ centralizer (L : Set A) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    have hc : (Nat.card Q).Coprime (Nat.card L) := by
      change (Nat.card (pCore 2 A)).Coprime _
      rw [hn]
      exact hodd.coprime_two_left.pow_left n
    exact commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hc))
  have hfixed : subspaceKernel ρ F ⊤ = Q :=
    fixedSpace_kernel_eq_twoCore_of_centralizes ρ
      (NormalElementaryQuotient.representation_injective U q hq hker) L hquot hcomm
  have hcentral : centralizer (W : Set G) = (subspaceKernel ρ F ⊤).comap q := by
    ext g
    constructor
    · intro hg
      refine ⟨mem_top _,?_⟩
      intro v hv
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply U q hq hker]
      exact (mul_inv_eq_iff_eq_mul).mpr (hg v.toMul (mem_map_of_mem U.subtype hv)).symm
    · rintro ⟨_,hg⟩ w ⟨v,hv,rfl⟩
      have he := congrArg (fun x : Additive U => (x.toMul : G))
        (hg (Additive.ofMul v) hv)
      rw [NormalElementaryQuotient.representation_apply U q hq hker] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rw [hfixed] at hcentral
  refine ⟨W,hWU,⟨hnorm,IsElementaryAbelian.of_le hWU,?_⟩,hcentral⟩
  let f := (QuotientGroup.mk' Q).comp q
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective Q).comp hq
  have hfker : f.ker = centralizer (W : Set G) := by
    rw [hcentral]
    ext g
    exact QuotientGroup.eq_one_iff (q g)
  let e := (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso 2 e]
  exact pCore_quotient_pCore_eq_bot 2

end Theory.GroupTheory
