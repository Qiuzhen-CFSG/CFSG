module
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Normalized prime projections in an actual central product

Pull back a prime subgroup through the multiplication map K times C onto
KC. Its kernel is central, so the prime core of the pullback maps onto the
original subgroup. Projecting that core onto C produces an actual prime
subgroup, invariant under every actor normalizing K, C and the original
subgroup. No splitting or triviality of the central intersection is required.

For a binary subgroup, unique maximal-two-local control kills a nontrivial
projection centralized by K. This is the projection step of Aschbacher--Smith
4.4.10(2), printed p.621, using only the residual's normalization.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A normalized prime subgroup of a central product has a normalized prime projection into either factor. -/
theorem exists_prime_projection_of_central_product (K C V F : Subgroup G)
    (hc : K ≤ centralizer (C : Set G)) (hV : IsPGroup p V)
    (hVK : V ≤ K ⊔ C) (hFK : F ≤ normalizer (K : Set G))
    (hFC : F ≤ normalizer (C : Set G)) (hFV : F ≤ normalizer (V : Set G)) :
    ∃ Q : Subgroup G, Q ≤ C ∧ IsPGroup p Q ∧ F ≤ normalizer (Q : Set G) ∧ V ≤ K ⊔ Q := by
  let f : K × C →* G := K.subtype.noncommCoprod C.subtype (fun k c =>
    (hc k.property c c.property).symm)
  have hr : f.range = K ⊔ C := by
    exact (MonoidHom.noncommCoprod_range _ _ _).trans (by rw [range_subtype,range_subtype])
  let U := V.comap f
  let q : U →* V := f.subgroupComap V
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨x,hx⟩ := (show (v:G)∈f.range by rw [hr]; exact hVK v.property)
    exact ⟨⟨x,by change f x∈V; rw [hx]; exact v.property⟩,Subtype.ext hx⟩
  have hk : q.ker ≤ center U := by
    intro x hx
    have he : ((x:K×C).1:G)*((x:K×C).2:G)=1 := congrArg Subtype.val hx
    have hleft : ((x:K×C).1:G)=((x:K×C).2:G)⁻¹ := eq_inv_of_mul_eq_one_left he
    have hright : ((x:K×C).2:G)=((x:K×C).1:G)⁻¹ := eq_inv_of_mul_eq_one_right he
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · change ((y:K×C).1:G)*((x:K×C).1:G)=((x:K×C).1:G)*((y:K×C).1:G)
      rw [hleft]
      exact (hc (y:K×C).1.property _ (C.inv_mem (x:K×C).2.property)).symm
    · change ((y:K×C).2:G)*((x:K×C).2:G)=((x:K×C).2:G)*((y:K×C).2:G)
      rw [hright]
      exact hc (K.inv_mem (x:K×C).1.property) _ (y:K×C).2.property
  have htop : pCore p V=⊤ := top_unique (le_sSup ⟨inferInstance,hV.to_subgroup ⊤⟩)
  have hmap : (pCore p U).map q=⊤ := (q.map_pCore_of_central_kernel hq hk).trans htop
  let P := U.pCoreIn p
  let snd : K×C →* G := C.subtype.comp (MonoidHom.snd K C)
  let Q := P.map snd
  have hQP : Q≤C := by
    rintro x ⟨y,hy,rfl⟩
    exact y.2.property
  refine ⟨Q,hQP,(isPGroup_pCoreIn p U).map snd,?_,?_⟩
  · intro a ha
    have hstable (a:G) (ha:a∈F) : ∀x∈Q,a*x*a⁻¹∈Q := by
      let e : K×C ≃* K×C :=
        (K.normalizerMonoidHom ⟨a,hFK ha⟩).prodCongr (C.normalizerMonoidHom ⟨a,hFC ha⟩)
      have hef (x:K×C) : f (e x)=a*f x*a⁻¹ := by
        change (a*(x.1:G)*a⁻¹)*(a*(x.2:G)*a⁻¹)=a*((x.1:G)*(x.2:G))*a⁻¹
        group
      have heU : U.map e.toMonoidHom=U := by
        apply le_antisymm
        · rintro x ⟨y,hy,rfl⟩
          change f (e y)∈V
          rw [hef]
          exact (mem_normalizer_iff.mp (hFV ha) _).mp hy
        · intro x hx
          refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
          change f (e.symm x)∈V
          apply (mem_normalizer_iff.mp (hFV ha) _).mpr
          rw [←hef,e.apply_symm_apply]
          exact hx
      have heP : P.map e.toMonoidHom=P := by
        change (U.pCoreIn p).map e.toMonoidHom=U.pCoreIn p
        rw [map_pCoreIn_of_injective p U _ e.injective,heU]
      rintro x ⟨y,hy,rfl⟩
      refine ⟨e y,?_,rfl⟩
      exact heP ▸ mem_map_of_mem e.toMonoidHom hy
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact hstable a ha x
    · intro hx
      have hh:=hstable a⁻¹ (F.inv_mem ha) _ hx
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
  · intro v hv
    have hvq : (⟨v,hv⟩:V)∈(pCore p U).map q := hmap ▸ mem_top _
    obtain ⟨x,hx,he⟩:=hvq
    have hp : (x:K×C)∈P := mem_map_of_mem U.subtype hx
    have hh : ((x:K×C).1:G)*((x:K×C).2:G)=v := congrArg Subtype.val he
    rw [←hh]
    exact (K⊔Q).mul_mem (mem_sup_left (x:K×C).1.property)
      (mem_sup_right (mem_map_of_mem snd hp))

/-- Unique two-local control removes the centralizer projection, placing the
original binary subgroup in the original factor. -/
theorem binary_subgroup_le_of_inner_product_uniqueness
    (K V F M : Subgroup G) (hV : IsPGroup 2 V)
    (hVF : V≤F) (hFK : F≤normalizer (K:Set G))
    (hFV : F≤normalizer (V:Set G))
    (hinner : F≤K⊔centralizer (K:Set G))
    (hunique : ∀N:Subgroup G, IsMaximalTwoLocal N→F≤N→N=M)
    (hout : ¬K≤M) : V≤K := by
  obtain ⟨Q,hQC,hQ,hFQ,hVQ⟩:=exists_prime_projection_of_central_product
    K (centralizer (K:Set G)) V F
    (le_centralizer_iff.mpr le_rfl) hV (hVF.trans hinner) hFK
    (hFK.trans (normalizer_le_normalizer_centralizer K)) hFV
  have hbot : Q=⊥ := by
    by_contra hn
    have hN:=normalizer_le_of_unique_maximalTwoLocal hunique hQ hn hFQ
    exact hout ((le_centralizer_iff.mp hQC).trans ((centralizer_le_normalizer _).trans hN))
  simpa only [hbot,sup_bot_eq] using hVQ
end Theory.GroupTheory
