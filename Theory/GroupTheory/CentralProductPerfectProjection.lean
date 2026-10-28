module
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.CentralProductPrimeProjection
public import Theory.GroupTheory.CComponent.Basic

/-!
# Perfect projections in a central product

Pull the original perfect subgroup back through the multiplication map from
the two commuting factors. The kernel is central, so the derived subgroup of
the pullback is perfect and still maps onto the original subgroup. Its actual
coordinate images are perfect, and characteristic transport retains every
actor normalizing the factors and the original subgroup.
Source: Aschbacher–Smith, C.3.2, printed p.149.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A perfect subgroup of a commuting product has perfect coordinate images.
The coordinates retain their original factors and multiply onto the subgroup. -/
theorem exists_perfect_projections_of_central_product (K C L : Subgroup G)
    (hc : K ≤ centralizer (C : Set G)) [Group.IsPerfect L] (hL : L ≤ K ⊔ C) :
    ∃ P Q : Subgroup G, P ≤ K ∧ Q ≤ C ∧ Group.IsPerfect P ∧ Group.IsPerfect Q ∧
      L ≤ P ⊔ Q ∧ P ≤ L ⊔ Q ∧
      (∀ A : Subgroup G, A ≤ normalizer (K : Set G) → A ≤ normalizer (C : Set G) →
        A ≤ normalizer (L : Set G) → A ≤ normalizer (P : Set G)) := by
  let f : K × C →* G := K.subtype.noncommCoprod C.subtype (fun k c =>
    (hc k.property c c.property).symm)
  have hr : f.range = K ⊔ C := by
    exact (MonoidHom.noncommCoprod_range _ _ _).trans (by rw [range_subtype,range_subtype])
  let U := L.comap f
  let q : U →* L := f.subgroupComap L
  have hq : Function.Surjective q := by
    intro l
    obtain ⟨x,hx⟩ := (show (l:G)∈f.range by rw [hr]; exact hL l.property)
    exact ⟨⟨x,by change f x∈L; rw [hx]; exact l.property⟩,Subtype.ext hx⟩
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
  let D := _root_.commutator U
  let := PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center q hq hk
  let fst : U →* G := K.subtype.comp ((MonoidHom.fst K C).comp U.subtype)
  let snd : U →* G := C.subtype.comp ((MonoidHom.snd K C).comp U.subtype)
  let P := D.map fst
  let Q := D.map snd
  have hmap : D.map q = ⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hq]
    exact commutator_eq_self (H := ⊤)
  refine ⟨P,Q,?_,?_,Group.IsPerfect.map fst,Group.IsPerfect.map snd,?_,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    exact (u:K×C).1.property
  · rintro _ ⟨u,hu,rfl⟩
    exact (u:K×C).2.property
  · intro l hl
    obtain ⟨u,hu,he⟩ := (show (⟨l,hl⟩:L) ∈ D.map q by rw [hmap]; trivial)
    have hh : fst u * snd u = l := congrArg Subtype.val he
    rw [←hh]
    exact mul_mem (mem_sup_left (mem_map_of_mem fst hu)) (mem_sup_right (mem_map_of_mem snd hu))
  · rintro _ ⟨u,hu,rfl⟩
    have hf : fst u * snd u ∈ L := u.property
    have he : fst u = (fst u * snd u) * (snd u)⁻¹ := by group
    rw [he]
    exact mul_mem (mem_sup_left hf) (mem_sup_right (Q.inv_mem (mem_map_of_mem snd hu)))
  · intro A hAK hAC hAL a ha
    have hstable (a:G) (ha:a∈A) : ∀x∈P,a*x*a⁻¹∈P := by
      let e : K×C ≃* K×C :=
        (K.normalizerMonoidHom ⟨a,hAK ha⟩).prodCongr (C.normalizerMonoidHom ⟨a,hAC ha⟩)
      have hef (x:K×C) : f (e x)=a*f x*a⁻¹ := by
        change (a*(x.1:G)*a⁻¹)*(a*(x.2:G)*a⁻¹)=a*((x.1:G)*(x.2:G))*a⁻¹
        group
      have heU : U.map e.toMonoidHom=U := by
        apply le_antisymm
        · rintro x ⟨y,hy,rfl⟩
          change f (e y)∈L
          rw [hef]
          exact (mem_normalizer_iff.mp (hAL ha) _).mp hy
        · intro x hx
          refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
          change f (e.symm x)∈L
          apply (mem_normalizer_iff.mp (hAL ha) _).mpr
          rw [←hef,e.apply_symm_apply]
          exact hx
      let eU : U ≃* U := (e.subgroupMap U).trans (MulEquiv.subgroupCongr heU)
      have heD : D.map eU.toMonoidHom = D := by
        change (_root_.commutator U).map eU.toMonoidHom = _root_.commutator U
        rw [map_commutator_eq,MonoidHom.range_eq_top.mpr eU.surjective]
        rfl
      rintro x ⟨u,hu,rfl⟩
      refine ⟨eU u,heD ▸ mem_map_of_mem eU.toMonoidHom hu,?_⟩
      rfl
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact hstable a ha x
    · intro hx
      have hh:=hstable a⁻¹ (A.inv_mem ha) _ hx
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
end Theory.GroupTheory
