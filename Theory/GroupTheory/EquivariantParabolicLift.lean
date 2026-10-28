module
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Full preimages of invariant model subgroups

A surjective equivariant homomorphism transports properness, generation and
normalization of model parabolics to their original component. This isolates
the literal quotient-map transport used in Aschbacher–Smith, 15.3.20.
-/

public section
open Subgroup
namespace Subgroup.EquivariantLift
variable {G H : Type*} [Group G] [Group H] (L : Subgroup G) (q : L →* H)

/-- Full preimage of a marked model subgroup in its original component. -/
def lift (P : Subgroup H) : Subgroup G := (P.comap q).map L.subtype

theorem lift_le (P : Subgroup H) : lift L q P ≤ L := map_subtype_le _
theorem lift_top : lift L q ⊤ = L := by
  rw [lift,comap_top,←MonoidHom.range_eq_map,range_subtype]
theorem lift_sup (hq : Function.Surjective q) (P Q : Subgroup H) :
    lift L q (P ⊔ Q) = lift L q P ⊔ lift L q Q := by
  rw [lift,←comap_sup_eq _ _ _ hq,map_sup]
  rfl
theorem lift_lt (hq : Function.Surjective q) {P : Subgroup H} (hp : P ≠ ⊤) :
    lift L q P < L := by
  apply lt_of_le_of_ne (lift_le L q P)
  intro he
  have hh := congrArg (fun D : Subgroup G => D.subgroupOf L) he
  change ((P.comap q).map L.subtype).comap L.subtype = L.subgroupOf L at hh
  rw [comap_map_eq_self_of_injective L.subtype_injective,subgroupOf_self] at hh
  exact hp ((comap_injective hq) (hh.trans (comap_top q).symm))

theorem le_lift {D : Subgroup G} (hD : D ≤ L) {P : Subgroup H}
    (hd : (D.subgroupOf L).map q ≤ P) : D ≤ lift L q P := by
  intro d hdD
  exact ⟨⟨d,hD hdD⟩,hd ⟨⟨d,hD hdD⟩,hdD,rfl⟩,rfl⟩

/-- A subgroup containing the kernel is recovered from its actual image. -/
theorem lift_map_subgroupOf (D : Subgroup G) (hD : D ≤ L)
    (hk : q.ker ≤ D.subgroupOf L) :
    lift L q ((D.subgroupOf L).map q) = D := by
  rw [lift,comap_map_eq_self hk,map_subgroupOf_eq_of_le hD]

variable {A : Subgroup G} (hn : A ≤ normalizer (L : Set G))
    (α : A →* MulAut H)
    (heq : ∀ (a : A) (l : L),
      q (L.normalizerMonoidHom (inclusion hn a) l) = α a (q l))

include hn heq in
/-- Equivariance transports subgroup invariance through the literal quotient map. -/
theorem map_invariant {D : Subgroup G} (hD : A ≤ normalizer (D : Set G)) (a : A) :
    ((D.subgroupOf L).map q).map (α a).toMonoidHom = (D.subgroupOf L).map q := by
  apply le_antisymm
  · rintro x ⟨y,⟨l,hl,rfl⟩,rfl⟩
    refine ⟨L.normalizerMonoidHom (inclusion hn a) l,?_,heq a l⟩
    exact (hD a.property l.val).mp hl
  · rintro x ⟨l,hl,rfl⟩
    let k := L.normalizerMonoidHom (inclusion hn a⁻¹) l
    have hk : k ∈ D.subgroupOf L := (hD (A.inv_mem a.property) l.val).mp hl
    refine ⟨q k,⟨k,hk,rfl⟩,?_⟩
    rw [show q k = α a⁻¹ (q l) from heq a⁻¹ l,map_inv]
    exact (α a).apply_symm_apply _

include hn heq in
/-- Fixing a model parabolic normalizes its full preimage in the original group. -/
theorem normalizes_lift {P : Subgroup H}
    (hP : ∀ a : A, P.map (α a).toMonoidHom = P) :
    A ≤ normalizer (lift L q P : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  obtain ⟨l,hl,rfl⟩ := hx
  let a₀ : A := ⟨a,ha⟩
  refine ⟨L.normalizerMonoidHom (inclusion hn a₀) l,?_,rfl⟩
  change q (L.normalizerMonoidHom (inclusion hn a₀) l) ∈ P
  rw [heq]
  exact hP a₀ ▸ mem_map_of_mem (α a₀).toMonoidHom hl
end Subgroup.EquivariantLift
