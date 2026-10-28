module

public import Theory.GroupAction.OddCommutatorImage
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Transport of cyclic automorphism commutators

A genuine group equivalence transports the commutator with a cyclic group of
automorphisms, its two-core quotient and the quotient cardinality. It also
preserves the two-power condition, outerness and setwise subgroup stability.
This permits passage from a standard Sylow subgroup to any conjugate without
replacing the marked actor by an involution power.
Application: Aschbacher–Smith 13.8.20, printed p.954.
-/

public section

open Subgroup
namespace Theory.GroupAction.OddCommutatorImage
variable {G H : Type*} [Group G] [Group H]

theorem map_cyclic_commutator (e : G ≃* H) (α : MulAut G) (B : Subgroup G) :
    (commutatorSubgroup (zpowers α) G B).map e.toMonoidHom =
      commutatorSubgroup (zpowers (MulAut.congr e α)) H (B.map e.toMonoidHom) := by
  have he : (zpowers α).map (MulAut.congr e).toMonoidHom =
      zpowers (MulAut.congr e α) := MonoidHom.map_zpowers _ _
  rw [commutatorSubgroup,commutatorSubgroup,MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_,⟨β,b,hb,rfl⟩,rfl⟩
    have hβ : MulAut.congr e β ∈ zpowers (MulAut.congr e α) := by
      rw [← he]
      exact mem_map_of_mem _ β.property
    refine ⟨⟨MulAut.congr e β,hβ⟩,e b,mem_map_of_mem _ hb,?_⟩
    change e (b⁻¹ * β.val b) = (e b)⁻¹ * MulAut.congr e β.val (e b)
    simp [MulAut.congr]
  · rintro ⟨β,_,⟨b,hb,rfl⟩,rfl⟩
    have hβ := he.ge β.property
    obtain ⟨γ,hγ,hγβ⟩ := hβ
    refine ⟨b⁻¹ * γ b,⟨⟨γ,hγ⟩,b,hb,rfl⟩,?_⟩
    change e (b⁻¹ * γ b) = (e b)⁻¹ * β.val (e b)
    rw [← hγβ]
    simp [MulAut.congr]

noncomputable def cyclicCommutatorEquiv (e : G ≃* H) (α : MulAut G) (B : Subgroup G) :
    commutatorSubgroup (zpowers α) G B ≃*
      commutatorSubgroup (zpowers (MulAut.congr e α)) H (B.map e.toMonoidHom) :=
  (equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_cyclic_commutator e α B))

theorem card_cyclic_commutator_quotient (e : G ≃* H) (α : MulAut G) (B : Subgroup G) :
    let C := commutatorSubgroup (zpowers α) G B
    let C' := commutatorSubgroup (zpowers (MulAut.congr e α)) H (B.map e.toMonoidHom)
    Nat.card (C ⧸ pCore 2 C) = Nat.card (C' ⧸ pCore 2 C') := by
  let f := cyclicCommutatorEquiv e α B
  exact Nat.card_congr (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).toEquiv
end Theory.GroupAction.OddCommutatorImage

namespace Theory.GroupAction.OddCommutatorImage
variable {G H : Type*} [Group G] [Group H]

theorem map_congr_commutes (e : G ≃* H) (α : MulAut G) (B : Subgroup G) :
    (B.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom =
      (B.map α.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr]

theorem congr_symm_stabilizes [Finite G] (e : G ≃* H) (α : MulAut H)
    (U : Subgroup G) (S : Subgroup H) (hUS : U.map e.toMonoidHom = S)
    (hS : S.map α.toMonoidHom = S) :
    U.map (MulAut.congr e.symm α).toMonoidHom = U := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨u,hu,rfl⟩
    have hsu : α (e u) ∈ S := hS.le (mem_map_of_mem _ (hUS.le (mem_map_of_mem _ hu)))
    rw [← hUS] at hsu
    obtain ⟨v,hv,he⟩ := hsu
    have hh : MulAut.congr e.symm α u = v := by
      apply e.injective
      simpa [MulAut.congr] using he.symm
    exact hh.symm ▸ hv
  · rw [card_map_of_injective (MulAut.congr e.symm α).injective]

theorem congr_outer (e : G ≃* H) (α : MulAut G)
    (hα : α ∉ MulAut.innerSubgroup G) :
    MulAut.congr e α ∉ MulAut.innerSubgroup H := by
  intro h
  rw [← MulAut.map_innerSubgroup_congr e] at h
  obtain ⟨β,hβ,he⟩ := h
  exact hα ((MulAut.congr e).injective he ▸ hβ)

theorem congr_two_power (e : G ≃* H) (α : MulAut G)
    (hα : ∃ k : ℕ, α ^ (2 ^ k) = 1) :
    ∃ k : ℕ, (MulAut.congr e α) ^ (2 ^ k) = 1 := by
  obtain ⟨k,hk⟩ := hα
  exact ⟨k,by rw [← map_pow,hk,map_one]⟩

end Theory.GroupAction.OddCommutatorImage

namespace Theory.GroupAction.OddCommutatorImage
variable {G H : Type*} [Group G] [Group H]

/-- Invert the transport of a specified subgroup without rewriting its carrier. -/
theorem map_symm_of_map_eq (e : G ≃* H) (B : Subgroup G) (B' : Subgroup H)
    (h : B.map e.toMonoidHom = B') : B'.map e.symm.toMonoidHom = B := by
  rw [← h,Subgroup.map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  rw [he,Subgroup.map_id]

end Theory.GroupAction.OddCommutatorImage
