module
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Mathlib.GroupTheory.Index

/-!
# Commuting intersections through a small central kernel

Suppose distinct conjugates of V commute whenever they meet nontrivially,
and the image of V under a central quotient is self-centralizing. If an
image element centralizes the image of U ≤ V, with U larger than the kernel,
its central commutator homomorphism on U has a nontrivial kernel. That fixed
element gives an intersection of V with its conjugate, forcing the quotient
element to normalize the image of V.

The second theorem transports the intersection property through a literal
injective group map. The source application is the original unitary Rudvalis
component, using 13.3.19(1), the marked three-space and the multiplier bound.
Source: Aschbacher--Smith 4.2.13 and 13.3.19, pp.611--612,895--896.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

/-- A central quotient centralizer forces a normalizer when the original
module has commuting intersecting conjugates and the kernel is smaller
than the fixed source subgroup. -/
theorem map_mem_normalizer_of_commuting_intersections
    (f : G →* K) (hker : f.ker ≤ center G)
    (V U : Subgroup G) (hUV : U ≤ V) (hcard : Nat.card f.ker < Nat.card U)
    (hinter : ∀ x : G, V ⊓ V.map (MulAut.conj x).toMonoidHom ≠ ⊥ →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set G))
    (hself : centralizer (V.map f : Set K) ≤ V.map f)
    (x : G) (hx : f x ∈ centralizer (U.map f : Set K)) :
    f x ∈ normalizer (V.map f : Set K) := by
  have hc : f.ker ≤ centralizer (U : Set G) := hker.trans (center_le_centralizer _)
  have hd (u : G) (hu : u ∈ U) : ⁅x,u⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.mp hx (f u) (mem_map_of_mem f hu)).symm
  let d := centralCommutatorHom U f.ker hc x hd
  have hdn : d.ker ≠ ⊥ := by
    intro he
    have hi := (MonoidHom.ker_eq_bot_iff d).mp he
    exact (not_le_of_gt hcard) (Nat.card_le_card_of_injective d hi)
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hdn
  have hu1 : ((u : U) : G) ≠ 1 := fun he => hu (Subtype.ext (Subtype.ext he))
  have hv : ((u : U) : G) ∈ V := hUV u.val.property
  have hcomm : Commute x ((u : U) : G) := by
    have he := congrArg Subtype.val (MonoidHom.mem_ker.mp u.property)
    change ⁅x,((u : U) : G)⁆ = 1 at he
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  have hconj : MulAut.conj x ((u : U) : G) = ((u : U) : G) := by
    change x * ((u : U) : G) * x⁻¹ = ((u : U) : G)
    rw [hcomm.eq,mul_inv_cancel_right]
  have hn : V ⊓ V.map (MulAut.conj x).toMonoidHom ≠ ⊥ := by
    intro he
    apply hu1
    exact mem_bot.mp (he ▸ (show ((u : U) : G) ∈ V ⊓ V.map (MulAut.conj x).toMonoidHom from
      ⟨hv,⟨u,hv,hconj⟩⟩))
  have hmaps : (V.map (MulAut.conj x).toMonoidHom).map f =
      (V.map f).map (MulAut.conj (f x)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext v
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  have hbound : (V.map (MulAut.conj x).toMonoidHom).map f ≤ centralizer (V.map f : Set K) := by
    rintro y ⟨v,hv,rfl⟩ z ⟨w,hw,rfl⟩
    simpa only [map_mul] using congrArg f (hinter x hn hv w hw)
  rw [hmaps] at hbound
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge (hbound.trans hself)
  rw [card_map_of_injective (f := (MulAut.conj (f x)).toMonoidHom) (MulAut.conj (f x)).injective]

omit [Finite G] [Finite K] in
/-- Commuting intersections restrict along the literal injective group map. -/
theorem commuting_intersections_of_injective_map
    (i : G →* K) (hi : Function.Injective i) (V : Subgroup G)
    (hinter : ∀ x : K, V.map i ⊓ (V.map i).map (MulAut.conj x).toMonoidHom ≠ ⊥ →
      (V.map i).map (MulAut.conj x).toMonoidHom ≤ centralizer (V.map i : Set K)) :
    ∀ x : G, V ⊓ V.map (MulAut.conj x).toMonoidHom ≠ ⊥ →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set G) := by
  intro x hx
  have hmaps : (V.map (MulAut.conj x).toMonoidHom).map i =
      (V.map i).map (MulAut.conj (i x)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext v
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hx
  have hiu : i u ≠ 1 := fun he => hu (Subtype.ext (hi (he.trans (map_one i).symm)))
  have hn : V.map i ⊓ (V.map i).map (MulAut.conj (i x)).toMonoidHom ≠ ⊥ := by
    intro he
    apply hiu
    apply mem_bot.mp
    rw [←he]
    exact ⟨mem_map_of_mem i u.property.1,hmaps ▸ mem_map_of_mem i u.property.2⟩
  intro v hv w hw
  apply hi
  simpa only [map_mul] using hinter (i x) hn
    (hmaps ▸ mem_map_of_mem i hv) (i w) (mem_map_of_mem i hw)

end Theory.GroupTheory
