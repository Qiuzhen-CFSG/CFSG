module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.Nonfusion

/-!
# Four fixed points for every order-three element of the E-normalizer

In the order-168 quotient branch, the actual normalizer N(E) has order
2688 = 128 · 3 · 7. Thus the cyclic subgroups of any order-three element
and of the marked coordinate actor c are Sylow 3-subgroups of N(E).
Sylow conjugacy transports their centralizers on E. Kernel reduction in
the given twisted model counts exactly four vectors fixed by c.

The proof uses centralizers of cyclic subgroups, so it is independent of
which generator Sylow conjugacy selects. It requires neither simplicity
nor fusion or normalizer information about the second elementary group F.
The construction of an actor preserving E ∩ F remains with the caller.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.7: conjugacy of Q₁
with Q in N(E) gives a four-group C_E(Q₁).
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))
local instance : DecidablePred (· ∈ centralizer ({c} : Set TwistedModel)) := fun x =>
  decidable_of_iff (x * c = c * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ (modelE ⊓ centralizer ({c} : Set TwistedModel) :
    Subgroup TwistedModel)) := fun x =>
  inferInstanceAs (Decidable (x ∈ modelE ∧ x ∈ centralizer ({c} : Set TwistedModel)))

private theorem model_c_fixed_card :
    Nat.card (modelE ⊓ centralizer ({c} : Set TwistedModel) : Subgroup TwistedModel) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem map_inf_centralizer_singleton {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) (x : A) :
    (H ⊓ centralizer ({x} : Set A)).map f =
      H.map f ⊓ centralizer ({f x} : Set B) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
    refine ⟨mem_map_of_mem f hz, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hzx)
  · rintro ⟨⟨z, hz, rfl⟩, hzx⟩
    refine ⟨z, ⟨hz, mem_centralizer_singleton_iff.mpr (hf ?_)⟩, rfl⟩
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hzx

private theorem three_zpowers_conjugate {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 2688) (x y : H) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ g : H, (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers y := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hsyl : ∀ t : H, orderOf t = 3 →
      ∃ P : Sylow 3 H, (P : Subgroup H) = zpowers t := by
    intro t ht
    refine ⟨Sylow.ofCard (zpowers t) ?_, rfl⟩
    rw [Nat.card_zpowers, ht, hcard]
    decide +kernel
  obtain ⟨P, hP⟩ := hsyl x hx
  obtain ⟨Q, hQ⟩ := hsyl y hy
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨g, ?_⟩
  have he := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul, hP, hQ, Subgroup.pointwise_smul_def] at he
  exact he

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem c_fixed_card :
    Nat.card (E D k ⊓ centralizer ({into D k c} : Set G) : Subgroup G) = 4 := by
  rw [← modelE_map D k, ← map_inf_centralizer_singleton (into D k) (into_injective D k),
    card_map_of_injective (into_injective D k)]
  exact model_c_fixed_card

/-- Every order-three element of the actual E-normalizer fixes a four-group
on E in the order-168 quotient branch. The element is supplied explicitly. -/
public theorem l27_three_fixed_card (h168 : Nat.card (eNormalizerQuotient D k) = 168)
    (q : G) (hE : q ∈ normalizer (E D k : Set G)) (ho : orderOf q = 3) :
    Nat.card (E D k ⊓ centralizer ({q} : Set G) : Subgroup G) = 4 := by
  let N := normalizer (E D k : Set G)
  let cN : N := ⟨into D k c, centralizer_le_normalizer_E D k (k c).property⟩
  let qN : N := ⟨q, hE⟩
  have hc : orderOf cN = 3 := by
    rw [Subgroup.orderOf_mk, orderOf_injective (into D k) (into_injective D k)]
    exact actor_orders.2.2.1
  obtain ⟨g, hg⟩ := three_zpowers_conjugate (eNormalizer_card_of_168 D k h168)
    cN qN hc (by simpa only [qN, Subgroup.orderOf_mk] using ho)
  have hamb := congrArg (Subgroup.map N.subtype) hg
  simp only [MonoidHom.map_zpowers] at hamb
  change zpowers ((g : G) * into D k c * (g : G)⁻¹) = zpowers q at hamb
  have hcentral : centralizer ({(g : G) * into D k c * (g : G)⁻¹} : Set G) =
      centralizer ({q} : Set G) := by
    have he := congrArg (fun H : Subgroup G => centralizer (H : Set G)) hamb
    simpa only [zpowers_eq_closure, centralizer_closure] using he
  have hmap := map_inf_centralizer_singleton (MulAut.conj (g : G)).toMonoidHom
    (MulAut.conj (g : G)).injective (E D k) (into D k c)
  have hEn : (E D k).map (MulAut.conj (g : G)).toMonoidHom = E D k :=
    mem_normalizer_iff_map_conj_eq.mp g.property
  rw [hEn] at hmap
  change (E D k ⊓ centralizer ({into D k c} : Set G)).map
    (MulAut.conj (g : G)).toMonoidHom =
    E D k ⊓ centralizer ({(g : G) * into D k c * (g : G)⁻¹} : Set G) at hmap
  rw [hcentral] at hmap
  rw [← hmap, card_map_of_injective (MulAut.conj (g : G)).injective]
  exact c_fixed_card D k

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
