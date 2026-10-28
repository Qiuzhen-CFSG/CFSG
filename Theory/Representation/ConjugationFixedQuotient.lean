module
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.TypeTags.Hom
/-!
# The fixed quotient bounds the literal centralizer index

An equivariant surjection sends centralizing elements to fixed vectors.
Composing with the fixed quotient therefore produces a surjective group
map whose kernel contains the original centralizer. Index monotonicity
supplies the bound without assuming that the ambient group is finite.
-/

public section
noncomputable section
open Subgroup
namespace Representation
theorem fixed_quotient_card_le_centralizer_index
    {G D V : Type*} [Group G] [Group D] [AddCommGroup V] [Module (ZMod 2) V] (U A : Subgroup G) [Finite U]
    (hn : A ≤ normalizer (U : Set G))
    (π : U →* Multiplicative V) (hp : Function.Surjective π)
    (ρ : Representation (ZMod 2) D V) (α : A →* D)
    (hact : ∀ (a : A) (u : U),
      π ⟨a.val*u.val*a.val⁻¹,(mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ =
        Multiplicative.ofAdd (ρ (α a) (π u).toAdd)) :
    Nat.card (V ⧸ BinaryOffender.fixedSpace ρ α.range) ≤ (centralizer (A : Set G)).relIndex U := by
  let f : U →* Multiplicative (V ⧸ BinaryOffender.fixedSpace ρ α.range) :=
    (BinaryOffender.fixedSpace ρ α.range).mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := (BinaryOffender.fixedSpace ρ α.range).mkQ_surjective v.toAdd
    obtain ⟨u,hu⟩ := hp (Multiplicative.ofAdd w)
    refine ⟨u,?_⟩
    change Multiplicative.ofAdd ((BinaryOffender.fixedSpace ρ α.range).mkQ (π u).toAdd)=v
    rw [hu,toAdd_ofAdd,hw,ofAdd_toAdd]
  have hker : (centralizer (A : Set G)).subgroupOf U ≤ f.ker := by
    intro u hu
    change (BinaryOffender.fixedSpace ρ α.range).mkQ (π u).toAdd=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rintro ⟨g,⟨a,rfl⟩⟩
    have hconj : a.val*u.val*a.val⁻¹=u.val := by
      have hc : a.val*u.val=u.val*a.val := hu a.val a.property
      rw [hc,mul_inv_cancel_right]
    have hh := hact a u
    have he : (⟨a.val*u.val*a.val⁻¹,
      (mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ : U)=u := Subtype.ext hconj
    rw [he] at hh
    exact congrArg Multiplicative.toAdd hh.symm
  have hidx : f.ker.index = Nat.card (V ⧸ BinaryOffender.fixedSpace ρ α.range) := by
    rw [index_ker,f.range_eq_top_of_surjective hf]
    exact Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative (V ⧸ BinaryOffender.fixedSpace ρ α.range))) ≃* _).toEquiv
  rw [←hidx]
  change f.ker.index ≤ ((centralizer (A : Set G)).subgroupOf U).index
  have h := relIndex_le_of_le_left (L := (⊤ : Subgroup U)) hker index_ne_zero_of_finite
  simpa only [relIndex_top_right] using h
end Representation
