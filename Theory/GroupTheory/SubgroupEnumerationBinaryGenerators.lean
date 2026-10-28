module

public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Theory.Frattini.PGroup

/-!
# Generating families with maximal binary Schreier branches

A finite two-group has a generating family for which every nonzero binary
signature gives a maximal subgroup through the binary Schreier construction.
Lift a basis of the elementary abelian Frattini quotient. The lifts generate
by the Frattini nongenerating theorem, and every binary assignment extends to
a character into the group of order two. A nonzero assignment has a maximal
kernel; Schreier's lemma identifies the branch with that kernel.

The relative version applies to any subgroup of a finite two-group, including
the trivial subgroup (whose chosen family is empty).

Source: Burnside's basis argument, using the Frattini quotient results in
`Theory.Frattini.PGroup`, and Schreier's lemma as formalized in
`Theory.GroupTheory.SubgroupEnumerationBinary`.
-/

open scoped IsMulCommutative
namespace Theory.GroupTheory.SubgroupEnumeration

/-- A finite two-group admits a finite generating family on which every binary
assignment extends to a character into the group of order two. -/
public theorem exists_generators_with_binary_characters {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) :
    ∃ (n : ℕ) (s : Fin n → G), Subgroup.closure (Set.range s) = ⊤ ∧
      ∀ σ : Fin n → Bool, ∃ f : G →* Multiplicative (ZMod 2),
        ∀ i, f (s i) = Multiplicative.ofAdd (if σ i then 1 else 0) := by
  classical
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  let Q := G ⧸ frattini G
  let : IsElementaryAbelian 2 Q := isElementaryAbelian_quotient_frattini
  let q : G →* Q := QuotientGroup.mk' (frattini G)
  let B := Module.Basis.ofVectorSpace (ZMod 2) (Additive Q)
  let := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive Q))
  let n := Fintype.card (Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive Q))
  let b : Module.Basis (Fin n) (ZMod 2) (Additive Q) := B.reindex (Fintype.equivFin _)
  have hlift (i : Fin n) : ∃ x : G, q x = (b i).toMul :=
    QuotientGroup.mk'_surjective (frattini G) _
  choose s hs using hlift
  refine ⟨n, s, ?_, ?_⟩
  · let H := Subgroup.closure (Set.range s)
    let W := AddSubgroup.toZModSubmodule 2 (H.map q).toAddSubgroup
    have hW : (⊤ : Submodule (ZMod 2) (Additive Q)) ≤ W := by
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change (b i).toMul ∈ H.map q
      exact ⟨s i, Subgroup.subset_closure ⟨i, rfl⟩, hs i⟩
    have hmap : H.map q = ⊤ := by
      apply top_unique
      intro x _
      exact hW (show Additive.ofMul x ∈ (⊤ : Submodule (ZMod 2) (Additive Q)) from trivial)
    apply frattini_nongenerating
    have he := Subgroup.comap_map_eq q H
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at he
    exact he.symm
  · intro σ
    let l : Additive Q →ₗ[ZMod 2] ZMod 2 := b.constr (ZMod 2) (fun i => if σ i then 1 else 0)
    refine ⟨l.toAddMonoidHom.toMultiplicativeRight.comp q, ?_⟩
    intro i
    change Multiplicative.ofAdd (l (Additive.ofMul (q (s i)))) = _
    rw [hs i]
    exact congrArg Multiplicative.ofAdd (b.constr_basis (ZMod 2) _ i)

private theorem binary_kernel_coatom {G : Type*} [Group G]
    (f : G →* Multiplicative (ZMod 2)) (x : G)
    (hx : f x = Multiplicative.ofAdd 1) : IsCoatom f.ker := by
  have hf : Function.Surjective f := by
    intro y
    have hy : y = 1 ∨ y = Multiplicative.ofAdd 1 := by
      change y.toAdd = 0 ∨ y.toAdd = 1
      exact (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) y.toAdd
    rcases hy with rfl | rfl
    · exact ⟨1, f.map_one⟩
    · exact ⟨x, hx⟩
  have hbot : IsCoatom (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
    let : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨by simpa [Nat.card_eq_fintype_card] using Nat.prime_two⟩
    refine ⟨bot_ne_top, ?_⟩
    intro H hH
    exact (Subgroup.eq_bot_or_eq_top_of_prime_card H).resolve_left hH.ne'
  exact Subgroup.isCoatom_comap_of_surjective hf hbot

/-- Basis lifts from the Frattini quotient give only maximal nonzero binary
Schreier branches. -/
public theorem exists_binarySchreier_generators_top {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) :
    ∃ (n : ℕ) (s : Fin n → G), Subgroup.closure (Set.range s) = ⊤ ∧
      ∀ (σ : Fin n → Bool) (j : Fin n), σ j = true →
        Subgroup.closure (Set.range (binarySchreierGenerator s (s j) σ)) ⋖ ⊤ := by
  obtain ⟨n, s, hs, hchars⟩ := exists_generators_with_binary_characters hG
  refine ⟨n, s, hs, ?_⟩
  intro σ j hj
  obtain ⟨f, hf⟩ := hchars σ
  have hjf : f (s j) = Multiplicative.ofAdd 1 := by simpa [hj] using hf j
  have hmax := binary_kernel_coatom f (s j) hjf
  have hsig : ∀ i, σ i = true ↔ s i ∉ f.ker := by
    intro i
    simp only [MonoidHom.mem_ker, hf i]
    cases σ i <;> simp
  rw [binarySchreier_eq_relative le_top
    (by simpa using hG.index_of_isCoatom f.ker hmax) s hs (s j) (by trivial)
    ((hsig j).mp hj) σ hsig]
  exact hmax.covBy_top

/-- Every subgroup of a finite two-group has a finite generating family whose
nonzero binary Schreier branches are maximal in that subgroup. -/
public theorem exists_binarySchreier_generators {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (K : Subgroup G) :
    ∃ (n : ℕ) (s : Fin n → G), Subgroup.closure (Set.range s) = K ∧
      ∀ (σ : Fin n → Bool) (j : Fin n), σ j = true →
        Subgroup.closure (Set.range (binarySchreierGenerator s (s j) σ)) ⋖ K := by
  obtain ⟨n, s, hs, hbranches⟩ := exists_binarySchreier_generators_top (hG.to_subgroup K)
  refine ⟨n, K.subtype ∘ s, ?_, ?_⟩
  · rw [Set.range_comp, ← MonoidHom.map_closure, hs]
    exact (MonoidHom.range_eq_map K.subtype).symm.trans K.range_subtype
  · intro σ j hj
    have hfun : K.subtype ∘ binarySchreierGenerator s (s j) σ =
        binarySchreierGenerator (K.subtype ∘ s) ((K.subtype ∘ s) j) σ := by
      funext ⟨b, i⟩
      cases b <;> cases hh : σ i <;> simp [binarySchreierGenerator, hh]
    rw [← hfun, Set.range_comp, ← MonoidHom.map_closure]
    let e : Subgroup K ≃o Set.Iic K := Subgroup.MapSubtype.orderIso K
    exact Set.Iic.isCoatom_iff.mp
      ((e.isCoatom_iff _).mpr
        (hbranches σ j hj).isCoatom)

end Theory.GroupTheory.SubgroupEnumeration
