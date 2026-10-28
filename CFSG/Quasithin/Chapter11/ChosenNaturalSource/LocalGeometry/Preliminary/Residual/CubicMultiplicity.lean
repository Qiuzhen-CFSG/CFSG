module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicDouble
public import Mathlib.Algebra.Ring.GeomSum
/-!
# Cubic containment for natural multiplicity prime to three

In s copies of a simple module with endomorphism field of order q, the
actual simple constituents number 1 + q + ⋯ + q^(s-1). If q is congruent
to one modulo three, this count is congruent to s. A cubic actor therefore
fixes a natural constituent whenever three does not divide s. Restricting
to its stabilizer supplies the same natural action and component quotient
as in CubicDouble, so the rank-two containment theorem applies with the
full SL₃ center and arbitrary prime-to-three covering kernel retained.

This extends the constituent-selection step of Aschbacher--Smith A.3.19,
printed pp.54--55. Multiplicity.Cubic applies it to the original chosen
module in 11.0.4, printed p.760. Its conclusion narrows the outstanding
source obligation to multiplicities divisible by three; it does not prove
that those multiplicities are absent. Final discharge remains with
qt-d-1222-natural-preliminary-source and its local-geometry consumer.
-/

public noncomputable section
open Representation
open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
section Ring
variable {A S V : Type*} [Ring A] [AddCommGroup S] [Module A S]
  [AddCommGroup V] [Module A V] [IsSimpleModule A S]

private theorem card_nonzero_copies (X : Type*) [Zero X] [Finite X] :
    Nat.card {x : X // x ≠ 0} = Nat.card X - 1 := by
  classical
  let := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_unique (α := {x : X // x = 0}), Nat.card_eq_fintype_card]

private def nonzeroEndCopiesEquiv : {f : Module.End A S // f ≠ 0} ≃ (S ≃ₗ[A] S) where
  toFun f := LinearEquiv.ofBijective f.val (LinearMap.bijective_of_ne_zero f.property)
  invFun e := by
    let : Nontrivial S := IsSimpleModule.nontrivial A S
    exact ⟨e.toLinearMap, LinearMap.ne_zero_of_injective e.injective⟩
  left_inv f := rfl
  right_inv e := by ext; rfl

/-- Count all simple constituents using their nonzero parametrizing maps. -/
theorem card_copies_repeated [Finite S] [Finite V] {s : ℕ}
    (e : V ≃ₗ[A] (Fin s → S)) :
    Nat.card (SimpleCopies.Copies A S V) =
      ∑ i ∈ Finset.range s, Nat.card (Module.End A S) ^ i := by
  let : Nontrivial S := IsSimpleModule.nontrivial A S
  let : Finite (Module.End A S) := Finite.of_injective _ DFunLike.coe_injective
  let : Finite (S →ₗ[A] V) := Finite.of_injective _ DFunLike.coe_injective
  have hE : 1 < Nat.card (Module.End A S) := Finite.one_lt_card
  let t : (S →ₗ[A] V) ≃ (Fin s → Module.End A S) := {
    toFun f i := (LinearMap.proj i).comp (e.toLinearMap.comp f)
    invFun f := e.symm.toLinearMap.comp (LinearMap.pi f)
    left_inv f := by ext v; exact e.symm_apply_apply (f v)
    right_inv f := by ext i v; exact congrFun (e.apply_symm_apply (fun i => f i v)) i }
  have hmaps : Nat.card (S →ₗ[A] V) = Nat.card (Module.End A S) ^ s := by
    rw [Nat.card_congr t, Nat.card_fun, Nat.card_fin]
  have hauto : Nat.card (S ≃ₗ[A] S) = Nat.card (Module.End A S) - 1 := by
    rw [← Nat.card_congr nonzeroEndCopiesEquiv]
    exact card_nonzero_copies _
  have h := SimpleCopies.card_nonzeroMaps (A := A) (S := S) (V := V)
  rw [card_nonzero_copies, hmaps, hauto] at h
  exact Nat.mul_right_cancel (by omega) (h.symm.trans
    (geom_sum_mul_of_one_le (by omega : 1 ≤ Nat.card (Module.End A S)) s).symm)

/-- Every simple constituent of a repeated simple module has the original type. -/
theorem isotypic_of_repeated {s : ℕ} (e : V ≃ₗ[A] (Fin s → S)) :
    IsIsotypicOfType A V S := by
  intro U hU
  let f (i : Fin s) : U →ₗ[A] S := (LinearMap.proj i).comp (e.toLinearMap.comp U.subtype)
  have h : ∃ i, f i ≠ 0 := by
    by_contra! hn
    let : Nontrivial U := IsSimpleModule.nontrivial A U
    obtain ⟨u,hu⟩ := exists_ne (0 : U)
    apply hu
    apply U.subtype_injective
    apply e.injective
    rw [map_zero, map_zero]
    funext i
    exact LinearMap.congr_fun (hn i) u
  obtain ⟨i,hi⟩ := h
  exact ⟨LinearEquiv.ofBijective (f i) (LinearMap.bijective_of_ne_zero hi)⟩

/-- When q is one modulo three, the number of constituents is s modulo three. -/
theorem copies_repeated_mod_three [Finite S] [Finite V] {s : ℕ}
    (e : V ≃ₗ[A] (Fin s → S))
    (hcard : 3 ∣ Nat.card (Module.End A S) - 1) :
    Nat.card (SimpleCopies.Copies A S V) % 3 = s % 3 := by
  rw [card_copies_repeated e]
  let : Nontrivial S := IsSimpleModule.nontrivial A S
  let : Finite (Module.End A S) := Finite.of_injective _ DFunLike.coe_injective
  have hc : 1 < Nat.card (Module.End A S) := Finite.one_lt_card
  have hmod : Nat.card (Module.End A S) % 3 = 1 := by omega
  clear e
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hmod, one_pow]
    exact (Nat.add_mod s 1 3).symm
end Ring

section Selection
variable {G V E : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
  [AddCommGroup E] [Module (ZMod 2)[N] E] [IsSimpleModule (ZMod 2)[N] E]

/-- A three-group fixes an actual simple copy when three does not divide its
multiplicity. The group action and intertwining map are retained. -/
theorem invariant_simple_of_repeated [Finite V] [Finite E] {s : ℕ}
    (e : Representation.asModule (ρ.comp N.subtype) ≃ₗ[(ZMod 2)[N]] (Fin s → E))
    (hcard : 3 ∣ Nat.card (Module.End (ZMod 2)[N] E) - 1) (hs : ¬ 3 ∣ s)
    (P : Subgroup G) (hP : IsPGroup 3 P) :
    ∃ U : Subrepresentation (ρ.comp N.subtype), U.toRepresentation.IsIrreducible ∧
      Nonempty (U.asSubmodule ≃ₗ[(ZMod 2)[N]] E) ∧
      ∀ p : P, U.toSubmodule.map (ρ p) = U.toSubmodule := by
  let : Finite (Representation.asModule (ρ.comp N.subtype)) :=
    Finite.of_equiv V (Representation.asModuleEquiv (ρ.comp N.subtype)).symm.toEquiv
  apply invariant_simple_of_count ρ N (isotypic_of_repeated e) ?_ P hP
  simpa only [Nat.dvd_iff_mod_eq_zero, copies_repeated_mod_three e hcard] using hs
end Selection

section Coordinates
variable {H W E : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup E] [Module (ZMod 2) E]

/-- Coordinate equations for each copy give an isomorphism over the original
component group algebra. -/
def repeatedModuleEquiv (ρ : Representation (ZMod 2) H W)
    (μ : Representation (ZMod 2) H E) {s : ℕ}
    (e : W ≃ₗ[ZMod 2] (Fin s → E))
    (he : ∀ g v, e (ρ g v) = fun i => μ g (e v i)) :
    ρ.asModule ≃ₗ[(ZMod 2)[H]] (Fin s → μ.asModule) := by
  let f (i : Fin s) : ρ.IntertwiningMap μ := {
    toLinearMap := (LinearMap.proj i).comp e.toLinearMap
    isIntertwining' g := LinearMap.ext (fun v => congrFun (he g v) i) }
  let j := LinearMap.pi (fun i => IntertwiningMap.equivLinearMapAsModule ρ μ (f i))
  exact LinearEquiv.ofBijective j e.bijective
end Coordinates

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]

/-- Every cubic lies in the marked component when the number of natural
copies in the original restriction is not divisible by three and the ambient three-rank is at most two. -/
theorem cubic_mem_of_repeated_natural (F : BinaryField)
    (L : Subgroup H) [L.Normal] (η : L →* SL(3,F.Carrier))
    (hη : Function.Surjective η) (hηker : Nat.Coprime 3 (Nat.card η.ker))
    (ρ : Representation (ZMod 2) H W)
    {s : ℕ} (hs : ¬ 3 ∣ s)
    (e : Representation.asModule (ρ.comp L.subtype) ≃ₗ[(ZMod 2)[L]]
      (Fin s → Representation.asModule ((linearNatural F 3).comp η)))
    (hd : 3 ∣ Nat.card F.Carrier - 1) (hr : primeRank 3 H ≤ 2)
    (x : H) (hx : x ^ 3 = 1) : x ∈ L := by
  let μ : Representation (ZMod 2) L (Fin 3 → F.Carrier) := (linearNatural F 3).comp η
  let : IsIrreducible μ := (irreducible_comp_surjective_iff η hη _).mpr
    (ExtensionConsequences.linearNatural_irreducible F (by decide))
  let : Finite μ.asModule := Finite.of_equiv (Fin 3 → F.Carrier) μ.asModuleEquiv.symm.toEquiv
  have hcard : 3 ∣ Nat.card (Module.End (ZMod 2)[L] μ.asModule) - 1 := by
    have heq : μ = (Representation.SL3OddNaturalNormalizer.binaryNatural F.Carrier).comp η := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro v
      rfl
    rw [heq, natural_end_card η hη]
    exact hd
  have hP : IsPGroup 3 (zpowers x) :=
    (isPGroup_iff_orderOf_dvd_pow).mpr (fun y => by
      refine ⟨1, ?_⟩
      have h : orderOf y ∣ 3 := by
        have hy := orderOf_dvd_natCard y
        have hc : Nat.card (zpowers x) = orderOf x := Nat.card_zpowers x
        rw [hc] at hy
        exact hy.trans (orderOf_dvd_of_pow_eq_one hx)
      exact h)
  obtain ⟨U,_,⟨a⟩,hU⟩ := invariant_simple_of_repeated ρ L e hcard hs (zpowers x) hP
  let eU : U.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → F.Carrier) := a.restrictScalars (ZMod 2)
  have ha (g : L) (v : U.toSubmodule) :
      eU (U.toRepresentation g v) = (η g).val.mulVec (eU v) := by
    let v' : U.asSubmodule := ⟨v.val,v.property⟩
    have hh := a.map_smul (MonoidAlgebra.single g (1 : ZMod 2)) v'
    have he : ((MonoidAlgebra.single g (1 : ZMod 2)) • v' : U.asSubmodule) =
        U.toRepresentation g v' := by
      apply Subtype.ext
      simp only [SetLike.val_smul, Representation.single_smul, one_smul]
      rfl
    rw [he] at hh
    have hs := Representation.single_smul μ 1 g (a v')
    rw [one_smul] at hs
    rw [hs] at hh
    change a (U.toRepresentation g v') = μ g (a v')
    exact hh
  let H₀ := BinaryOffender.subspaceStabilizer ρ U.toSubmodule
  have hLH : L ≤ H₀ := BinaryOffender.le_subspaceStabilizer ρ U.toSubmodule
    (fun g hg v hv => U.apply_mem_toSubmodule ⟨g,hg⟩ hv)
  have hxH : x ∈ H₀ := by
    have hn : zpowers x ≤ H₀ := BinaryOffender.le_subspaceStabilizer ρ U.toSubmodule (by
      intro g hg v hv
      rw [← hU ⟨g,hg⟩]
      exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩)
    exact hn (mem_zpowers x)
  let L₀ := L.subgroupOf H₀
  let : L₀.Normal := inferInstance
  let q : L₀ ≃* L := subgroupOfEquivOfLe hLH
  let η₀ : L₀ →* SL(3,F.Carrier) := η.comp q.toMonoidHom
  have hker : Nat.Coprime 3 (Nat.card η₀.ker) := by
    have hk : η₀.ker = η.ker.comap q.toMonoidHom := rfl
    rw [hk, comap_equiv_eq_map_symm', card_map_of_injective q.symm.injective]
    exact hηker
  let τ : Representation (ZMod 2) H₀ (Fin 3 → F.Carrier) :=
    (eU.conjRingEquiv.toMonoidHom).comp (BinaryOffender.stabilizerRepresentation ρ U.toSubmodule)
  have hnat (g : L₀) (v : Fin 3 → F.Carrier) :
      τ (g : H₀) v = (η₀ g).val.mulVec v := by
    change eU (U.toRepresentation (q g) (eU.symm v)) = _
    rw [ha, eU.apply_symm_apply]
    rfl
  have hh := cubic_mem_of_natural_quotient L₀ η₀ (hη.comp q.surjective) hker τ hnat hd
    ((Theory.GroupTheory.primeRank_le_of_injective 3 H₀.subtype H₀.subtype_injective).trans hr)
    ⟨x,hxH⟩ (Subtype.ext hx)
  exact hh

/-- Cubic containment from arbitrary repeated-natural binary coordinates
whose multiplicity is prime to three. -/
theorem cubic_mem_of_repeated_coordinates (F : BinaryField)
    (L : Subgroup H) [L.Normal] (η : L →* SL(3,F.Carrier))
    (hη : Function.Surjective η) (hηker : Nat.Coprime 3 (Nat.card η.ker))
    (ρ : Representation (ZMod 2) H W) {s : ℕ} (hs : ¬ 3 ∣ s)
    (e : W ≃ₗ[ZMod 2] (Fin s → Fin 3 → F.Carrier))
    (he : ∀ (g : L) (v : W), e (ρ g v) = fun i => (η g).val.mulVec (e v i))
    (hd : 3 ∣ Nat.card F.Carrier - 1) (hr : primeRank 3 H ≤ 2)
    (x : H) (hx : x ^ 3 = 1) : x ∈ L := by
  exact cubic_mem_of_repeated_natural F L η hη hηker ρ hs
    (repeatedModuleEquiv (ρ.comp L.subtype) ((linearNatural F 3).comp η) e he) hd hr x hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
