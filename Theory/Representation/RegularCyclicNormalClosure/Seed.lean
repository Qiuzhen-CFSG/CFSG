module

public import Theory.Representation.RegularCyclicNormalClosure.Basic

/-!
# A local factor interface for regular cyclic normal closures

`FactorSeed` singles out one actual subgroup between C and its normal
closure. It requires a local fixed/moved splitting and fixation of the
moved spaces of its distinct conjugates. Its alternatives are C itself or
a nonabelian group of order 21 on a moved space of dimension three.
It does not provide a global decomposition or assert that such a subgroup
exists for nonnormal C. Construction of that subgroup and assembly of its
conjugates are separate proof obligations.

The elementary lemmas below show that mutual fixation of moved spaces
implies commuting actors and internal independence of both the groups and
their moved spaces. Faithfulness detects the group identities, while each
local splitting detects the trivial intersections.

This interface supports the proof of the extension cited as Aschbacher,
Weak closure in finite groups of even characteristic, J. Algebra 70 (1981),
10.4, applied in Aschbacher–Smith E.6.24, printed p.255 (PDF p.266).
-/

public section

open Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A local factor fixing the moved spaces of its distinct conjugates.
Existence of such a factor is a separate geometric obligation. -/
structure FactorSeed (ρ : Representation (ZMod 2) A W) (C B : Subgroup A) : Prop where
  contained : C ≤ B
  in_normalClosure : B ≤ normalClosure (C : Set A)
  split : IsCompl (fixedSpace ρ B) (displacementSpan ρ B ⊤)
  cross_fixed : ∀ a : A, B.map (MulAut.conj a).toMonoidHom ≠ B →
    ∀ b ∈ B, ∀ v ∈ displacementSpan ρ (B.map (MulAut.conj a).toMonoidHom) ⊤, ρ b v = v
  alternatives : C = B ∨
    (Nat.card C = 3 ∧ Nat.card B = 21 ∧ (¬ ∀ x y : B, x * y = y * x) ∧
      Module.finrank (ZMod 2) (displacementSpan ρ B ⊤) = 3)

/-- A normal cyclic subgroup itself supplies the local factor. -/
theorem Input.factorSeed_of_normal (h : Input ρ C) [C.Normal] : FactorSeed ρ C C where
  contained := le_rfl
  in_normalClosure := le_normalClosure
  split := h.split
  cross_fixed := fun a ha => (ha (Subgroup.Normal.map_conj_eq C a)).elim
  alternatives := Or.inl rfl

/-- Actors fixing one another's displacements commute in a faithful action. -/
theorem commute_of_cross_fixed (hfaithful : Function.Injective ρ)
    {B D : Subgroup A}
    (hBD : ∀ b ∈ B, ∀ v ∈ displacementSpan ρ D ⊤, ρ b v = v)
    (hDB : ∀ d ∈ D, ∀ v ∈ displacementSpan ρ B ⊤, ρ d v = v)
    {b d : A} (hb : b ∈ B) (hd : d ∈ D) : Commute b d := by
  change b * d = d * b
  apply hfaithful
  ext v
  simp only [map_mul, Module.End.mul_apply]
  have hbd := hBD b hb (ρ d v - v) (Submodule.subset_span ⟨d, hd, v, Submodule.mem_top, rfl⟩)
  have hdb := hDB d hd (ρ b v - v) (Submodule.subset_span ⟨b, hb, v, Submodule.mem_top, rfl⟩)
  rw [map_sub, sub_eq_iff_eq_add] at hbd hdb
  rw [hbd, hdb]
  abel

/-- Every family of locally split supports fixed by the other actors is independent. -/
theorem summands_independent_of_cross_fixed {ι : Type*} (B : ι → Subgroup A)
    (hs : ∀ i, IsCompl (fixedSpace ρ (B i)) (displacementSpan ρ (B i) ⊤))
    (hf : ∀ i j, i ≠ j → ∀ b ∈ B i, ∀ v ∈ displacementSpan ρ (B j) ⊤, ρ b v = v) :
    iSupIndep (fun i => displacementSpan ρ (B i) ⊤) := by
  intro i
  apply (hs i).disjoint.symm.mono_right
  apply iSup_le
  intro j
  apply iSup_le
  intro hji v hv b
  exact hf i j hji.symm b b.property v hv

/-- The internal group factors are independent when their moved spaces are
locally split and fixed by every other factor. -/
theorem factors_independent_of_cross_fixed (hfaithful : Function.Injective ρ)
    {ι : Type*} (B : ι → Subgroup A)
    (hs : ∀ i, IsCompl (fixedSpace ρ (B i)) (displacementSpan ρ (B i) ⊤))
    (hf : ∀ i j, i ≠ j → ∀ b ∈ B i, ∀ v ∈ displacementSpan ρ (B j) ⊤, ρ b v = v) :
    iSupIndep B := by
  intro i
  apply Subgroup.disjoint_def.mpr
  intro b hb hrest
  have hfix : ∀ v ∈ displacementSpan ρ (B i) ⊤, ρ b v = v := by
    refine Subgroup.iSup_induction _
      (C := fun b => ∀ v ∈ displacementSpan ρ (B i) ⊤, ρ b v = v) hrest ?_ ?_ ?_
    · intro j a ha
      refine Subgroup.iSup_induction _
        (C := fun b => ∀ v ∈ displacementSpan ρ (B i) ⊤, ρ b v = v) ha ?_ ?_ ?_
      · intro hji a ha v hv
        exact hf j i hji a ha v hv
      · intro v _
        simp
      · intro a b ha hb v hv
        simp only [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
    · intro v _
      simp
    · intro a b ha hb v hv
      simp only [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
  apply hfaithful
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ fixedSpace ρ (B i) ⊔ displacementSpan ρ (B i) ⊤ by
      rw [(hs i).sup_eq_top]; trivial)
  rw [map_one, Module.End.one_apply, map_add,
    (show ρ b u = u from hu ⟨b, hb⟩), hfix w hw]

end Representation.RegularCyclicNormalClosure
