module
public import Theory.Representation.SimpleHeadQuotient.DistinctPair
public import Theory.Representation.PSL3Two.NaturalDualNormalizer
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Point two-group fixed vectors generate the natural–dual pair

An invariant subspace of the binary natural plus dual representation is one
of the four coordinate sums. If a normalizing two-group stabilizes a proper
nonzero sum, all its automorphisms are inner: an outer automorphism exchanges
the two summands. The complementary summand is then stable and has a nonzero
fixed vector. Thus a subspace stable under both actors and containing every
fixed vector is the whole six-space.

This supplies the orbit-generation step for row 10.1.1(5) in the constrained
branch of Aschbacher–Smith 10.2.9, printed p.751. The application to literal
conjugation coordinates is in PointControl.Constrained.Preparation.NaturalDual.
-/

public section
namespace BinaryLinearThree.NaturalDual
open Subgroup Representation.BinaryOffender
variable {P : Type*} [_root_.Group P]

private theorem fixed_outside_axis
    (η : Representation (ZMod 2) P Space) (hP : IsPGroup 2 P)
    (a : P →* MulAut Group)
    (ha : ∀ p g x, η p (action g x) = action (a p g) (η p x))
    (K : Submodule (ZMod 2) Space)
    (hstable : ∀ p x, x ∈ K → η p x ∈ K)
    (haxis : K = (⊤ : Submodule (ZMod 2) Vector).prod ⊥ ∨
      K = (⊥ : Submodule (ZMod 2) Vector).prod ⊤) :
    ∃ x, x ≠ 0 ∧ (∀ p, η p x = x) ∧ x ∉ K := by
  have hin (p : P) : a p ∈ MulAut.innerSubgroup Group := by
    by_contra hn
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom p)
    have hf : ∀ g x, f (action g x) = action (a p g) (f x) := ha p
    have hs := outer_swaps (a p) f hf hn
    rcases haxis with rfl | rfl
    · obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
      have hm := hstable p (v,0) (by simp)
      have hz : η p (v,0) = 0 := Prod.ext (hs.1 v) hm.2
      have he := (f.injective (hz.trans (f.map_zero).symm))
      exact hv (congrArg Prod.fst he)
    · obtain ⟨v,hv⟩ := exists_ne (0 : Module.Dual (ZMod 2) Vector)
      have hm := hstable p (0,v) (by simp)
      have hz : η p (0,v) = 0 := Prod.ext hm.1 (hs.2 v)
      have he := (f.injective (hz.trans (f.map_zero).symm))
      exact hv (congrArg Prod.snd he)
  have haxes (p : P) :
      (∀ v, (η p (v,0)).2 = 0) ∧ (∀ v, (η p (0,v)).1 = 0) := by
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom p)
    obtain ⟨g,hg⟩ := inner_operator (a p) f (ha p) (hin p)
    constructor
    · intro v
      change (f (v,0)).2 = 0
      rw [hg]
      change W.dual g 0 = 0
      exact map_zero _
    · intro v
      change (f (0,v)).1 = 0
      rw [hg]
      change W g 0 = 0
      exact map_zero _
  have hPtop : IsPGroup 2 (⊤ : Subgroup P) := hP.of_injective _ (⊤ : Subgroup P).subtype_injective
  rcases haxis with rfl | rfl
  · let C : Submodule (ZMod 2) Space := (⊥ : Submodule (ZMod 2) Vector).prod ⊤
    have hC : C ≠ ⊥ := by
      obtain ⟨v,hv⟩ := exists_ne (0 : Module.Dual (ZMod 2) Vector)
      exact (Submodule.ne_bot_iff _).mpr ⟨(0,v),by simp [C],fun h => hv (congrArg Prod.snd h)⟩
    have hCS : (⊤ : Subgroup P) ≤ subspaceStabilizer η C := by
      apply le_subspaceStabilizer
      rintro p _ ⟨v,w⟩ hvw
      have hv : v = 0 := hvw.1
      subst v
      exact ⟨(haxes p).2 w,Submodule.mem_top⟩
    obtain ⟨x,hx,hx0,hxf⟩ := PermutedSupports.exists_nonzero_fixed η ⊤ hPtop C hC hCS
    refine ⟨x,hx0,fun p => hxf ⟨p,mem_top p⟩,fun hk => hx0 (Prod.ext hx.1 hk.2)⟩
  · let C : Submodule (ZMod 2) Space := (⊤ : Submodule (ZMod 2) Vector).prod ⊥
    have hC : C ≠ ⊥ := by
      obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
      exact (Submodule.ne_bot_iff _).mpr ⟨(v,0),by simp [C],fun h => hv (congrArg Prod.fst h)⟩
    have hCS : (⊤ : Subgroup P) ≤ subspaceStabilizer η C := by
      apply le_subspaceStabilizer
      rintro p _ ⟨v,w⟩ hvw
      have hw : w = 0 := hvw.2
      subst w
      exact ⟨Submodule.mem_top,(haxes p).1 v⟩
    obtain ⟨x,hx,hx0,hxf⟩ := PermutedSupports.exists_nonzero_fixed η ⊤ hPtop C hC hCS
    refine ⟨x,hx0,fun p => hxf ⟨p,mem_top p⟩,fun hk => hx0 (Prod.ext hk.1 hx.2)⟩

theorem fixed_generates
    (η : Representation (ZMod 2) P Space) (hP : IsPGroup 2 P)
    (a : P →* MulAut Group)
    (ha : ∀ p g x, η p (action g x) = action (a p g) (η p x))
    (K : Submodule (ZMod 2) Space)
    (hK : ∀ g x, x ∈ K → action g x ∈ K)
    (hstable : ∀ p x, x ∈ K → η p x ∈ K)
    (hfixed : ∀ x, (∀ p, η p x = x) → x ∈ K) : K = ⊤ := by
  let := IrreducibleCatalogue.natural_irreducible
  let := IrreducibleCatalogue.dual_irreducible
  rcases Representation.SimpleHeadQuotient.distinct_pair_submodules W W.dual
    AutomorphismAction.natural_not_equiv_dual K hK with hb | hl | hr | ht
  · have hPtop : IsPGroup 2 (⊤ : Subgroup P) := hP.of_injective _ (⊤ : Subgroup P).subtype_injective
    obtain ⟨x,_,hx,hxf⟩ := PermutedSupports.exists_nonzero_fixed η ⊤ hPtop ⊤ top_ne_bot
      (by apply le_subspaceStabilizer; intros; trivial)
    have hh := hfixed x (fun p => hxf ⟨p,mem_top p⟩)
    rw [hb] at hh
    exact False.elim (hx hh)
  · obtain ⟨x,_,hxf,hxn⟩ := fixed_outside_axis η hP a ha K hstable (Or.inl hl)
    exact False.elim (hxn (hfixed x hxf))
  · obtain ⟨x,_,hxf,hxn⟩ := fixed_outside_axis η hP a ha K hstable (Or.inr hr)
    exact False.elim (hxn (hfixed x hxf))
  · exact ht
end BinaryLinearThree.NaturalDual
