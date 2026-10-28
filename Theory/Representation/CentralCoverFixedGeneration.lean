module
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Theory.Representation.FirstCohomologyDuality

/-!
# Fixed-vector generation through a central cover

If fixed quotient vectors lift, a two-group has a nonzero fixed image in an
irreducible quotient. Its orbit generates that quotient, and full commutator
generation removes the central kernel. Source application: Aschbacher–Smith
10.2.9, printed p.751.
-/

public noncomputable section
open Representation Representation.OneCohomology
namespace Representation.OneCohomology
open Representation.BinaryOffender
variable {J P N W : Type*} [Group J] [Group P]
  [AddCommGroup N] [Module (ZMod 2) N] [FiniteDimensional (ZMod 2) N]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Fixed vectors of a two-group generate a fully moved central cover when
fixed quotient vectors lift and the quotient is irreducible. -/
theorem eq_top_of_contains_fixed_of_cover
    {ρ : Representation (ZMod 2) J N} [ρ.IsIrreducible]
    {σ : Representation (ZMod 2) J W}
    (q : σ.IntertwiningMap ρ) (hq : IsCover q)
    (η : Representation (ZMod 2) P N) (τ : Representation (ZMod 2) P W)
    (hP : IsPGroup 2 P)
    (hlift : ∀ v, (∀ p, η p v = v) → ∃ w, q w = v ∧ ∀ p, τ p w = w)
    (K : Submodule (ZMod 2) W)
    (hK : ∀ j w, w ∈ K → σ j w ∈ K)
    (hfix : ∀ w, (∀ p, τ p w = w) → w ∈ K) : K = ⊤ := by
  let : Nontrivial N := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v,_,hv,hvf⟩ := PermutedSupports.exists_nonzero_fixed η ⊤
    (hP.of_injective (⊤ : Subgroup P).subtype Subtype.val_injective)
    ⊤ top_ne_bot (le_subspaceStabilizer η ⊤ (fun _ _ _ _ => Submodule.mem_top))
  obtain ⟨w,hw,hwf⟩ := hlift v (fun p => hvf ⟨p,Subgroup.mem_top p⟩)
  let Q : Subrepresentation ρ := {
    toSubmodule := K.map q.toLinearMap
    apply_mem_toSubmodule := by
      rintro j _ ⟨x,hx,rfl⟩
      exact ⟨σ j x,hK j x hx,LinearMap.congr_fun (q.isIntertwining' j) x⟩ }
  have hQ : Q = ⊤ := (eq_bot_or_eq_top Q).resolve_left (by
    intro he
    have hm : v ∈ Q := ⟨w,hfix w hwf,hw⟩
    rw [he] at hm
    exact hv hm)
  apply top_unique
  rw [←hq.2.2]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j,x⟩,rfl⟩
  have hm : q x ∈ Q := hQ ▸ Submodule.mem_top
  obtain ⟨y,hy,hxy⟩ := hm
  change q y = q x at hxy
  have hk : x-y ∈ q.toLinearMap.ker := by
    change q (x-y) = 0
    rw [map_sub,hxy,sub_self]
  have hf := hq.2.1 hk j
  have hh : σ j x-x = σ j y-y := by
    rw [map_sub] at hf
    exact (sub_eq_sub_iff_sub_eq_sub).mp hf
  change σ j x-x ∈ K
  rw [hh]
  exact K.sub_mem (hK j y hy) hy
end Representation.OneCohomology
