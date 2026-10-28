module
public import Theory.Representation.BinaryPermutation.TransvectionCoreMap
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections
public import Theory.Representation.BinaryPermutation.ProperInvariant
public import Theory.Representation.BinaryPermutation.CoreQuotientModels
import Mathlib.Tactic

/-!
# Fixed kernels from a rank-one involution in a fully moved S₈-module

A faithful binary action with a rank-one involution identifies that involution
as a transposition. Its augmentation-core map is onto whenever the alternating
commutator is the whole module. Pulling a proper invariant subspace back to
that core shows it is fixed by the entire symmetric group. In particular,
there is a natural six-dimensional quotient whose literal kernel is fixed.
No splitting of either quotient is used.

Source: Aschbacher–Smith, B.3.1, printed p.83; this supplies the rank-one
alternative in the whole-module approach to 14.7.51, printed p.1065.
It does not select a rank-one involution from a quadratic offender.
-/

public noncomputable section
namespace BinaryPermutation.TransvectionCoreMap
open Representation Representation.BinaryOffender
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- Fixation descends from the preimage of any proper alternating-invariant
subspace through a surjective augmentation-core map. -/
theorem proper_invariant_fixed_of_core_surjection
    (ρ : Representation (ZMod 2) H E) (e : H ≃* Equiv.Perm (Fin 8))
    (K : Subgroup H) (hK : K.map e.toMonoidHom = alternatingGroup (Fin 8))
    (f : core (Fin 8) →ₗ[ZMod 2] E) (hf : Function.Surjective f)
    (he : ∀ g v, f (coreRepresentation (Fin 8) (e g) v) = ρ g (f v))
    (W : Submodule (ZMod 2) E)
    (hW : ∀ g ∈ K, ∀ w ∈ W, ρ g w ∈ W) (hp : W ≠ ⊤) :
    W ≤ invariants ρ := by
  have hpre : ∀ g : alternatingGroup (Fin 8), ∀ v ∈ W.comap f,
      coreRepresentation (Fin 8) g.val v ∈ W.comap f := by
    intro g v hv
    have hg : g.val ∈ K.map e.toMonoidHom := by rw [hK]; exact g.property
    obtain ⟨k,hk,hkg⟩ := Subgroup.mem_map.mp hg
    change e k = g.val at hkg
    change f (coreRepresentation (Fin 8) g.val v) ∈ W
    rw [←hkg,he]
    exact hW k hk (f v) hv
  have hproper : W.comap f ≠ ⊤ := by
    intro ht
    apply hp
    apply top_unique
    intro w _
    obtain ⟨v,rfl⟩ := hf w
    exact (show v ∈ W.comap f from ht ▸ Submodule.mem_top)
  intro w hw g
  obtain ⟨v,rfl⟩ := hf w
  rw [←he,core_proper_invariant_fixed (by decide) (W.comap f) hpre hproper (e g) v hw]

/-- Every nonzero quotient of the augmentation core has a natural quotient,
retaining the full symmetric action and the specified marking. -/
theorem natural_quotient_of_core_surjection
    (ρ : Representation (ZMod 2) H E) (e : H ≃* Equiv.Perm (Fin 8))
    (f : core (Fin 8) →ₗ[ZMod 2] E) (hf : Function.Surjective f)
    (he : ∀ g v, f (coreRepresentation (Fin 8) (e g) v) = ρ g (f v))
    (hne : f ≠ 0) :
    ∃ p : ρ.IntertwiningMap ((naturalRepresentation (Fin 8)).comp e.toMonoidHom),
      Function.Surjective p := by
  rcases natural_or_core_of_core_surjection (by decide) ρ e f he hf hne with
    ⟨j,hj⟩ | ⟨j,hj⟩
  · exact ⟨j.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ hj,j.surjective⟩
  · refine ⟨((coreToNatural (Fin 8)).comp j.toLinearMap).intertwiningMap_of_isIntertwiningMap
      _ _ ?_,coreToNatural_surjective.comp j.surjective⟩
    intro g w
    change coreToNatural (Fin 8) (j (ρ g w)) = _
    rw [hj,coreToNatural_equivariant]
    rfl

/-- Full alternating movement and a rank-one involution construct a natural
quotient with a fixed kernel, including nonsplit augmentation covers. -/
theorem natural_fixed_kernel_quotient_of_rank_one_involution
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (hρ : Function.Injective ρ)
    (e : H ≃* Equiv.Perm (Fin 8))
    (K : Subgroup H) (hK : K.map e.toMonoidHom = alternatingGroup (Fin 8))
    (hmove : subspaceCommutator ρ ⊤ K = ⊤)
    (a : H) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hr : fixedCodim ρ (Subgroup.zpowers a) = 1) :
    ∃ p : ρ.IntertwiningMap ((naturalRepresentation (Fin 8)).comp e.toMonoidHom),
      Function.Surjective p ∧ p.toLinearMap.ker ≤ invariants ρ := by
  have hs := SymmetricEightTransvections.isSwap_of_fixedCodim_eq_one ρ hρ e a ha ha2 hr
  obtain ⟨f,he,hf⟩ := exists_core_map_of_transposition ρ hρ e K hK a hs hr
  have hfs : Function.Surjective f := LinearMap.range_eq_top.mp (hf.trans hmove)
  have hfn : f ≠ 0 := by
    intro hz
    apply ha
    apply hρ
    ext w
    obtain ⟨v,rfl⟩ := hfs w
    simp [hz]
  obtain ⟨p,hp⟩ := natural_quotient_of_core_surjection ρ e f hfs he hfn
  refine ⟨p,hp,proper_invariant_fixed_of_core_surjection ρ e K hK f hfs he
    p.toLinearMap.ker ?_ ?_⟩
  · intro g _ w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining,show p w = 0 from hw,map_zero]
  · let : Nontrivial (natural (Fin 8)) := Module.nontrivial_of_finrank_pos (by
      rw [finrank_natural_even (Fin 8) (by decide)]
      decide)
    intro hz
    obtain ⟨w,hw⟩ := exists_ne (0 : natural (Fin 8))
    obtain ⟨v,rfl⟩ := hp w
    have hv : v ∈ p.toLinearMap.ker := by rw [hz]; trivial
    exact hw hv

end BinaryPermutation.TransvectionCoreMap
