module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import Theory.Representation.BinaryPermutation.GroupIrreducible
public import Theory.GroupTheory.TINormalizerControl

/-!
# Trivial intersections and local seed normalizers for the actual A₅ module

The binary five-point core is irreducible. Pulling invariant subgroups
through the original module map proves this for V itself. Consequently
two conjugates of V under N(L) either coincide or have trivial intersection.
This is the original 12.2.6 normalizer-control input for V₃, and identifies
its centralizer inside M=N(L) with the full centralizer of V.

Source: Aschbacher–Smith 12.2.6 and13.2.3, printed pp.797 and878–879.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem irreducible_module (W : Subgroup G) (hWV : W ≤ V)
    (hLW : L ≤ normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  have hinv : ∀ a : alternatingGroup (Fin 5), ∀ x ∈ d.flag.preimage W,
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a.val x.toAdd) ∈
        d.flag.preimage W := by
    intro a x hx
    obtain ⟨l,rfl⟩ := d.flag.module.onto a
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.module.action l).val x.toAdd)) ∈ W
    rw [← d.flag.module.equivariant]
    exact (mem_normalizer_iff.mp (hLW l.property) _).mp hx
  rcases BinaryPermutation.fiveCore_invariant_subgroup (d.flag.preimage W) hinv with h | h
  · left
    have hm := congrArg (map d.flag.module.map) h
    simpa only [d.flag.preimage_map W hWV,Subgroup.map_bot] using hm
  · right
    have hm := congrArg (map d.flag.module.map) h
    simpa only [d.flag.preimage_map W hWV,← MonoidHom.range_eq_map,d.flag.module.range_eq] using hm

/-- The actual M-conjugates of the chosen module have trivial intersections. -/
theorem trivial_intersections (g : G) (hg : g ∈ normalizer (L : Set G)) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V := by
  have hLVg : L ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    have h := (map_mono (f := (MulAut.conj g).toMonoidHom) d.chosen.normalizes).trans
      (V.le_normalizer_map (MulAut.conj g).toMonoidHom)
    have he : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hg
    exact he ▸ h
  rcases d.irreducible_module (V ⊓ V.map (MulAut.conj g).toMonoidHom) inf_le_left
      ((le_inf d.chosen.normalizes hLVg).trans inf_normalizer_le_normalizer_inf) with h | h
  · exact Or.inl h
  · right
    have hle : V ≤ V.map (MulAut.conj g).toMonoidHom := h.symm.le.trans inf_le_right
    exact (eq_of_le_of_card_ge hle
      (card_map_of_injective (MulAut.conj g).injective).le).symm

theorem third_ne_bot : V₃ ≠ ⊥ := by
  intro h
  have hc := d.third_card
  simp [h] at hc

/-- Original 12.2.6 applied to the actual third subgroup. -/
theorem third_normalizer_local : normalizer (L : Set G) ⊓ normalizer (V₃ : Set G) ≤
    normalizer (V : Set G) :=
  inf_normalizer_le_of_trivial_intersections d.trivial_intersections d.third_ne_bot d.third_le

/-- The centralizer needed for the local Sylow step of13.2.3(2). -/
theorem third_centralizer_local : normalizer (L : Set G) ⊓ centralizer (V₃ : Set G) =
    centralizer (V : Set G) := by
  apply le_antisymm
  · intro x hx
    exact (centralizer_third d.flag V₃ d.third_le d.third_card d.third_invariant).le
      ⟨d.third_normalizer_local ⟨hx.1,Subgroup.centralizer_le_normalizer _ hx.2⟩,hx.2⟩
  · exact le_inf ((Subgroup.centralizer_le_normalizer _).trans d.module_normalizer)
      (centralizer_le d.third_le)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
