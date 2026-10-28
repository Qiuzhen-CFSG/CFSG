module
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Modules

/-!
# Fixed vectors of the binary natural-plus-dual point stabilizer

The point stabilizer fixes precisely the natural point line. Radical
transvections detect the natural coordinate, and the full natural commutator
space annihilates every invariant covector. This characterization is canonical
and remains usable when the module sits beside a central fixed supplement.

Source: Aschbacher–Smith, H.9.1(3) and the point-parabolic construction in
15.3.24, printed pp.389–390 and 1129–1130.
-/

public section
namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear
open Theory.LinearAlgebra.BinaryFivePointStabilizer
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem point_fixed_iff [FiniteDimensional (ZMod 2) V]
    (hd : 3 ≤ Module.finrank (ZMod 2) V) {x : V} (hx : x ≠ 0)
    (v : V × Module.Dual (ZMod 2) V) :
    (∀ g : pointStabilizer x, NaturalDualFlag.action g.val v = v) ↔
      v.1 ∈ line x ∧ v.2 = 0 := by
  constructor
  · intro hv
    have hline : line x ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
    refine ⟨(mem_iff_fixed_radical hline v.1).mpr ?_, ?_⟩
    · intro g hg
      have hgx : g ∈ pointStabilizer x :=
        hg.1 x (Submodule.mem_span_singleton_self x)
      simpa only [NaturalDualFlag.action_fst] using congrArg Prod.fst (hv ⟨g,hgx⟩)
    · have hker : Representation.Coinvariants.ker (pointNaturalRepresentation x) ≤ v.2.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨g,w⟩,rfl⟩
        change v.2 (g.val w - w) = 0
        have he := congrArg (fun a : V × Module.Dual (ZMod 2) V => a.2 w) (hv g⁻¹)
        rw [NaturalDualFlag.action_snd] at he
        change v.2 (g.val w) = v.2 w at he
        rw [map_sub,he,sub_self]
      rw [point_natural_commutator hd hx] at hker
      apply LinearMap.ext
      intro w
      exact hker (Submodule.mem_top)
  · rintro ⟨hv,hf⟩ g
    apply Prod.ext
    · rw [NaturalDualFlag.action_fst]
      exact fixes_line x g v.1 hv
    · apply LinearMap.ext
      intro w
      simp only [NaturalDualFlag.action_snd,hf,LinearMap.zero_apply]

end BinaryNaturalDual.VectorStabilizers.Pure
