module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics
public import Theory.PGroupCore

/-!
# Coordinates on direct powers of the second Tits parabolic

An equivalence with a finite direct power of the actual second parabolic
gives surjective coordinate homomorphisms with trivial common kernel.
Each coordinate maps the two-core onto the parabolic's two-core: the
product of the factor cores is a normal two-subgroup, and its constant
vectors lift every element of the target core. This does not require a
coordinate kernel, which contains the other factors, to be a two-group.

These are the intrinsic coordinate calculations for the centerless
component-orbit construction in Aschbacher–Smith 2.3.9(7), printed p.526.
The ambient normal base and its two-group quotient are constructed by
the chapter consumer, allowing the Sylow subgroup to permute components.
-/

@[expose] public section

open Subgroup
namespace Tits.RelativeSecondBlockLayers.ComponentOrbit

private theorem pCore_map_eval {P : Type*} [Group P] [Finite P]
    (p n : ℕ) (i : Fin n) :
    (pCore p (Fin n → P)).map (Pi.evalMonoidHom (fun _ : Fin n => P) i) =
      pCore p P := by
  let ev := Pi.evalMonoidHom (fun _ : Fin n => P) i
  have hev : Function.Surjective ev := fun x => ⟨fun _ => x, rfl⟩
  apply le_antisymm
  · exact le_sSup ⟨Subgroup.Normal.map inferInstance ev hev, pCore_isPGroup.map ev⟩
  · let Q : Subgroup (Fin n → P) := pi Set.univ (fun _ => pCore p P)
    have hQ (x : Fin n → P) : x ∈ Q ↔ ∀ j, x j ∈ pCore p P := by
      simp [Q, mem_pi]
    have hn : Q.Normal := ⟨by
      intro x hx y
      apply (hQ _).mpr
      intro j
      exact (pCore_normal (p := p) (G := P)).conj_mem _ ((hQ _).mp hx j) _⟩
    have hp : IsPGroup p Q := by
      obtain ⟨m, hm⟩ := (pCore_isPGroup (p := p) (G := P)).exists_card_dvd_pow
      intro x
      refine ⟨m, Subtype.ext (funext fun j => ?_)⟩
      let y : pCore p P := ⟨x.val j, (hQ _).mp x.property j⟩
      exact congrArg Subtype.val
        (orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard y).trans hm))
    have hle : Q ≤ pCore p (Fin n → P) := le_sSup ⟨hn, hp⟩
    intro x hx
    exact ⟨fun _ => x, hle ((hQ _).mpr (fun _ => hx)), rfl⟩

variable {X : Type*} [Group X] {n : ℕ}
  (e : X ≃* (Fin n → ExceptionalParabolics.second))

/-- Evaluation after the supplied equivalence to the actual parabolic power. -/
def projection (i : Fin n) : X →* ExceptionalParabolics.second :=
  (Pi.evalMonoidHom (fun _ : Fin n => ExceptionalParabolics.second) i).comp e.toMonoidHom

theorem projection_surjective (i : Fin n) : Function.Surjective (projection e i) :=
  fun x => ⟨e.symm (fun _ => x), by simp [projection]⟩

/-- Core surjectivity uses the normal product of all factor cores. -/
theorem projection_core_image (i : Fin n) :
    (pCore 2 X).map (projection e i) = pCore 2 ExceptionalParabolics.second := by
  rw [projection, ← Subgroup.map_map, pCore_map_iso]
  exact pCore_map_eval 2 n i

/-- All coordinates together are faithful, although individual kernels need not be two-groups. -/
theorem iInf_projection_ker_eq_bot : (⨅ i, (projection e i).ker) = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  rw [map_one]
  funext i
  exact (mem_iInf.mp hx i : e x i = 1)

end Tits.RelativeSecondBlockLayers.ComponentOrbit

end
