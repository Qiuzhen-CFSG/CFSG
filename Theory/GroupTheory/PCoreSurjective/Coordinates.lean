module

public import Theory.GroupTheory.PCoreSurjective

/-!
# Core-surjective coordinates on a group power

The product of the factor p-cores is a normal p-subgroup. Constant vectors
in this product show that evaluation maps its p-core onto each factor core.
Combining this with p-core lifting through a p-group kernel gives coordinate
core-surjectivity for every surjection onto a finite power with such a kernel.
The individual coordinate kernels need not be p-groups.

This supplies the core-image assertion for component-orbit sections in
Aschbacher–Smith 2.3.9(7), printed p.526.
-/

public section

open Subgroup

/-- Evaluation maps the p-core of a direct power onto the factor p-core. -/
theorem Subgroup.pCore_map_eval {P I : Type*} [Group P] [Finite P]
    (p : ℕ) (i : I) :
    (pCore p (I → P)).map (Pi.evalMonoidHom (fun _ : I => P) i) = pCore p P := by
  let ev := Pi.evalMonoidHom (fun _ : I => P) i
  have hev : Function.Surjective ev := fun x => ⟨fun _ => x, rfl⟩
  apply le_antisymm
  · exact le_sSup ⟨Subgroup.Normal.map inferInstance ev hev, pCore_isPGroup.map ev⟩
  · let Q : Subgroup (I → P) := pi Set.univ (fun _ => pCore p P)
    have hQ (x : I → P) : x ∈ Q ↔ ∀ j, x j ∈ pCore p P := by
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
    have hle : Q ≤ pCore p (I → P) := le_sSup ⟨hn, hp⟩
    intro x hx
    exact ⟨fun _ => x, hle ((hQ _).mpr (fun _ => hx)), rfl⟩

/-- A surjection onto a finite power with p-group kernel is core-surjective
in each coordinate, even when a coordinate kernel contains other factors. -/
theorem MonoidHom.pCore_map_coordinate {X P I : Type*}
    [Group X] [Group P] [Finite X] [Finite P] [Finite I]
    {p : ℕ} [Fact p.Prime] (f : X →* (I → P))
    (hf : Function.Surjective f) (hk : IsPGroup p f.ker) (i : I) :
    (pCore p X).map ((Pi.evalMonoidHom (fun _ : I => P) i).comp f) = pCore p P := by
  rw [← Subgroup.map_map, ← f.comap_pCore_of_ker_isPGroup hf hk,
    Subgroup.map_comap_eq_self]
  · exact Subgroup.pCore_map_eval p i
  · rw [f.range_eq_top_of_surjective hf]
    exact le_top

end
