module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LocalPair
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsMarked
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LargeLocal
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal
public import Theory.SpecificGroups.ReeF4.LocalBlockInput
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Exclusion of Ree and Tits components by their local blocks

Source: Aschbacher–Smith 1.1.5(3)(a), printed pp.501–502, and the two-parabolic
argument for 2.3.9(7), printed p.526, in `refs/quasithin.pdf`.

The two actual local factors generate the component. Their invariance under
N_S(L) allows adjoining the whole Sylow subgroup S, including when S permutes
components. Both resulting overgroups belong to HeOver, with nontrivial
two-cores. The source block decomposition would produce an escaping χ₀ block
subnormal in one of these overgroups.

For the large Ree family, the Suzuki-side overgroup has order prime to three,
excluding χ₀ subgroups. Every escaping block of the linear-side overgroup has
a normal two-layer with nonzero third commutator, contrary to shortness.
`not_large_fixed_model` assembles this argument with the explicit exceptional
endomorphism. `not_isReeF4Model` then discharges that construction input using
the proved canonical endomorphism and its actual fixed-group comparison.
Simplicity is inherited from source 1.1.5(3)(a); no independent model simplicity
certificate or extra local-geometry hypothesis is assumed.

At the simple endpoint, the literal inner action constructs a compatible
Tits marking. Its first overgroup lies in M, while the second admits no
escaping short subnormal block. `not_tits_model` applies these calculations
to `Tits.ParrottGroup`, keeping it distinct from the full fixed group ²F₄(2).
No whole parabolic is identified with a block.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The large Ree fixed-group case is incompatible with the source local block
decompositions. The exceptional endomorphism remains an explicit construction
input in this version. The inner action of z is unnecessary for this exclusion. -/
theorem not_large_fixed_model (h : LocalSetup H L M S z) [IsSimpleGroup L]
    {m : ℕ} (hm : 1 ≤ m) (d : ReeF4.LocalBlockInput m) :
    ¬ Nonempty (L ≃* d.fixedGroup) := by
  rintro ⟨e⟩
  obtain ⟨p, _, _, he₁, he₂, hthree, hlayers⟩ :=
    large_exists_local_calculations h hm d e
  exact false_of_pair_calculations h p he₁ he₂ hthree hlayers

/-- Exclude every actual large Ree model in 1.1.5(3)(a), with the exceptional
endomorphism and its comparison to the model fully instantiated. -/
theorem not_isReeF4Model (h : LocalSetup H L M S z) [IsSimpleGroup L] :
    ¬ ReeF4.IsReeF4Model L := by
  rintro ⟨m, hm, ⟨e⟩⟩
  let d := ReeF4.canonicalLocalBlockInput m
  exact not_large_fixed_model h hm d ⟨e.trans d.modelEquiv.symm⟩

/-- The simple Tits endpoint of 1.1.5(3)(a) is incompatible with the source
local block decompositions. The marking and every local-overgroup premise
are constructed from the actual model and the literal inner action of z. -/
theorem not_tits_model (h : LocalSetup H L M S z)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ¬ Nonempty (L ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  obtain ⟨_, _, d, _, _, _, _, _, _, hleft, _, he₂, _, hlayers⟩ :=
    tits_exists_local_calculations h e α hα hinner
  exact false_of_right_calculations h d hleft he₂ hlayers

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
