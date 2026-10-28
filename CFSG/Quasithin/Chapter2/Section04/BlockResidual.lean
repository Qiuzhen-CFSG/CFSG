module

public import CFSG.Quasithin.Chapter2.Section04.SourceSetup
public import Theory.GroupTheory.PResidual.ConjugateGeneration

/-!
# The block closure is the actual two-residual

In the selected minimal parabolic H = ⟨L,S⟩, the block L is two-perfect.
Thus its S-conjugates generate exactly O²(H). In particular their closure
L₀ is normal in H and H = L₀S. This supplies the literal residual K used
in C.5, rather than confusing it with O₂(H).

Source: Aschbacher–Smith §2.4, printed p.528; Hypothesis C.5.1, p.154.
All normality statements are internal to the selected H. The two-core
identity U₀ = O₂(L₀) from 2.4.5(4) is a later C.5 consequence.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] {M : Subgroup G}

/-- The source's L₀, before adjoining the Sylow subgroup. Taking all
S-conjugates gives the same subgroup with either conjugation convention. -/
def MinimalBlockSetup.L0 (d : MinimalBlockSetup M) : Subgroup d.H :=
  ⨆ s : (d.S : Subgroup d.H), d.block.map (MulAut.conj (s : d.H)).toMonoidHom

/-- The source's U₀, using the actual block commutator module. -/
def MinimalBlockSetup.U0 (d : MinimalBlockSetup M) : Subgroup d.H :=
  ⨆ s : (d.S : Subgroup d.H),
    ((ChapterC.blockU d.block).map d.block.subtype).map
      (MulAut.conj (s : d.H)).toMonoidHom

/-- Identify the source block closure with the two-residual. -/
theorem MinimalBlockSetup.L0_eq_residual (d : MinimalBlockSetup M) :
    d.L0 = pResidual 2 d.H :=
  (pResidual_eq_iSup_conjugates d.block (d.S : Subgroup d.H)
    d.block_type.1.short.twoPerfect d.S.isPGroup' d.generated).symm

/-- The selected block closure is normal in H. -/
theorem MinimalBlockSetup.L0_normal (d : MinimalBlockSetup M) : d.L0.Normal := by
  rw [d.L0_eq_residual]
  infer_instance

/-- The source's U₀ is a subgroup of the actual block closure. -/
theorem MinimalBlockSetup.U0_le_L0 (d : MinimalBlockSetup M) : d.U0 ≤ d.L0 :=
  iSup_mono fun _ => map_mono (map_subtype_le _)

/-- Adjoining S to the block closure recovers the whole selected parabolic. -/
theorem MinimalBlockSetup.L0_sup_sylow (d : MinimalBlockSetup M) :
    d.L0 ⊔ (d.S : Subgroup d.H) = ⊤ := by
  apply top_unique
  rw [← d.generated]
  exact sup_le_sup (le_iSup_conjugates d.block (d.S : Subgroup d.H)) le_rfl

/-- The same generation identity with the literal ambient maps. -/
theorem MinimalBlockSetup.ambient_L0_sup_sylow (d : MinimalBlockSetup M) :
    d.L0.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype = d.H := by
  rw [← Subgroup.map_sup, d.L0_sup_sylow, ← MonoidHom.range_eq_map, range_subtype]

/-- The source product H = L₀S is an elementwise product, not just generation. -/
theorem MinimalBlockSetup.factorization (d : MinimalBlockSetup M) (h : d.H) :
    ∃ l : d.L0, ∃ s : (d.S : Subgroup d.H), h = (l : d.H) * (s : d.H) := by
  let := d.L0_normal
  obtain ⟨l, hl, s, hs, he⟩ := mem_sup_of_normal_left.mp
    (show h ∈ d.L0 ⊔ (d.S : Subgroup d.H) by rw [d.L0_sup_sylow]; trivial)
  exact ⟨⟨l, hl⟩, ⟨s, hs⟩, he.symm⟩

end CFSG.Quasithin.Chapter2
