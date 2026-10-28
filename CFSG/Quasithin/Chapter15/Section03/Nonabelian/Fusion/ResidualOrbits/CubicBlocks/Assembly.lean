module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.TensorCensus
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Transport

/-!
# The two cubic blocks and their actual four-orbit censuses

From the genuine s = 1 actions of 15.3.53–54, the relative centers and
fixed-lift geometry, `exists_source_cubic_blocks` constructs cubics assigned
to the two actual local planes. The assignment retains the permutation of
the two invariant natural summands. Each plane has order 32 and lies in its
assigned block. The singular commutator lines, cubic centralizer generators,
reductions into U and P-conjugacy on the exceptional affine cosets are all
retained for these same cubics.

The full ambient action realization and the proved finite tensor census
supply `BlockCensus` for each block: an actual E64 equivalence, invariance,
orbit lengths 9, 6, 12 and 36, exhaustive coverage, and generation of V by
each inside orbit. The source Sylow witness places both blocks in T ∩ K.
No census, block coordinates or local-plane reduction is an input.

The earlier layer actions, fixed-lift identities, actual local-product
isomorphism and markings remain explicit, as does the earlier Sylow witness.
Their source assembly belongs to the caller. The independent block-normalizer
motion and the final global two-class cover are not used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–59
and the proof of 15.3.61(2), printed pp.1146–1151. The corrected local planes
have order 32; neither the printed E16 cover nor transitivity between the
two invariant quotient summands is used.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
open Realization
variable {G : Type*} [Group G]

/-- The complete cubic-block branch, with both cubics indexed by the actual
local planes. The common actor image retains their natural-summand labels;
all structural, affine-fusion and census conclusions concern the same D_i.
The final two fields give the exact plane reduction and census family needed
by `residual_cover_of_local_geometry`, without assuming its two-class cover
or the independent moving-normalizer conclusion. -/
theorem exists_source_cubic_blocks [Finite G]
    (Z ZS T Y V : Subgroup G) (g : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    [IsExtraspecial 2 (closureU Z ZS)]
    {hIP : pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G)}
    {hIV : pairI Z ZS g ≤ normalizer (V : Set G)}
    (d : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV)
    (a : centralizerH Z)
    (e : (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel)
    (hLP : fixedLift Z ZS a ⊔ V ≤ pairP Z ZS g)
    (hcenter : V = (center (pairP Z ZS g)).map (pairP Z ZS g).subtype)
    (hUZ : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hUa : fixedLift Z ZS a = closureU Z ZS ⊓ centralizer (V : Set G))
    (hVU : V ≤ normalizer (closureU Z ZS : Set G))
    (hUcard : Nat.card (closureU Z ZS) = 128)
    (z : V) (hz : z ≠ 1) (hZ : zpowers (z : G) = Z)
    (hsing : (d.lowerCoordinates z).toAdd.det = 0)
    (hUV : closureU Z ZS ⊓ V = sourceHyperplane d z)
    (v : V) (hv : (d.lowerCoordinates v).toAdd.det ≠ 0)
    (S : Sylow 2 (pairI Z ZS g))
    (hS : (S : Subgroup (pairI Z ZS g)).map (pairI Z ZS g).subtype = residualSylow T Z) :
    ∃ D : Fin 2 → Subgroup G, ∃ ai : Fin 2 → G, ∃ σ : Equiv.Perm (Fin 2),
      (∀ i,
        D i ≤ pairI Z ZS g ∧ Nat.card (D i) = 3 ∧
        ((D i).subgroupOf (pairI Z ZS g)).map d.actor = complementaryCubic (σ i) ∧
        fusionBlock (pairP Z ZS g) V (D i) ≤ residualSylow T Z ∧
        Nat.card (fusionBlock (pairP Z ZS g) V (D i)) = 64 ∧
        IsElementaryAbelian 2 (fusionBlock (pairP Z ZS g) V (D i))) ∧
      (∀ i,
        let A := localPlane (fixedLift Z ZS a ⊔ V) e i
        Nat.card A = 32 ∧ IsElementaryAbelian 2 A ∧
        V ≤ A ∧ A ≤ summandPreimage d (σ i) ∧
        (∀ x ∈ A, ∀ b ∈ D i, MulAut.conj b x / x ∈ V) ∧
        A ≤ fusionBlock (pairP Z ZS g) V (D i) ∧
        Nat.card (A ⊓ centralizer (D i : Set G) : Subgroup G) = 2 ∧
        ai i ∈ A ⊓ centralizer (D i : Set G) ∧ orderOf (ai i) = 2 ∧
        zpowers (ai i) = A ⊓ centralizer (D i : Set G) ∧
        ai i ∉ V ∧ A = zpowers (ai i) ⊔ V) ∧
      (∀ i,
        ⁅Z, D i⁆ =
            (tensorCubicLine (σ i) (d.lowerCoordinates z)).map (tensorEmbedding d) ∧
        Nat.card (⁅Z, D i⁆ : Subgroup G) = 4 ∧
        ⁅Z, D i⁆ ≤ closureU Z ZS ⊓ V ∧
        ∀ w : V, (w : G) ∈ ⁅Z, D i⁆ →
          (d.lowerCoordinates w).toAdd.det = 0) ∧
      (∀ i,
        ⁅zpowers (ai i), pairP Z ZS g⁆ = ⁅Z, D i⁆ ∧
        ((ai i ∈ closureU Z ZS →
            ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
              ∃ b ∈ D i, MulAut.conj b x ∈ closureU Z ZS) ∧
          (ai i ∉ closureU Z ZS →
            ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
              x ∉ zpowers (ai i) ⊔ ⁅zpowers (ai i), pairP Z ZS g⁆ →
              ∃ b ∈ D i, MulAut.conj b x ∈ closureU Z ZS) ∧
          (∀ c₁ ∈ ⁅zpowers (ai i), pairP Z ZS g⁆,
            ∀ c₂ ∈ ⁅zpowers (ai i), pairP Z ZS g⁆,
              ∃ p ∈ pairP Z ZS g,
                MulAut.conj p (ai i * c₁) = ai i * c₂) ∧
          ((zpowers (ai i) ⊔ ⁅zpowers (ai i), pairP Z ZS g⁆ : Subgroup G) : Set G) =
            (zpowers (ai i) : Set G) *
              (⁅zpowers (ai i), pairP Z ZS g⁆ : Subgroup G))) ∧
      (∀ i, ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i, orderOf x = 2 →
        ∃ y, (y ∈ closureU Z ZS ∨ y ∈ fusionBlock (pairP Z ZS g) V (D i)) ∧
          ConjugateBy (pairI Z ZS g) x y) ∧
      Nonempty (∀ i, BlockCensus (pairI Z ZS g) (pairP Z ZS g) V (D i) (z : G) (v : G)) := by
  classical
  obtain ⟨D, hblocks, hplanes, σ, ai, hlocal, hlines, hreduce⟩ :=
    exists_source_cubic_realization Z ZS T Y V g d a e hLP hcenter hUZ hUa hVU
      hUcard z hz hZ hsing hUV v hv S hS
  refine ⟨fun i => D (σ i), ai, σ, ?_, ?_, ?_, hreduce, ?_, ?_⟩
  · intro i
    obtain ⟨hDI, hD, himage, hBT, hcard, helem, _⟩ := hblocks (σ i)
    exact ⟨hDI, hD, himage, hBT, hcard, helem⟩
  · intro i
    exact ⟨(hplanes i).1, (hplanes i).2, hlocal i⟩
  · intro i
    exact hlines (σ i)
  · intro i x hx _
    exact ⟨x, Or.inr ((hlocal i).2.2.2.1 hx), ConjugateBy.refl _ _⟩
  · have hc (i : Fin 2) :
        Nonempty (BlockCensus (pairI Z ZS g) (pairP Z ZS g) V (D (σ i))
          (z : G) (v : G)) := by
      obtain ⟨_, _, _, _, _, _, c, hcz, hcv⟩ := hblocks (σ i)
      exact ⟨blockCensus_of_coordinates c tensorCensus _ _ hcz hcv⟩
    exact ⟨fun i => Classical.choice (hc i)⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
