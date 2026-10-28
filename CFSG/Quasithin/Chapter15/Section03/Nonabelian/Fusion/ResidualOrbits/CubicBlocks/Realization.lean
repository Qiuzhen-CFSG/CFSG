module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Lifting
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Splitting
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LiftedAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes

/-!
# Construction and action of the two actual cubic blocks

The common earlier actions on V and P/V construct two actual order-three
subgroups of I, one for each natural quotient summand. Coprime lifting
identifies their blocks with the two summand inverse images. Ambient
multiplication and the literal quotient map construct the six coordinates.
The tensor commutator pairing, together with the cubic-normalizer Frattini
factorization, proves equality with the full displayed transformation family.

`exists_source_cubic_realization` assembles this action with the corrected
order-32 local planes, their singular commutator lines and affine fusion
reductions. It uses the same cubics throughout and discharges `PairingFormula`
from the genuine earlier layer actions and relative center. The determinant
markings identify the source z and v, and the actual 15.3.59 Sylow witness
places both blocks in T ∩ K.

Earlier fixed-lift identities, the actual local-product equivalence and the
source layer actions remain explicit inputs. The independent tensor census,
moving-block-normalizer calculation and final two-class cover are not used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–59
and 15.3.61(2), printed pp.1146–1151. No printed E16 cover is asserted.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
variable {G : Type*} [Group G]

/-- Source 15.3.59(2) places the literal two-core in the residual Sylow group. -/
theorem pairP_le_residualSylow_of_sylow (Z ZS T : Subgroup G) (g : G)
    (S : Sylow 2 (pairI Z ZS g))
    (hS : (S : Subgroup (pairI Z ZS g)).map (pairI Z ZS g).subtype = residualSylow T Z) :
    pairP Z ZS g ≤ residualSylow T Z := by
  rw [← hS]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal S)

/-- The actual Sylow information, together with V ≤ P, places every cubic block. -/
theorem block_le_residualSylow_of_sylow (Z ZS T V D : Subgroup G) (g : G)
    (hVP : V ≤ pairP Z ZS g) (S : Sylow 2 (pairI Z ZS g))
    (hS : (S : Subgroup (pairI Z ZS g)).map (pairI Z ZS g).subtype = residualSylow T Z) :
    fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z :=
  fusionBlock_le_residualSylow T Z ZS V D g hVP
    (pairP_le_residualSylow_of_sylow Z ZS T g S hS)

/-- Both cubics and both actual block equivalences, from the earlier two-layer
source action. `exists_source_cubic_realization` additionally supplies the
full conjugation action and the local-plane reductions. -/
theorem exists_source_blocks [Finite G] (Z ZS T Y V : Subgroup G) (g : G)
    (hIP : pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G))
    (hIV : pairI Z ZS g ≤ normalizer (V : Set G))
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    (d : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV)
    (hVP : V ≤ pairP Z ZS g)
    (hcentral : V ≤ centralizer (pairP Z ZS g : Set G))
    (S : Sylow 2 (pairI Z ZS g))
    (hS : (S : Subgroup (pairI Z ZS g)).map (pairI Z ZS g).subtype = residualSylow T Z) :
    ∃ D : Fin 2 → Subgroup G, ∀ i,
      D i ≤ pairI Z ZS g ∧ Nat.card (D i) = 3 ∧
      ((D i).subgroupOf (pairI Z ZS g)).map d.actor = complementaryCubic i ∧
      fusionBlock (pairP Z ZS g) V (D i) = summandPreimage d i ∧
      pairI Z ZS g ≤ normalizer (fusionBlock (pairP Z ZS g) V (D i) : Set G) ∧
      fusionBlock (pairP Z ZS g) V (D i) ≤ residualSylow T Z ∧
      ∃ e : fusionBlock (pairP Z ZS g) V (D i) ≃* BlockModel,
        ∀ x : fusionBlock (pairP Z ZS g) V (D i), (x : G) ∈ V ↔ e x ∈ modelV := by
  choose D hDI hD himage using (fun i => exists_complementary_cubic d hVP i)
  refine ⟨D, fun i => ⟨hDI i, hD i, himage i, ?_, ?_, ?_, ?_⟩⟩
  · exact fusionBlock_eq_summandPreimage d hVP i (D i) (hDI i) (hD i) (himage i)
  · rw [fusionBlock_eq_summandPreimage d hVP i (D i) (hDI i) (hD i) (himage i)]
    exact normalizes_summandPreimage d i
  · exact block_le_residualSylow_of_sylow Z ZS T V (D i) g hVP S hS
  · exact ⟨blockEquiv d hVP hcentral i (D i) (hDI i) (hD i) (himage i),
      blockEquiv_distinguished d hVP hcentral i (D i) (hDI i) (hD i) (himage i)⟩

/-- Actual cubic-block realization from the genuine earlier action, relative
center, fixed-lift and Sylow conclusions. The same chosen cubics carry the full
six-coordinate conjugation action and all the local-plane reductions. In
particular, neither the square/commutator formulas nor the lifted action is
assumed. The independent finite orbit census and final global fusion remain
with the source-theorem assembly owner. -/
theorem exists_source_cubic_realization [Finite G]
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
    ∃ D : Fin 2 → Subgroup G,
      (∀ j,
        D j ≤ pairI Z ZS g ∧ Nat.card (D j) = 3 ∧
        ((D j).subgroupOf (pairI Z ZS g)).map d.actor = complementaryCubic j ∧
        fusionBlock (pairP Z ZS g) V (D j) ≤ residualSylow T Z ∧
        Nat.card (fusionBlock (pairP Z ZS g) V (D j)) = 64 ∧
        IsElementaryAbelian 2 (fusionBlock (pairP Z ZS g) V (D j)) ∧
        ∃ c : BlockCoordinates (pairI Z ZS g) (pairP Z ZS g) V (D j),
          Singular (c.equiv ⟨z,
            (show V ≤ fusionBlock (pairP Z ZS g) V (D j) from le_sup_right) z.property⟩) ∧
          Nonsingular (c.equiv ⟨v,
            (show V ≤ fusionBlock (pairP Z ZS g) V (D j) from le_sup_right) v.property⟩)) ∧
      (∀ i, Nat.card (localPlane (fixedLift Z ZS a ⊔ V) e i) = 32 ∧
        IsElementaryAbelian 2 (localPlane (fixedLift Z ZS a ⊔ V) e i)) ∧
    ∃ σ : Equiv.Perm (Fin 2), ∃ ai : Fin 2 → G,
      (∀ i,
        let A := localPlane (fixedLift Z ZS a ⊔ V) e i
        V ≤ A ∧ A ≤ summandPreimage d (σ i) ∧
        (∀ x ∈ A, ∀ b ∈ D (σ i), MulAut.conj b x / x ∈ V) ∧
        A ≤ fusionBlock (pairP Z ZS g) V (D (σ i)) ∧
        Nat.card (A ⊓ centralizer (D (σ i) : Set G) : Subgroup G) = 2 ∧
        ai i ∈ A ⊓ centralizer (D (σ i) : Set G) ∧ orderOf (ai i) = 2 ∧
        zpowers (ai i) = A ⊓ centralizer (D (σ i) : Set G) ∧
        ai i ∉ V ∧ A = zpowers (ai i) ⊔ V) ∧
      (∀ j,
        ⁅Z, D j⁆ =
            (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d) ∧
        Nat.card (⁅Z, D j⁆ : Subgroup G) = 4 ∧
        ⁅Z, D j⁆ ≤ closureU Z ZS ⊓ V ∧
        ∀ v : V, (v : G) ∈ ⁅Z, D j⁆ →
          (d.lowerCoordinates v).toAdd.det = 0) ∧
      (∀ i,
        ⁅zpowers (ai i), pairP Z ZS g⁆ = ⁅Z, D (σ i)⁆ ∧
        ((ai i ∈ closureU Z ZS →
            ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
              ∃ b ∈ D (σ i), MulAut.conj b x ∈ closureU Z ZS) ∧
          (ai i ∉ closureU Z ZS →
            ∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
              x ∉ zpowers (ai i) ⊔ ⁅zpowers (ai i), pairP Z ZS g⁆ →
              ∃ b ∈ D (σ i), MulAut.conj b x ∈ closureU Z ZS) ∧
          (∀ c₁ ∈ ⁅zpowers (ai i), pairP Z ZS g⁆,
            ∀ c₂ ∈ ⁅zpowers (ai i), pairP Z ZS g⁆,
              ∃ p ∈ pairP Z ZS g,
                MulAut.conj p (ai i * c₁) = ai i * c₂) ∧
          ((zpowers (ai i) ⊔ ⁅zpowers (ai i), pairP Z ZS g⁆ : Subgroup G) : Set G) =
            (zpowers (ai i) : Set G) *
              (⁅zpowers (ai i), pairP Z ZS g⁆ : Subgroup G))) := by
  have hVP : V ≤ pairP Z ZS g := le_sup_right.trans hLP
  have hPI : pairP Z ZS g ≤ pairI Z ZS g := map_subtype_le _
  have hcentral : V ≤ centralizer (pairP Z ZS g : Set G) := by
    rw [hcenter]
    rintro v ⟨vP, hvP, rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp hvP ⟨x, hx⟩)
  choose D hDI hD himage using (fun i => exists_complementary_cubic d hVP i)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro j
    refine ⟨hDI j, hD j, himage j,
      block_le_residualSylow_of_sylow Z ZS T V (D j) g hVP S hS,
      fusionBlock_card d hVP hcentral j (D j) (hDI j) (hD j) (himage j),
      fusionBlock_elementary d hVP hcentral j (D j) (hDI j) (hD j) (himage j), ?_⟩
    refine ⟨blockCoordinates d hVP j (D j) (hDI j) (hD j) (himage j) hPI hcenter, ?_, ?_⟩
    · rw [blockCoordinates_equiv d hVP hcentral]
      exact blockEquiv_singular d hVP hcentral j (D j) (hDI j) (hD j) (himage j)
        z (fun h => hz (Subtype.ext h)) hsing
    · rw [blockCoordinates_equiv d hVP hcentral]
      exact blockEquiv_nonsingular d hVP hcentral j (D j) (hDI j) (hD j) (himage j) v hv
  · intro i
    exact ⟨localPlane_card _ e i, localPlane_elementary _ e i⟩
  · exact exists_localPlane_cubic_reductions Z ZS Y V g d
      (pairingFormula_of_layerActions d hVP hcenter) a e hLP hcenter hUZ hUa hVU hUcard
      z hz hZ hsing hUV D hDI hD himage

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
