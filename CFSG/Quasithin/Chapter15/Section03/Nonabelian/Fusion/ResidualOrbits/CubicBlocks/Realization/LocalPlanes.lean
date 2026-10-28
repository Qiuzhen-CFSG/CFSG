module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Summands
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Centralizers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Orthogonality
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.SingularLines
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.AffineFusion

/-!
# Actual local planes and their assigned cubics

`exists_localPlane_cubic_data` constructs the permutation aligning the actual
order-32 local planes with the natural summands. It proves the literal
fixed-quotient condition, embeds each plane in its assigned cubic block, and
constructs an ambient involution generating its order-two cubic centralizer.
The proof uses the actual local product equivalence and the conditional
`PairingFormula`; their source construction belongs to the respective owners.

`sourceHyperplane` uses the determinant polarization on the supplied lower
coordinates. The theorem `exists_localPlane_cubic_reductions` assembles the
singular-line identification and intermediate fusion calculations from those
interfaces. In particular, its conjugation reductions into U are derived from
the literal commutator line and the determinant hyperplane, rather than from
plane-to-block containment alone.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–55
and 15.3.61(2), printed pp.1146–1147 and 1150–1151. The local product has
two elementary planes of order 32; the printed E16 cover is not used.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

variable {G : Type*} [Group G]

/-- The complete local-plane reduction package used in the first part of
15.3.61(2).  The permutation is produced by the actual local-product
equivalence, so the two planes are never given arbitrary labels.  The
commutator-line and affine-fusion conclusions are then connected through the
same ambient generators and the same assigned cubics.

The source inputs retained here are the relative center, the extraspecial
closure and its fixed lift, the determinant hyperplane intersection, and the
actual actor image of each order-three subgroup.  In particular, no plane
coordinates or fusion orbit is assumed. -/
theorem exists_localPlane_cubic_reductions [Finite G]
    (Z ZS Y V : Subgroup G) (g : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    [IsExtraspecial 2 (closureU Z ZS)]
    {hIP : pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G)}
    {hIV : pairI Z ZS g ≤ normalizer (V : Set G)}
    (d : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV)
    (hf : PairingFormula d) (a : centralizerH Z)
    (e : (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel)
    (hLP : fixedLift Z ZS a ⊔ V ≤ pairP Z ZS g)
    (hcenter : V = (center (pairP Z ZS g)).map (pairP Z ZS g).subtype)
    (hUZ : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hUa : fixedLift Z ZS a = closureU Z ZS ⊓ centralizer (V : Set G))
    (hVU : V ≤ normalizer (closureU Z ZS : Set G))
    (_hUcard : Nat.card (closureU Z ZS) = 128)
    (z : V) (hz : z ≠ 1) (hZ : zpowers (z : G) = Z)
    (hsing : (d.lowerCoordinates z).toAdd.det = 0)
    (hUV : closureU Z ZS ⊓ V = sourceHyperplane d z)
    (D : Fin 2 → Subgroup G) (hDI : ∀ j, D j ≤ pairI Z ZS g)
    (hD : ∀ j, Nat.card (D j) = 3)
    (himage : ∀ j,
      ((D j).subgroupOf (pairI Z ZS g)).map d.actor = complementaryCubic j) :
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
  have hcentral : V ≤ centralizer (pairP Z ZS g : Set G) := by
    rw [hcenter]
    rintro v ⟨vP, hvP, rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp hvP ⟨x, hx⟩)
  have hUaU : fixedLift Z ZS a ≤ closureU Z ZS := by
    rw [hUa]
    exact inf_le_left
  obtain ⟨σ, hσ⟩ := exists_localPlane_cubic_data Z ZS Y V g d hf a e hLP hcentral
    D hDI hD himage
  have hex (i : Fin 2) : ∃ ai : G,
      ai ∈ localPlane (fixedLift Z ZS a ⊔ V) e i ⊓
        centralizer (D (σ i) : Set G) ∧
      orderOf ai = 2 ∧
      zpowers ai = localPlane (fixedLift Z ZS a ⊔ V) e i ⊓
        centralizer (D (σ i) : Set G) ∧
      ai ∉ V ∧
      localPlane (fixedLift Z ZS a ⊔ V) e i = zpowers ai ⊔ V :=
    (hσ i).2.2.2.2.2
  choose ai hai hai2 haiV haiA haiEq using hex
  have hbase (i : Fin 2) :
      V ≤ localPlane (fixedLift Z ZS a ⊔ V) e i ∧
      localPlane (fixedLift Z ZS a ⊔ V) e i ≤ summandPreimage d (σ i) ∧
      (∀ x ∈ localPlane (fixedLift Z ZS a ⊔ V) e i,
        ∀ b ∈ D (σ i), MulAut.conj b x / x ∈ V) ∧
      localPlane (fixedLift Z ZS a ⊔ V) e i ≤
        fusionBlock (pairP Z ZS g) V (D (σ i)) ∧
      Nat.card (localPlane (fixedLift Z ZS a ⊔ V) e i ⊓
        centralizer (D (σ i) : Set G) : Subgroup G) = 2 := by
    exact ⟨(hσ i).1, (hσ i).2.1, (hσ i).2.2.1, (hσ i).2.2.2.1,
      (hσ i).2.2.2.2.1⟩
  have hplanes : ∀ i,
      localPlane (fixedLift Z ZS a ⊔ V) e i ≤ summandPreimage d (σ i) :=
    fun i => (hbase i).2.1
  have hlines := localPlane_singular_commutator_lines Z ZS Y V g d hf a e hLP hcenter
    hUZ hUa z hz hZ hsing hUV D hDI himage σ ai hplanes
    hai hai2 haiA
  refine ⟨σ, ai, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    exact ⟨(hσ i).1, (hσ i).2.1, (hσ i).2.2.1,
      (hσ i).2.2.2.1, (hσ i).2.2.2.2.1, hai i, hai2 i,
      haiV i, haiA i, haiEq i⟩
  · exact hlines.1
  · intro i
    have hline : ⁅zpowers (ai i), pairP Z ZS g⁆ =
        (tensorCubicLine (σ i) (d.lowerCoordinates z)).map (tensorEmbedding d) :=
      (hlines.2 i).trans (hlines.1 (σ i)).1
    have hred := AffineFusion.local_plane_affine_fusion d
      (le_sup_right.trans hLP) hcentral (σ i)
      (D (σ i)) (hDI _) (hD _) (himage _) z hz hsing
      (closureU Z ZS) (fixedLift Z ZS a) hUaU hVU hLP hUV
      (localPlane (fixedLift Z ZS a ⊔ V) e i) (localPlane_le _ e i)
      (hbase i |>.1) (ai i) (hai i) (hai2 i) (haiA i) (haiEq i) hline
    exact ⟨(hlines.2 i), hred⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
