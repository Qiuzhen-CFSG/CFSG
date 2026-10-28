module

public import CFSG.Quasithin.Chapter12.Section08.Terminal.OrthogonalModels.EightResidual
public import CFSG.Quasithin.Chapter12.Section08.Terminal.OrthogonalModels.PairedBorel
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.Residuals
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Completed terminal orthogonal model calculations

The four-block residual supplies the E₁₆ kernel and E₉ quotient on the actual
dotted point stabilizer. Restricting the supplied ambient Sylow subgroup to
the normal A₈ component makes the rank bound available in either overgroup.
For the paired A₅ alternative, cubic generation of A₄ × A₄ discharges the
two-perfectness and three-rank premises of the geometric Borel calculation.
The concrete swapped model also gives the upper bound for the full stabilizer.

The final paired application uses Xdot = image(Wᵍ) and Z0 = image(Z(U)ᵍ)
under the literal faithful action quotient. It gives both three-rank two and
Z0 = 1 from the earlier source rank equation and total isotropy. The source
owner retains the independent argument that this rank forces Z0 ≠ 1, as well
as the component construction and the remaining conclusions of 12.8.13(5).
Only earlier geometric/action markings and source subgroup clauses remain
explicit; no residual, Borel, or rank conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.11.2(5),(12),
printed p.364, and the model calculations in 12.8.13(5),(7), printed pp.855–856.
-/

@[expose] public section
noncomputable section
open Subgroup Module
open scoped IsMulCommutative
open BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The full S₈ case has an explicit elementary-sixteen kernel and
elementary-nine quotient on its prime-to-three residual. -/
theorem terminal_symmetric_eight_residual_structure (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (e : F.TerminalHdot ≃* Equiv.Perm (Fin 8))
    (heq : ∀ (h : F.TerminalHdot) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h) (c (Additive.ofMul u)))
    (Q : Sylow 2 F.TerminalHdot) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    ∃ f : primeToResidual 3 (F.terminalPointStabilizer u) →* FourBlockResidual.E9,
      Function.Surjective f ∧ Nat.card f.ker = 16 ∧ IsElementaryAbelian 2 f.ker ∧
      Nonempty ((primeToResidual 3 (F.terminalPointStabilizer u)) ⧸ f.ker ≃*
        FourBlockResidual.E9) ∧
      primeRank 3 (primeToResidual 3 (F.terminalPointStabilizer u)) = 2 ∧
      primeRank 3 (F.terminalPointStabilizer u) = 2 := by
  obtain ⟨_, _, _, _, ⟨eR⟩, hrank⟩ :=
    F.terminal_symmetric_eight_residual_rank q c e heq Q u hu hfixed
  exact ⟨FourBlockResidual.markedQuotientMap eR,
    FourBlockResidual.markedQuotientMap_surjective eR,
    FourBlockResidual.markedQuotientMap_kernel_card eR, inferInstance,
    ⟨FourBlockResidual.markedQuotientEquiv eR⟩,
    (Theory.GroupTheory.primeRank_equiv 3 eR).trans FourBlockResidual.product_primeRank,
    hrank⟩

private theorem alternating_eight_ambient_data (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (K : Subgroup F.TerminalHdot) [K.Normal] (e : K ≃* alternatingGroup (Fin 8))
    (heq : ∀ (h : K) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h).val (c (Additive.ofMul u)))
    (Q : Sylow 2 F.TerminalHdot) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    Nonempty (primeToResidual 3 ((F.terminalPointStabilizer u).subgroupOf K) ≃*
      FourBlockResidual.Product) ∧
      primeRank 3 ((F.terminalPointStabilizer u).subgroupOf K) = 2 ∧
      2 ≤ primeRank 3 (F.terminalPointStabilizer u) := by
  obtain ⟨QK, hQK⟩ := Q.exists_subgroupOf_eq_of_normal K
  have hf : ∀ h ∈ (QK : Subgroup K), F.terminalFaithfulHatAction h u = u := by
    intro h hh
    apply hfixed h
    exact show h ∈ (Q : Subgroup F.TerminalHdot).subgroupOf K from hQK ▸ hh
  obtain ⟨_, _, _, _, heR, hrank⟩ :=
    F.terminal_alternating_eight_residual_rank q c K e heq QK u hu hf
  exact ⟨heR, hrank,
    F.terminal_alternating_eight_point_rank_ge q c K e heq QK u hu hf⟩

/-- The same calculation inside a normal A₈ component uses the restriction
of the original ambient Sylow, and bounds the full point centralizer below. -/
theorem terminal_alternating_eight_residual_structure (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (K : Subgroup F.TerminalHdot) [K.Normal] (e : K ≃* alternatingGroup (Fin 8))
    (heq : ∀ (h : K) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h).val (c (Additive.ofMul u)))
    (Q : Sylow 2 F.TerminalHdot) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    ∃ f : primeToResidual 3 ((F.terminalPointStabilizer u).subgroupOf K) →*
        FourBlockResidual.E9,
      Function.Surjective f ∧ Nat.card f.ker = 16 ∧ IsElementaryAbelian 2 f.ker ∧
      Nonempty ((primeToResidual 3 ((F.terminalPointStabilizer u).subgroupOf K)) ⧸ f.ker ≃*
        FourBlockResidual.E9) ∧
      primeRank 3 (primeToResidual 3 ((F.terminalPointStabilizer u).subgroupOf K)) = 2 ∧
      primeRank 3 ((F.terminalPointStabilizer u).subgroupOf K) = 2 ∧
      2 ≤ primeRank 3 (F.terminalPointStabilizer u) := by
  obtain ⟨⟨eR⟩, hrank, hge⟩ := alternating_eight_ambient_data F q c K e heq Q u hu hfixed
  exact ⟨FourBlockResidual.markedQuotientMap eR,
    FourBlockResidual.markedQuotientMap_surjective eR,
    FourBlockResidual.markedQuotientMap_kernel_card eR, inferInstance,
    ⟨FourBlockResidual.markedQuotientEquiv eR⟩,
    (Theory.GroupTheory.primeRank_equiv 3 eR).trans FourBlockResidual.product_primeRank,
    hrank, hge⟩

section Paired
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
  (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
  (c : q.IsometryEquiv PairedFive.form)
  (hq : ∀ (h : F.TerminalHdot) (u : F.Uhat),
    q (Additive.ofMul (F.terminalFaithfulHatAction h u)) = q (Additive.ofMul u))
  (hs : ∀ h, PairedBorel.PreservesSummandPair (F.terminalPairedLinearAction c.toLinearEquiv h))
  (L : Subgroup F.TerminalHdot) (eL : L ≃* PairedFive.Actor)
  (heL : ∀ (l : L) (u : F.Uhat),
    c (Additive.ofMul (F.terminalFaithfulHatAction l u)) =
      PairedFive.action (eL l) (c (Additive.ofMul u)))

include hq hs heL in
/-- The paired Borel and both three-ranks, with the numerical premises
discharged and all source subgroups still embedded in the faithful quotient. -/
theorem terminal_paired_borel_rank
    (X : Subgroup F.TerminalHdot) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 8) (x : F.TerminalHdot) (hx : x ∈ X)
    (hswap : ∀ v : PairedFive.Factor,
      (F.terminalPairedLinearAction c.toLinearEquiv x (v, 0)).1 = 0)
    (hsplit : X ≤ L ⊔ Subgroup.zpowers x)
    (Q : Sylow 2 F.TerminalHdot) (hXQ : X ≤ Q)
    (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    (pResidual 2 (F.terminalPointStabilizer u)).map (F.terminalPointStabilizer u).subtype =
        F.terminalPointStabilizer u ⊓ L ∧
      Nonempty (((F.terminalPointStabilizer u).subgroupOf L) ≃*
        (PairedBorel.A4 × PairedBorel.A4)) ∧
      Nonempty ((pResidual 2 (F.terminalPointStabilizer u)) ≃*
        (PairedBorel.A4 × PairedBorel.A4)) ∧
      primeRank 3 (pResidual 2 (F.terminalPointStabilizer u)) = 2 ∧
      primeRank 3 (F.terminalPointStabilizer u) = 2 := by
  obtain ⟨hr, hb, he, hd, hge⟩ := F.terminal_paired_residual_of_source q c hq hs L eL heL
    X hcard x hx hswap hsplit Q hXQ u hu hfixed
    FourBlockResidual.product_pResidual FourBlockResidual.product_primeRank
  refine ⟨hr, hb, he, hd, le_antisymm ?_ hge⟩
  obtain ⟨_, r, hinj, _⟩ :=
    F.terminal_paired_marking q c hq hs L eL heL X hcard x hx hswap hsplit Q hXQ
  exact (Theory.GroupTheory.primeRank_le_of_injective 3
    (r.comp (F.terminalPointStabilizer u).subtype)
    (hinj.comp (F.terminalPointStabilizer u).subtype_injective)).trans
      PairedBorel.model_threeRank_le

include hq hs heL in
/-- The two model consequences used on p.856, now on the literal Xdot and
Z0. The terminal owner combines these with its earlier-source implication
from point-centralizer three-rank greater than one to Z0 ≠ 1. -/
theorem terminal_paired_source_rank_and_center [IsMulCommutative V]
    (hn : 1 ≤ n) (g : G) (hU : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hpolar : ∀ a b : F.U,
      q.polarBilin (Additive.ofMul (QuotientGroup.mk' (center F.U) a))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) b)) = 0 ↔ Commute a b)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hcard : Nat.card (F.terminalDot (F.X g)) = 8)
    (x : F.TerminalHdot) (hx : x ∈ F.terminalDot (F.X g))
    (hswap : ∀ v : PairedFive.Factor,
      (F.terminalPairedLinearAction c.toLinearEquiv x (v, 0)).1 = 0)
    (hsplit : F.terminalDot (F.X g) ≤ L ⊔ Subgroup.zpowers x)
    (Q : Sylow 2 F.TerminalHdot) (hXQ : F.terminalDot (F.X g) ≤ Q)
    (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u)
    (hbalance : finrank (ZMod 2) (Symplectic.hatSpace F (F.E g)) +
      finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) = 7) :
    (pResidual 2 (F.terminalPointStabilizer u)).map (F.terminalPointStabilizer u).subtype =
        F.terminalPointStabilizer u ⊓ L ∧
      primeRank 3 (pResidual 2 (F.terminalPointStabilizer u)) = 2 ∧
      primeRank 3 (F.terminalPointStabilizer u) = 2 ∧
      F.terminalDot (conjugate F.ZU g) = ⊥ := by
  obtain ⟨hr, _, _, hd, hs'⟩ := F.terminal_paired_borel_rank q c hq hs L eL heL
    (F.terminalDot (F.X g)) hcard x hx hswap hsplit Q hXQ u hu hfixed
  exact ⟨hr, hd, hs', F.terminal_paired_rank_balance_center_eq_bot hn g hU hPhi hdis
    q c hpolar hcard hbalance⟩

end Paired
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
