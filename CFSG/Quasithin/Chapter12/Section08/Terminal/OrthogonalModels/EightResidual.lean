module

public import CFSG.Quasithin.Chapter12.Section08.Terminal.OrthogonalModels
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidual

/-!
# The terminal orthogonal eight-point residuals

The quadratic, equivariant markings of the literal dotted quotient identify
its point stabilizers with the unordered four-block stabilizers in S₈ and A₈.
The embedded prime-to-three residual is the same block product A₄ × A₄ in
both cases. The statements retain the conjugating permutation and the map
from the actual stabilizer, and establish three-rank two without assuming
any residual structure or nontriviality of the dotted conjugate center.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.11.2(5),
printed p.364, and the point-centralizer calculation in 12.8.13(5), pp.855–856.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
open BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private def markedSubgroupEquiv {A B : Type*} [Group A] [Group B]
    (U : Subgroup A) (W : Subgroup B) (e : A ≃* B)
    (he : ∀ a, a ∈ U ↔ e a ∈ W) : U ≃* W where
  toFun a := ⟨e a, (he a).mp a.property⟩
  invFun b := ⟨e.symm b, (he _).mpr (by rw [e.apply_symm_apply]; exact b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (e.map_mul a b)

private def evenBlockEquiv :
    FourBlockResidual.H.subgroupOf (alternatingGroup (Fin 8)) ≃* FourBlockResidual.P where
  toFun a := ⟨a.val.val, a.val.property, a.property⟩
  invFun a := ⟨⟨a.val, a.property.1⟩, a.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The S₈ marking identifies the actual residual image and its product
structure, as well as the full point stabilizer's three-rank. -/
theorem terminal_symmetric_eight_residual_rank (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (e : F.TerminalHdot ≃* Equiv.Perm (Fin 8))
    (heq : ∀ (h : F.TerminalHdot) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h) (c (Additive.ofMul u)))
    (Q : Sylow 2 F.TerminalHdot) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    ∃ r : Equiv.Perm (Fin 8),
      ∃ s : F.terminalPointStabilizer u ≃* FourBlockResidual.H,
        (∀ h, (s h : Equiv.Perm (Fin 8)) = r * e h * r⁻¹) ∧
        (primeToResidual 3 (F.terminalPointStabilizer u)).map
          (FourBlockResidual.H.subtype.comp s.toMonoidHom) = FourBlockResidual.R ∧
        Nonempty (primeToResidual 3 (F.terminalPointStabilizer u) ≃* FourBlockResidual.Product) ∧
        primeRank 3 (F.terminalPointStabilizer u) = 2 := by
  obtain ⟨r, hr⟩ := F.terminal_symmetric_eight_stabilizer q c e heq Q u hu hfixed
  let s := markedSubgroupEquiv (F.terminalPointStabilizer u) FourBlockResidual.H
    (e.trans (MulAut.conj r)) (fun h => (F.mem_terminalPointStabilizer u h).trans (hr h))
  refine ⟨r, s, (fun _ => rfl), ?_, ?_, ?_⟩
  · rw [← map_map, map_primeToResidual, FourBlockResidual.H_residual]
  · exact ⟨(primeToResidualEquiv 3 s).trans
      (FourBlockResidual.residualEquiv _ FourBlockResidual.R_le_H le_rfl)⟩
  · rw [Theory.GroupTheory.primeRank_equiv 3 s, FourBlockResidual.H_primeRank]

/-- The A₈ marking computes the stabilizer inside the actual marked component.
Its embedding into the dotted group is unchanged. -/
theorem terminal_alternating_eight_residual_rank (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (K : Subgroup F.TerminalHdot) (e : K ≃* alternatingGroup (Fin 8))
    (heq : ∀ (h : K) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h).val (c (Additive.ofMul u)))
    (Q : Sylow 2 K) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup K), F.terminalFaithfulHatAction h u = u) :
    ∃ r : alternatingGroup (Fin 8),
      ∃ s : (F.terminalPointStabilizer u).subgroupOf K ≃* FourBlockResidual.P,
        (∀ h, (s h : Equiv.Perm (Fin 8)) = r.val * (e h).val * r.val⁻¹) ∧
        (primeToResidual 3 ((F.terminalPointStabilizer u).subgroupOf K)).map
          (FourBlockResidual.P.subtype.comp s.toMonoidHom) = FourBlockResidual.R ∧
        Nonempty (primeToResidual 3 ((F.terminalPointStabilizer u).subgroupOf K) ≃*
          FourBlockResidual.Product) ∧
        primeRank 3 ((F.terminalPointStabilizer u).subgroupOf K) = 2 := by
  obtain ⟨r, hr⟩ := F.terminal_alternating_eight_stabilizer q c K e heq Q u hu hfixed
  let s₀ := markedSubgroupEquiv ((F.terminalPointStabilizer u).subgroupOf K)
    (FourBlockResidual.H.subgroupOf (alternatingGroup (Fin 8)))
    (e.trans (MulAut.conj r)) (fun h => hr h)
  let s := s₀.trans evenBlockEquiv
  refine ⟨r, s, (fun _ => rfl), ?_, ?_, ?_⟩
  · rw [← map_map, map_primeToResidual, FourBlockResidual.P_residual]
  · exact ⟨(primeToResidualEquiv 3 s).trans
      (FourBlockResidual.residualEquiv _ FourBlockResidual.R_le_P inf_le_right)⟩
  · rw [Theory.GroupTheory.primeRank_equiv 3 s, FourBlockResidual.P_primeRank]

/-- The marked A₈ component already forces rank at least two in the full
point centralizer. This is the model input to the earlier-source argument
forcing nontrivial dotted conjugate center. -/
theorem terminal_alternating_eight_point_rank_ge (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (K : Subgroup F.TerminalHdot) (e : K ≃* alternatingGroup (Fin 8))
    (heq : ∀ (h : K) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h).val (c (Additive.ofMul u)))
    (Q : Sylow 2 K) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup K), F.terminalFaithfulHatAction h u = u) :
    2 ≤ primeRank 3 (F.terminalPointStabilizer u) := by
  obtain ⟨r, s, _, _, _, hs⟩ :=
    F.terminal_alternating_eight_residual_rank q c K e heq Q u hu hfixed
  let f : (F.terminalPointStabilizer u).subgroupOf K →* F.terminalPointStabilizer u :=
    { toFun := fun a => ⟨a.val.val, a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    have hv : (a.val : F.TerminalHdot) = (b.val : F.TerminalHdot) :=
      congrArg (fun z : F.terminalPointStabilizer u => (z : F.TerminalHdot)) h
    exact Subtype.ext (Subtype.ext hv)
  rw [← hs]
  exact Theory.GroupTheory.primeRank_le_of_injective 3 f hf

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
