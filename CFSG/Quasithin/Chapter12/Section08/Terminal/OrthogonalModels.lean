module

public import CFSG.Quasithin.Chapter12.Section08.Terminal.Quotients
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Intersection
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal
public import Theory.Representation.BinaryPermutation.EightSylowFixed


/-!
# Terminal applications of the concrete orthogonal modules

The action of H on U/Z(U) descends faithfully through its literal kernel
quotient. Quadratic, equivariant markings transport the symmetric-eight
stabilizer and the paired alternating-five point calculation to this action.
The paired calculation keeps the actual factor subgroup, its two action maps,
and an element inducing the literal swap; the three marked elements must lie
in the actual ambient Sylow subgroup.

For the rank obstruction, Ehat is the image of W ∩ W^g in U/Z(U), Xdot is
the image of W^g in the faithful action quotient, and Z0 is the image of
Z(U)^g there. The earlier Frattini and commutator-form clauses prove total
isotropy using 12.8.11(2). The rank equation of 12.8.11(5), together with the
order-eight alternative, forces Z0 to be trivial. The source owner must still
prove its nontriviality using the three-rank of the model point centralizer;
that assertion is not assumed here as a model fact.

The module markings, Frattini/disjointness clauses and rank equation remain
explicit earlier-source inputs. This is not an unconditional proof of
12.8.13(5) or (7). Source: Aschbacher–Smith, combined manuscript of
1 March 2004, G.11.2(5),(12), printed p.364, and 12.8.13, pp.855–856.
-/

@[expose] public section

open Subgroup Module
open scoped IsMulCommutative
open BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The literal faithful action of the dotted quotient on U/Z(U). -/
noncomputable def terminalFaithfulHatAction (F : InvariantFlag T V n) :
    F.TerminalHdot →* MulAut F.Uhat := QuotientGroup.kerLift F.terminalHatAction

lemma terminalFaithfulHatAction_injective (F : InvariantFlag T V n) :
    Function.Injective F.terminalFaithfulHatAction :=
  QuotientGroup.kerLift_injective F.terminalHatAction

lemma terminalFaithfulHatAction_apply_mk (F : InvariantFlag T V n)
    (h : F.H) (u : F.Uhat) :
    F.terminalFaithfulHatAction (QuotientGroup.mk' F.terminalHatAction.ker h) u =
      F.terminalHatAction h u := rfl

/-- The point centralizer for the faithful dotted action. This shared
subgroup is the target of the two independent residual calculations. -/
noncomputable def terminalPointStabilizer (F : InvariantFlag T V n) (u : F.Uhat) :
    Subgroup F.TerminalHdot :=
  letI := MulAction.compHom F.Uhat F.terminalFaithfulHatAction
  MulAction.stabilizer F.TerminalHdot u

lemma mem_terminalPointStabilizer (F : InvariantFlag T V n)
    (u : F.Uhat) (h : F.TerminalHdot) :
    h ∈ F.terminalPointStabilizer u ↔ F.terminalFaithfulHatAction h u = u := by rfl

/-- The S₈ overgroup case, retaining a quadratic equivariant marking. -/
lemma terminal_symmetric_eight_stabilizer [Finite G] (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (e : F.TerminalHdot ≃* Equiv.Perm (Fin 8))
    (heq : ∀ (h : F.TerminalHdot) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h) (c (Additive.ofMul u)))
    (Q : Sylow 2 F.TerminalHdot) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    ∃ r : Equiv.Perm (Fin 8), ∀ h : F.TerminalHdot,
      F.terminalFaithfulHatAction h u = u ↔
        r * e h * r⁻¹ ∈
          Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
  have hv : c (Additive.ofMul u) ≠ 0 := by
    intro hz
    apply hu
    have he := c.injective (hz.trans c.map_zero.symm)
    exact he
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hf : ∀ g ∈ (Q' : Subgroup (Equiv.Perm (Fin 8))),
      BinaryPermutation.naturalRepresentation (Fin 8) g (c (Additive.ofMul u)) =
        c (Additive.ofMul u) := by
    rintro g ⟨h, hh, rfl⟩
    change BinaryPermutation.naturalRepresentation (Fin 8) (e h) (c (Additive.ofMul u)) = _
    rw [← heq, hfixed h hh]
  obtain ⟨r, hr⟩ := BinaryPermutation.EightSylowFixed.exists_conjugate_stabilizer
    Q' (c (Additive.ofMul u)) hv hf
  refine ⟨r, fun h => ?_⟩
  rw [← hr (e h), ← heq]
  exact c.injective.eq_iff.symm

/-- The A₈ component case. The stabilizer is calculated inside the literal
marked subgroup of the dotted group, so this also applies in an overgroup. -/
lemma terminal_alternating_eight_stabilizer [Finite G] (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv Eight.form)
    (K : Subgroup F.TerminalHdot) (e : K ≃* alternatingGroup (Fin 8))
    (heq : ∀ (h : K) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (e h).val (c (Additive.ofMul u)))
    (Q : Sylow 2 K) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup K), F.terminalFaithfulHatAction h u = u) :
    ∃ r : alternatingGroup (Fin 8), ∀ h : K,
      F.terminalFaithfulHatAction h u = u ↔
        r.val * (e h).val * r.val⁻¹ ∈
          Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
  have hv : c (Additive.ofMul u) ≠ 0 := by
    intro hz
    exact hu (c.injective (hz.trans c.map_zero.symm))
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hf : ∀ g ∈ (Q' : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.naturalRepresentation (Fin 8) g.val (c (Additive.ofMul u)) =
        c (Additive.ofMul u) := by
    rintro g ⟨h, hh, rfl⟩
    change BinaryPermutation.naturalRepresentation (Fin 8) (e h).val
      (c (Additive.ofMul u)) = _
    rw [← heq, hfixed h hh]
  obtain ⟨r, hr⟩ := Eight.alternating_exists_conjugate_stabilizer
    Q' (c (Additive.ofMul u)) hv hf
  refine ⟨r, fun h => ?_⟩
  rw [← hr (e h).val, ← heq]
  exact c.injective.eq_iff.symm

/-- Stabilizer inside the actual paired component, with the swap and Sylow
markings retained. -/
lemma terminal_paired_stabilizer (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv PairedFive.form)
    (L : Subgroup F.TerminalHdot) (e : L ≃* PairedFive.Actor)
    (heq : ∀ (h : L) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
        PairedFive.action (e h) (c (Additive.ofMul u)))
    (x : F.TerminalHdot)
    (hswap : ∀ u : F.Uhat, c (Additive.ofMul (F.terminalFaithfulHatAction x u)) =
      PairedFive.swap (c (Additive.ofMul u)))
    (Q : Sylow 2 F.TerminalHdot)
    (ha : (e.symm (BinaryPermutation.CubicFixedSpace.Five.first,
      BinaryPermutation.CubicFixedSpace.Five.first) : F.TerminalHdot) ∈ Q)
    (hb : (e.symm (BinaryPermutation.CubicFixedSpace.Five.second,
      BinaryPermutation.CubicFixedSpace.Five.second) : F.TerminalHdot) ∈ Q)
    (hx : x ∈ Q) (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u) :
    ∀ h : L, F.terminalFaithfulHatAction h u = u ↔
      (e h).1.val 4 = 4 ∧ (e h).2.val 4 = 4 := by
  have hv : c (Additive.ofMul u) ≠ 0 := by
    intro hz
    exact hu (c.injective (hz.trans c.map_zero.symm))
  have hp : c (Additive.ofMul u) = PairedFive.point := by
    apply PairedFive.eq_point_of_fixed _ hv
    · have hh := heq (e.symm (BinaryPermutation.CubicFixedSpace.Five.first,
        BinaryPermutation.CubicFixedSpace.Five.first)) u
      rw [hfixed _ ha, e.apply_symm_apply] at hh
      exact hh.symm
    · have hh := heq (e.symm (BinaryPermutation.CubicFixedSpace.Five.second,
        BinaryPermutation.CubicFixedSpace.Five.second)) u
      rw [hfixed _ hb, e.apply_symm_apply] at hh
      exact hh.symm
    · rw [← hswap, hfixed x hx]
  intro h
  rw [← PairedFive.point_fixed_iff, ← hp, ← heq]
  exact c.injective.eq_iff.symm

/-- Z(U)^g maps into the image of W^g under the same quotient map. -/
lemma terminalDot_conjugateCenter_le_X (F : InvariantFlag T V n) (g : G) :
    F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) := by
  have hZW : F.ZU ≤ F.W := by
    rintro z ⟨z, hz, rfl⟩
    refine ⟨z.property, ?_⟩
    intro v hv
    have hvU : v ∈ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H) hv
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨v, hvU⟩)
  exact map_mono (subgroupOf_mono F.H (map_mono hZW))

/-- The rank equation and the genuine paired quadratic coordinates force
the dotted conjugate center to be trivial. Its nontriviality is the independent
point-centralizer consequence in the source owner. -/
lemma terminal_paired_rank_balance_center_eq_bot [Finite G]
    (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsElementaryAbelian 2 F.Uhat]
    (hn : 1 ≤ n) (g : G) (hU : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
    (c : q.IsometryEquiv PairedFive.form)
    (hq : ∀ u v : F.U,
      q.polarBilin (Additive.ofMul (QuotientGroup.mk' (center F.U) u))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) v)) = 0 ↔ Commute u v)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hX : Nat.card (F.terminalDot (F.X g)) = 8)
    (hbalance : finrank (ZMod 2) (Symplectic.hatSpace F (F.E g)) +
      finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) = 7) :
    F.terminalDot (conjugate F.ZU g) = ⊥ := by
  let E := Symplectic.hatSpace F (F.E g)
  let Em := E.map c.toLinearEquiv.toLinearMap
  have hi := Symplectic.Ehat_totally_isotropic F hn g hU hPhi hdis q.polarBilin hq
  have hiso : ∀ v ∈ Em, ∀ w ∈ Em, PairedFive.form.polarBilin v w = 0 := by
    rintro v ⟨v, hv, rfl⟩ w ⟨w, hw, rfl⟩
    change PairedFive.form.polarBilin (c v) (c w) = 0
    have hadd : c (v + w) = c v + c w := c.toLinearEquiv.map_add v w
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← hadd, c.map_app, c.map_app, c.map_app]
    exact hi v hv w hw
  have hd : finrank (ZMod 2) E = finrank (ZMod 2) Em :=
    (E.equivMapOfInjective c.toLinearEquiv.toLinearMap c.injective).finrank_eq
  have hn' : (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)) = ⊥ := by
    apply rank_balance_forces_bot _ hX Em hiso
    rw [← hd]
    exact hbalance
  apply le_bot_iff.mp
  intro z hz
  have hm : (⟨z, F.terminalDot_conjugateCenter_le_X g hz⟩ : F.terminalDot (F.X g)) ∈
      (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)) := hz
  rw [hn'] at hm
  exact congrArg Subtype.val (mem_bot.mp hm)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
