module
public import CFSG.Quasithin.Chapter12.Section08.Terminal.OrthogonalModels
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Marking

/-!
# The paired Borel in the terminal faithful quotient

The point-stabilizer criterion of `terminal_paired_stabilizer` identifies the
stabilizer inside the actual paired component with A₄ × A₄. For the full
faithful group, an equivariant quadratic marking into the swapped permutation
model transports the literal stabilizer and its two-residual. The nonzero
fixed vector is calculated from the standard elementary eight-subgroup inside
the actual Sylow; no fixed-line or Borel conclusion is an input.

The final adapter constructs the full action marking and elementary Sylow
placement from the original geometric action, the marked paired component,
and the source splitting clause for X. It proves that the two-residual is
exactly the intersection with that component, identifies both with A₄ × A₄,
and gives three-rank two for the residual and a lower bound for the stabilizer.

The earlier quadratic/action and source subgroup inputs remain explicit.
Two-perfectness and three-rank of A₄ × A₄ remain separate numerical group
inputs. The terminal model owner must
discharge these inputs, and the terminal source owner retains the center
nontriviality and final exclusion in 12.8.13(7).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.11.2(12),
printed p.364, and 12.8.13(7), printed pp.855–856.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

lemma terminal_paired_borel_model (F : InvariantFlag T V n)
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
    Nonempty (((F.terminalPointStabilizer u).subgroupOf L) ≃*
      (PairedBorel.A4 × PairedBorel.A4)) := by
  have hcriterion := F.terminal_paired_stabilizer q c L e heq x hswap Q ha hb hx u hu hfixed
  let S := (F.terminalPointStabilizer u).subgroupOf L
  let f : S →* PairedBorel.pairedBorel := {
    toFun := fun h => ⟨e h.val, (hcriterion h.val).mp h.property⟩
    map_one' := Subtype.ext e.map_one
    map_mul' := fun a b => Subtype.ext (e.map_mul a.val b.val) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro a
      have hmem : e.symm a.val ∈ S := by
        apply (hcriterion _).mpr
        rw [e.apply_symm_apply]
        exact a.property
      exact ⟨⟨e.symm a.val, hmem⟩, Subtype.ext (e.apply_symm_apply a.val)⟩
  exact ⟨(MulEquiv.ofBijective f hf).trans PairedBorel.borelEquiv⟩

section FullMarking
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
  (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
  (c : q.IsometryEquiv PairedFive.form)
  (H : Subgroup PairedBorel.Model) (e : F.TerminalHdot ≃* H)
  (heq : ∀ (h : F.TerminalHdot) (u : F.Uhat),
    c (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
      PairedBorel.modelAction (e h).val (c (Additive.ofMul u)))
  (Q : Sylow 2 F.TerminalHdot)
  (hX : PairedBorel.elementary ≤
    (Q : Subgroup F.TerminalHdot).map (H.subtype.comp e.toMonoidHom))
  (u : F.Uhat) (hu : u ≠ 1)
  (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u)

include heq hX hu hfixed in
lemma terminal_paired_point_of_elementary :
    c (Additive.ofMul u) = PairedFive.point := by
  apply PairedBorel.elementary_fixed_point
  · intro hz
    exact hu (c.injective (hz.trans c.map_zero.symm))
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := hX hg
    change PairedBorel.modelAction (e h).val (c (Additive.ofMul u)) = _
    rw [← heq, hfixed h hh]

noncomputable def terminalPairedStabilizerEquiv
    (hp : c (Additive.ofMul u) = PairedFive.point) :
    F.terminalPointStabilizer u ≃* PairedBorel.stabilizerIn H where
  toFun s := ⟨e s.val, by
    change PairedBorel.modelAction (e s.val).val PairedFive.point = PairedFive.point
    rw [← hp, ← heq, (F.mem_terminalPointStabilizer u s.val).mp s.property]⟩
  invFun s := ⟨e.symm s.val, by
    apply (F.mem_terminalPointStabilizer u _).mpr
    apply c.injective
    change c (Additive.ofMul (F.terminalFaithfulHatAction (e.symm s.val) u)) =
      c (Additive.ofMul u)
    rw [heq, e.apply_symm_apply, hp]
    exact s.property⟩
  left_inv s := Subtype.ext (e.symm_apply_apply s.val)
  right_inv s := Subtype.ext (e.apply_symm_apply s.val)
  map_mul' s t := Subtype.ext (e.map_mul s.val t.val)

include heq hX hu hfixed in
lemma terminal_paired_residual_model
    (hH : PairedBorel.pairedInclusion.range ≤ H)
    (hperfect : pResidual 2 (PairedBorel.A4 × PairedBorel.A4) = ⊤)
    (hrank : primeRank 3 (PairedBorel.A4 × PairedBorel.A4) = 2) :
    (((pResidual 2 (F.terminalPointStabilizer u)).map
        (F.terminalPointStabilizer u).subtype).map
      (H.subtype.comp e.toMonoidHom) = PairedBorel.embeddedBorel) ∧
    Nonempty ((pResidual 2 (F.terminalPointStabilizer u)) ≃*
      (PairedBorel.A4 × PairedBorel.A4)) ∧
    primeRank 3 (pResidual 2 (F.terminalPointStabilizer u)) = 2 ∧
    2 ≤ primeRank 3 (F.terminalPointStabilizer u) := by
  have hp := F.terminal_paired_point_of_elementary q c H e heq Q hX u hu hfixed
  let d := F.terminalPairedStabilizerEquiv q c H e heq u hp
  have hd : (pResidual 2 (F.terminalPointStabilizer u)).map d.toMonoidHom =
      pResidual 2 (PairedBorel.stabilizerIn H) := map_pResidual 2 d
  let r := ((d.subgroupMap (pResidual 2 (F.terminalPointStabilizer u))).trans
    (MulEquiv.subgroupCongr hd)).trans (PairedBorel.residualEquiv H hH hperfect)
  have hfinite : Finite F.TerminalHdot := Finite.of_equiv H e.symm.toEquiv
  refine ⟨?_, ⟨r⟩, ?_, ?_⟩
  · have hm := congrArg (Subgroup.map (PairedBorel.stabilizerMap H)) hd
    rw [PairedBorel.residual_map_stabilizer H hH hperfect] at hm
    rw [map_map] at hm ⊢
    exact hm
  · exact (Theory.GroupTheory.primeRank_equiv 3 r).trans hrank
  · exact (PairedBorel.stabilizer_threeRank_ge H hH hrank).trans_eq
      (Theory.GroupTheory.primeRank_equiv 3 d).symm
end FullMarking

section GeometricMarking

variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]

/-- The original faithful dotted action in the given linear coordinates. -/
noncomputable def terminalPairedLinearAction
    (c : Additive F.Uhat ≃ₗ[ZMod 2] PairedFive.Space) :
    F.TerminalHdot →* (PairedFive.Space ≃ₗ[ZMod 2] PairedFive.Space) where
  toFun h := c.symm.trans
    (({ (F.terminalFaithfulHatAction h).toAdditive with
      map_smul' := ZMod.map_smul (F.terminalFaithfulHatAction h).toAdditive } :
        Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat).trans c)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change c (Additive.ofMul (F.terminalFaithfulHatAction 1 (c.symm v).toMul)) = v
    simp
  map_mul' h k := by
    apply LinearEquiv.ext
    intro v
    change c (Additive.ofMul (F.terminalFaithfulHatAction (h * k) (c.symm v).toMul)) =
      c (Additive.ofMul (F.terminalFaithfulHatAction h
        (c.symm (c (Additive.ofMul (F.terminalFaithfulHatAction k (c.symm v).toMul)))).toMul))
    simp

/-- The coordinate action is literally the faithful action on U/Z(U). -/
lemma terminalPairedLinearAction_apply
    (c : Additive F.Uhat ≃ₗ[ZMod 2] PairedFive.Space)
    (h : F.TerminalHdot) (u : F.Uhat) :
    F.terminalPairedLinearAction c h (c (Additive.ofMul u)) =
      c (Additive.ofMul (F.terminalFaithfulHatAction h u)) := by
  change c (Additive.ofMul (F.terminalFaithfulHatAction h (c.symm (c (Additive.ofMul u))).toMul)) = _
  rw [c.symm_apply_apply]
  rfl

/-- Changing vector coordinates preserves faithfulness of the dotted action. -/
lemma terminalPairedLinearAction_injective
    (c : Additive F.Uhat ≃ₗ[ZMod 2] PairedFive.Space) :
    Function.Injective (F.terminalPairedLinearAction c) := by
  intro h k he
  apply F.terminalFaithfulHatAction_injective
  ext u
  apply c.injective
  exact (F.terminalPairedLinearAction_apply c h u).symm.trans
    ((LinearEquiv.congr_fun he (c (Additive.ofMul u))).trans
      (F.terminalPairedLinearAction_apply c k u))

variable (q : QuadraticForm (ZMod 2) (Additive F.Uhat))
  (c : q.IsometryEquiv PairedFive.form)
  (hq : ∀ (h : F.TerminalHdot) (u : F.Uhat),
    q (Additive.ofMul (F.terminalFaithfulHatAction h u)) = q (Additive.ofMul u))
  (hs : ∀ h, PairedBorel.PreservesSummandPair (F.terminalPairedLinearAction c.toLinearEquiv h))
  (L : Subgroup F.TerminalHdot) (eL : L ≃* PairedFive.Actor)
  (heL : ∀ (l : L) (u : F.Uhat),
    c (Additive.ofMul (F.terminalFaithfulHatAction l u)) =
      PairedFive.action (eL l) (c (Additive.ofMul u)))
  (X : Subgroup F.TerminalHdot) [IsElementaryAbelian 2 X]
  (hcard : Nat.card X = 8) (x : F.TerminalHdot) (hx : x ∈ X)
  (hswap : ∀ v : PairedFive.Factor,
    (F.terminalPairedLinearAction c.toLinearEquiv x (v, 0)).1 = 0)
  (hsplit : X ≤ L ⊔ Subgroup.zpowers x)
  (Q : Sylow 2 F.TerminalHdot) (hXQ : X ≤ Q)

include hq hs heL hcard hx hswap hsplit hXQ in
/-- Construct compatible model coordinates from the geometric action and the
source elementary subgroup, retaining the exact factor, swap and Sylow images. -/
lemma terminal_paired_marking :
    ∃ (c' : q.IsometryEquiv PairedFive.form) (r : F.TerminalHdot →* PairedBorel.Model),
      Function.Injective r ∧
      (∀ (h : F.TerminalHdot) (u : F.Uhat),
        c' (Additive.ofMul (F.terminalFaithfulHatAction h u)) =
          PairedBorel.modelAction (r h) (c' (Additive.ofMul u))) ∧
      L.map r = PairedBorel.pairedInclusion.range ∧
      X.map r = PairedBorel.elementary ∧ r x = PairedBorel.interchange ∧
      PairedBorel.elementary ≤ (Q : Subgroup F.TerminalHdot).map r := by
  let φ := F.terminalPairedLinearAction c.toLinearEquiv
  have hform : ∀ h v, PairedFive.form (φ h v) = PairedFive.form v := by
    intro h v
    obtain ⟨u, rfl⟩ := c.surjective v
    exact (congrArg PairedFive.form
      (F.terminalPairedLinearAction_apply c.toLinearEquiv h u.toMul)).trans
      ((c.map_app _).trans ((hq h u.toMul).trans (c.map_app u).symm))
  have hact : ∀ (l : L) v, φ l v = PairedFive.action (eL l) v := by
    intro l v
    obtain ⟨u, rfl⟩ := c.surjective v
    exact (F.terminalPairedLinearAction_apply c.toLinearEquiv l u.toMul).trans (heL l u.toMul)
  obtain ⟨t, r, hr, heq, hL, hX, hx', hQ⟩ := PairedBorel.exists_standard_marking
    φ (F.terminalPairedLinearAction_injective c.toLinearEquiv) hform hs L eL hact
    X hcard x hx hswap hsplit Q hXQ
  refine ⟨c.trans (PairedBorel.modelIsometry (PairedBorel.base t)), r,
    hr, ?_, hL, hX, hx', hQ⟩
  intro h u
  change PairedBorel.modelAction (PairedBorel.base t)
    (c (Additive.ofMul (F.terminalFaithfulHatAction h u))) =
      PairedBorel.modelAction (r h) (PairedBorel.modelAction (PairedBorel.base t)
        (c (Additive.ofMul u)))
  rw [heq]
  exact congrArg (PairedBorel.modelAction (PairedBorel.base t))
    (F.terminalPairedLinearAction_apply c.toLinearEquiv h u).symm

include hq hs heL hcard hx hswap hsplit hXQ in
/-- The paired Borel calculation in 12.8.13(7), on the literal faithful quotient.
The two-residual is the point stabilizer inside the actual paired component,
and both are A₄ × A₄. The input is the geometric action and source splitting
clause, with no full-group model, standard-generator placement or fixed-line
premise. The two numerical A₄-product inputs are discharged by the terminal
model assembly; the earlier geometric and source subgroup inputs remain there. -/
lemma terminal_paired_residual_of_source
    (u : F.Uhat) (hu : u ≠ 1)
    (hfixed : ∀ h ∈ (Q : Subgroup F.TerminalHdot), F.terminalFaithfulHatAction h u = u)
    (hperfect : pResidual 2 (PairedBorel.A4 × PairedBorel.A4) = ⊤)
    (hrank : primeRank 3 (PairedBorel.A4 × PairedBorel.A4) = 2) :
    (pResidual 2 (F.terminalPointStabilizer u)).map (F.terminalPointStabilizer u).subtype =
        F.terminalPointStabilizer u ⊓ L ∧
      Nonempty (((F.terminalPointStabilizer u).subgroupOf L) ≃*
        (PairedBorel.A4 × PairedBorel.A4)) ∧
      Nonempty ((pResidual 2 (F.terminalPointStabilizer u)) ≃*
        (PairedBorel.A4 × PairedBorel.A4)) ∧
      primeRank 3 (pResidual 2 (F.terminalPointStabilizer u)) = 2 ∧
      2 ≤ primeRank 3 (F.terminalPointStabilizer u) := by
  obtain ⟨c', r, hr, heq, hL, hX, hx', hQ⟩ :=
    F.terminal_paired_marking q c hq hs L eL heL X hcard x hx hswap hsplit Q hXQ
  let H : Subgroup PairedBorel.Model := r.range
  let e : F.TerminalHdot ≃* H := MonoidHom.ofInjective hr
  have he (h : F.TerminalHdot) (v : F.Uhat) :
      c' (Additive.ofMul (F.terminalFaithfulHatAction h v)) =
        PairedBorel.modelAction (e h).val (c' (Additive.ofMul v)) := heq h v
  have hH : PairedBorel.pairedInclusion.range ≤ H := by
    rw [← hL]
    exact Subgroup.map_le_range r L
  have hQ' : PairedBorel.elementary ≤
      (Q : Subgroup F.TerminalHdot).map (H.subtype.comp e.toMonoidHom) := hQ
  obtain ⟨hres, hiso, hrank', hge⟩ :=
    F.terminal_paired_residual_model q c' H e he Q hQ' u hu hfixed hH hperfect hrank
  have hp := F.terminal_paired_point_of_elementary q c' H e he Q hQ' u hu hfixed
  have hS : (F.terminalPointStabilizer u).map r = PairedBorel.pointStabilizer ⊓ H := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨?_, ⟨h, rfl⟩⟩
      change PairedBorel.modelAction (r h) PairedFive.point = PairedFive.point
      rw [← hp, ← heq, (F.mem_terminalPointStabilizer u h).mp hh]
    · rintro ⟨hg, h, rfl⟩
      refine ⟨h, ?_, rfl⟩
      apply (F.mem_terminalPointStabilizer u h).mpr
      apply c'.injective
      change c' (Additive.ofMul (F.terminalFaithfulHatAction h u)) = c' (Additive.ofMul u)
      rw [heq, hp]
      exact hg
  have hB : (F.terminalPointStabilizer u ⊓ L).map r = PairedBorel.embeddedBorel := by
    rw [Subgroup.map_inf _ _ r hr, hS, hL, PairedBorel.embeddedBorel_eq,
      inf_assoc, inf_eq_right.mpr hH]
  have heqres : (pResidual 2 (F.terminalPointStabilizer u)).map
      (F.terminalPointStabilizer u).subtype = F.terminalPointStabilizer u ⊓ L := by
    apply Subgroup.map_injective hr
    exact hres.trans hB.symm
  let η := PairedBorel.pairedSubgroupEquiv L r hr hL
  have hη (l : L) (v : F.Uhat) :
      c' (Additive.ofMul (F.terminalFaithfulHatAction l v)) =
        PairedFive.action (η l) (c' (Additive.ofMul v)) := by
    rw [heq, ← PairedBorel.pairedSubgroupEquiv_apply L r hr hL l,
      PairedBorel.modelAction_paired]
  have hxswap (v : F.Uhat) :
      c' (Additive.ofMul (F.terminalFaithfulHatAction x v)) =
        PairedFive.swap (c' (Additive.ofMul v)) := by
    rw [heq, hx', PairedBorel.modelAction_interchange]
  have ha := PairedBorel.pairedSubgroupEquiv_symm_mem L r hr hL
    (Q : Subgroup F.TerminalHdot) _ (hQ PairedBorel.elementary_first)
  have hb := PairedBorel.pairedSubgroupEquiv_symm_mem L r hr hL
    (Q : Subgroup F.TerminalHdot) _ (hQ PairedBorel.elementary_second)
  have hborel := F.terminal_paired_borel_model q c' L η hη x hxswap Q ha hb (hXQ hx)
    u hu hfixed
  exact ⟨heqres, hborel, hiso, hrank', hge⟩

end GeometricMarking

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
