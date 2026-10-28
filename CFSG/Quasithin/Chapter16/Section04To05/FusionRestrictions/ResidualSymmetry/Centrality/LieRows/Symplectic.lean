module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Symplectic.Rows
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Separating the symplectic centrality rows

Over a field of order 2^n, n ≥ 2, both root residuals have two-part
exponent 4n: each actual point/plane local group contains the unipotent
Sylow subgroup. The c₂ fixed group is a two-group, so its two-residual
is trivial. The individual Sylow markings make all three inner rows
central. Field and graph-field residuals have exponent 2n, except for
the field row at n = 2, whose derived binary residual is A₆ with exponent 3.
These numbers separate the central and noncentral modified residuals,
since the O³ modification preserves two-parts.

We reuse the existing `SymplecticInvolutionRows` and universal table from
`SylowSymmetry/.../Symplectic/Rows`, owned by the earlier table assembly
`qt-16-lie-symplectic-four`. Both root types and both outer actions remain
present, with actual residual equivalences and conjugating automorphisms.
The individual Sylow markings and the exact trivial-center covering clause
remain explicit earlier inputs. No residual comparison or centrality
transfer is among those inputs. Their discharge and source 16.5.6(4)
assembly remain with the source owners.

The separate PSp₄(2)′ quotient endpoint is excluded through the actual
polar equivalence with A₆, after using the covering clause to identify
the full component with its quotient. Full PSp₄(2) is never substituted
for its derived subgroup. No additional 16.4 intersection geometry is used.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 16.1.2–4,
printed pp.1170–1172, and Notation 16.5.5 and 16.5.6(4), printed p.1197.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.Symplectic
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.GraphFieldFixedResidual
open SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open BenderSuzuki.MatrixGroups

private theorem valuation_of_odd_index {X : Type*} [Group X] [Finite X]
    (H : Subgroup X) (hH : ¬ 2 ∣ H.index) :
    padicValNat 2 (Nat.card H) = padicValNat 2 (Nat.card X) := by
  rw [← H.card_mul_index, padicValNat.mul Nat.card_pos.ne' (by
    intro h; exact hH (h ▸ dvd_zero 2)), padicValNat.eq_zero_of_not_dvd hH, add_zero]

private theorem sp_valuation {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    padicValNat 2 (Nat.card (Sp F)) = 4 * n := by
  rw [← valuation_of_odd_index (unipotent (F := F))
    (two_not_dvd_index_unipotent hF hn), card_unipotent, hF, ← pow_mul,
    padicValNat.prime_pow]
  omega

private theorem local_valuation {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (P : Subgroup (Sp F)) (hP : unipotent ≤ P) :
    padicValNat 2 (Nat.card P) = 4 * n := by
  rw [valuation_of_odd_index P (fun h =>
    two_not_dvd_index_unipotent hF hn (h.trans (index_dvd_of_le hP)))]
  exact sp_valuation hn hF

private theorem derived_valuation {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    (n = 1 ∧ padicValNat 2 (Nat.card (commutator (Sp F))) = 3) ∨
    (2 ≤ n ∧ padicValNat 2 (Nat.card (commutator (Sp F))) = 4 * n) := by
  by_cases hb : n = 1
  · refine Or.inl ⟨hb, ?_⟩
    rw [Nat.card_congr (Binary.derivedEquivAlternatingSix (by simpa [hb] using hF)).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    change padicValNat 2 (2 ^ 3 * 45) = 3
    rw [padicValNat.mul (by decide) (by decide), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45), add_zero]
  · have hq : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    let := perfect_of_card_gt_two hq
    refine Or.inr ⟨by omega, ?_⟩
    rw [Group.IsPerfect.commutator_eq_top,
      Nat.card_congr (topEquiv : (⊤ : Subgroup (Sp F)) ≃* Sp F).toEquiv]
    exact sp_valuation hn hF

private theorem suzuki_valuation (m : ℕ) (hm : 0 < m) :
    padicValNat 2 (Nat.card (SuzukiMatrixGroup m)) = 2 * (2 * m + 1) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  have hc : Nat.card P = (2 ^ (2 * m + 1)) ^ 2 :=
    (congrArg (fun H : Subgroup (SuzukiMatrixGroup m) => Nat.card H) hP).trans
      (suzukiRootSubgroup_card m hm)
  calc
    padicValNat 2 (Nat.card (SuzukiMatrixGroup m)) = padicValNat 2 (Nat.card P) :=
      (valuation_of_odd_index (P : Subgroup (SuzukiMatrixGroup m)) P.not_dvd_index).symm
    _ = 2 * (2 * m + 1) := by
      rw [hc, ← pow_mul, padicValNat.prime_pow]
      omega

/-- Individual Sylow markings of the three inner types. The root predicate
retains both b₁ and a₂, through all eight actual matrix root families. -/
structure CentralityMarkings (F : Type*) [Field F] : Prop where
  root : ∀ x : Sp F, InvolutionTypes.IsRootElement x →
    IsTwoCentralIn (MulAut.innerSubgroup (Sp F)) (MulAut.conj x)
  c2 : ∀ x : Sp F, InvolutionTypes.IsC2 x →
    IsTwoCentralIn (MulAut.innerSubgroup (Sp F)) (MulAut.conj x)

/-- The earlier Sylow markings, at all nonbinary field witnesses. -/
def CentralityTable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ),
    2 ≤ n → Nat.card F = 2 ^ n → CentralityMarkings F

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Both root residuals contain the full unipotent Sylow subgroup. The c₂
residual is trivial. These are the only central rows over a nonbinary field. -/
theorem central_valuation {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (rows : SymplecticInvolutionRows F n) (a : MulAut (Sp F)) (ha2 : orderOf a = 2)
    (ha : IsTwoCentralIn (MulAut.innerSubgroup (Sp F)) a) :
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 4 * n ∨
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 0 := by
  have hi : ∃ x, a = MulAut.conj x := by
    obtain ⟨x, hx⟩ := (twoCentral_iff_odd_index.mp ha).2.1
    exact ⟨x, hx.symm⟩
  obtain ⟨_, _, _, h⟩ := rows.inner a ha2 hi
  rcases h with ⟨_, hr⟩ | ⟨_, hp⟩
  · rcases hr with hr | hr
    · obtain ⟨e⟩ := hr
      exact Or.inl ((congrArg (padicValNat 2) (Nat.card_congr e.toEquiv)).trans
        (local_valuation (by omega) hF pointLocal inf_le_left))
    · obtain ⟨e⟩ := hr
      exact Or.inl ((congrArg (padicValNat 2) (Nat.card_congr e.toEquiv)).trans
        (local_valuation (by omega) hF planeLocal inf_le_right))
  · have he : pResidual 2 a.fixedSubgroup = ⊥ :=
      bot_unique (sInf_le ⟨inferInstance, hp.to_quotient ⊥⟩)
    right
    rw [he]
    simp

/-- Field residuals have two-part exponent 2n, except for n=2 where the
actual derived half-field carrier A₆ has exponent 3. Graph-field residuals
have exponent 2n. Both bounds retain their source parameter restrictions. -/
theorem outer_valuation {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (rows : SymplecticInvolutionRows F n) (a : MulAut (Sp F)) (ha2 : orderOf a = 2)
    (ha : ¬ ∃ x, a = MulAut.conj x) :
    (n = 2 ∧ padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 3) ∨
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 2 * n := by
  rcases rows.outer a ha2 ha with ⟨m, hm, he, c, hc⟩ | ⟨m, he, c, hc, ⟨efix⟩⟩
  · have hF' : Nat.card F = 2 ^ (2 * m) := he ▸ hF
    have hK := FieldFixedResidual.card_halfField hm hF'
    let s := (MulAut.fixedResidualEquivOfCompatible 2 c a
      (FieldFixedResidual.representative m) hc).trans
        (FieldFixedResidual.residualEquiv ((frobeniusEquiv F 2) ^ m))
    rw [Nat.card_congr s.toEquiv]
    rcases derived_valuation hm hK with ⟨hb, hv⟩ | ⟨_, hv⟩
    · exact Or.inl ⟨by omega, hv⟩
    · right
      simpa only [he, show 2 * (2 * m) = 4 * m by omega] using hv
  · have hm : 0 < m := by omega
    let es : commutator (SuzukiMatrixGroup m) ≃* SuzukiMatrixGroup m :=
      (MulEquiv.subgroupCongr (suzuki_commutator_eq_top m hm)).trans topEquiv
    let s := ((MulAut.fixedResidualEquivOfCompatible 2 c a
      (graphFieldAut m) hc).trans (residualEquivOfSuzuki m hm efix)).trans es
    right
    rw [Nat.card_congr s.toEquiv, suzuki_valuation m hm, he]

/-- The individual inner markings force a noncentral actor into an outer row. -/
theorem noncentral_valuation {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (rows : SymplecticInvolutionRows F n) (marks : CentralityMarkings F)
    (a : MulAut (Sp F)) (ha2 : orderOf a = 2)
    (ha : ¬ IsTwoCentralIn (MulAut.innerSubgroup (Sp F)) a) :
    (n = 2 ∧ padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 3) ∨
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 2 * n := by
  apply outer_valuation hn hF rows a ha2
  intro hi
  obtain ⟨x, _, hx, h⟩ := rows.inner a ha2 hi
  apply ha
  rw [hx]
  rcases h with ⟨hr, _⟩ | ⟨hc, _⟩
  · exact marks.root x hr
  · exact marks.c2 x hc

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- Central and noncentral actors have distinct modified residuals in a
specified full symplectic model; O³ preserves the separating two-part. -/
theorem separation_of_model {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (rows : SymplecticInvolutionRows F n) (marks : CentralityMarkings F)
    (e : L ≃* Sp F) (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let a := fullModelAction e (actionMap le_rfl u)
  let b := fullModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hu2
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hv2
  have ha := central_valuation hn hF rows a ha2
    ((fullModelAction_twoCentral_iff e _).mpr hu)
  have hb := noncentral_valuation hn hF rows marks b hb2
    (fun h => hv ((fullModelAction_twoCentral_iff e _).mp h))
  rintro ⟨d⟩
  have he := fixedResidual_twoValuation_eq e u v d
  change padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) =
    padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup)) at he
  omega

/-- The source quotient formulation, conditional on the exact trivial-center
clause of 16.1.2 for this surviving family and the earlier marked table. -/
theorem separation (rows : SymplecticInvolutionTable) (marks : CentralityTable)
    (hZ : center L = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ n))
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  obtain ⟨F, hfield, hfin, hcard, ⟨c⟩⟩ := hmodel
  let := EvenProjective.charTwo_of_card hcard
  let e : L ≃* Sp F :=
    ((QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans c).trans EvenProjective.equiv.symm
  exact separation_of_model hn hcard (rows F n hn hcard) (marks F n hn hcard)
    e u v hu2 hv2 hu hv

omit [Finite G] in
/-- The derived binary endpoint is excluded only after constructing the
actual A₆ equivalence of the full component, using the covering clause. -/
theorem binary_derived_excluded (hZ : center L = ⊥)
    (ha6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    (e : (L ⧸ center L) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False := by
  apply ha6
  exact ⟨((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e).trans
      Binary.projectiveDerivedEquivAlternatingSix⟩

/-- Both symplectic alternatives of the surviving catalogue, including the
separate quotient-first derived binary carrier. -/
theorem separation_of_surviving_models
    (rows : SymplecticInvolutionTable) (marks : CentralityTable)
    (hZ : center L = ⊥) (ha6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    (hmodel : (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ n)) ∨
      Nonempty ((L ⧸ center L) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  rcases hmodel with ⟨n, hn, hmodel⟩ | he
  · exact separation rows marks hZ hn hmodel u v hu2 hv2 hu hv
  · obtain ⟨e⟩ := he
    exact (binary_derived_excluded hZ ha6 e).elim

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.Symplectic
