module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Basic

/-!
# Small commutators on dual-line preimages in the actual midpoint span

Every nonzero dual quotient vector is the image of an element in a genuine
local conjugate of Z_c. The quotient kernel is the original Z_alpha, which
centralizes Q_alpha. Thus the full preimage of each binary line has its
Q_alpha commutator contained in a conjugate of [Z_c,Q_alpha], of order at
most four. All lifts use the given natural marking and source projection.

This supplies the small-commutator input suggested by the rank-one pairing
argument (1.7). It does not prove the distinct parabolic displacement bound
on core/U_alpha or eliminate the fixed kernel.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7), pp.847--848, and the
midpoint span in (4.6.12), pp.910--912. The order-four input comes from the
already proved common binary reduction and radius geometry.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.SpanPairing

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) {geometry : Geometry R}
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (q : SpanQuotient source common s.middle)

/-- The actual binary-line preimage, retaining Z_alpha as its kernel. -/
noncomputable def linePreimage (x : orbitSpan s.middle) : Subgroup (FreeAmalgam R) :=
  ((zpowers (q.quotient x)).comap q.quotient).map (orbitSpan s.middle).subtype

theorem linePreimage_eq (x : orbitSpan s.middle) :
    linePreimage source common s q x = Z R (alpha R) ⊔ zpowers (x : FreeAmalgam R) := by
  unfold linePreimage
  rw [← MonoidHom.map_zpowers q.quotient, comap_map_eq, q.kernel,
    Subgroup.map_sup, MonoidHom.map_zpowers,
    map_subgroupOf_eq_of_le (Z_le_orbitSpan_of_distance_two s.middle s.first_distance)]
  exact sup_comm _ _

include radius hb in
/-- A nonzero quotient vector can be lifted from a genuine conjugate of Z_c.
No lift modulo U_alpha is asserted. -/
theorem exists_conjugate_lift (x : orbitSpan s.middle) (hx : q.quotient x ≠ 1) :
    ∃ (m : M) (y : orbitSpan s.middle), q.quotient y = q.quotient x ∧
      (y : FreeAmalgam R) ∈
        (Z R s.middle).map (MulAut.conj (embedM R m)).toMonoidHom := by
  have hnot : ¬ Z R s.middle ≤ Z R (alpha R) := by
    intro h
    apply (midpoint_nu common radius hb s).2
    exact h.trans (Flags.Z_le_B geometry (alpha R)
      (geometry.V_local (alpha R) rfl common.large_distance))
  obtain ⟨z, hz, hzn⟩ := SetLike.not_le_iff_exists.mp hnot
  let z₀ : orbitSpan s.middle := ⟨z, Z_le_orbitSpan s.middle hz⟩
  have hzq : (q.quotient z₀).toAdd ≠ 0 := by
    intro he
    have hk : z₀ ∈ q.quotient.ker := Multiplicative.toAdd.injective he
    rw [q.kernel] at hk
    exact hzn hk
  have hxq : (q.quotient x).toAdd ≠ 0 := by
    intro he
    exact hx (Multiplicative.toAdd.injective he)
  obtain ⟨g, hg⟩ := Linear.dual_orbit hzq hxq
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmark : common.natural.marking (source.projection m) = g := by simp [hm]
  have hlocal : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  let y : orbitSpan s.middle := ⟨embedM R m * z * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (orbitSpan_normalized s.middle hlocal) z).mp z₀.property⟩
  refine ⟨m, y, ?_, ⟨z, hz, rfl⟩⟩
  apply Multiplicative.toAdd.injective
  rw [q.action m z₀ y rfl, hmark]
  exact hg

include radius hb in
/-- The full Z-kernel line seed has the genuine order-four Q_alpha
commutator bound needed in (1.7). This does not bound a parabolic actor's
fixed codimension on core/U_alpha. -/
theorem linePreimage_commutator_card (x : orbitSpan s.middle)
    (hx : q.quotient x ≠ 1) :
    Nat.card (⁅linePreimage source common s q x, Q R (alpha R)⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  obtain ⟨m, y, hyq, hy⟩ := exists_conjugate_lift source common radius hb s q x hx
  have hline : linePreimage source common s q x = linePreimage source common s q y := by
    unfold linePreimage
    rw [hyq]
  rw [hline, linePreimage_eq]
  let f := (MulAut.conj (embedM R m)).toMonoidHom
  let A := (Z R s.middle).map f
  have hlocal : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  have hQmap : (Q R (alpha R)).map f = Q R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R (alpha R) hlocal)
  have hZQ : Z R s.middle ≤ Q R (alpha R) :=
    (Z_le_orbitSpan s.middle).trans
      ((orbitSpan_le_radius s.middle ((cosetGraph R).dist_comm.trans s.first_distance).le).trans
        (geometry.V_le_Q common.large_distance (alpha R) rfl))
  have hAQ : A ≤ Q R (alpha R) := (map_mono hZQ).trans_eq hQmap
  have hcomm : ⁅Z R (alpha R) ⊔ A, Q R (alpha R)⁆ = ⁅A, Q R (alpha R)⁆ := by
    rw [commutator_comm (Z R (alpha R) ⊔ A), commutator_comm A]
    exact (commutator_eq_of_centralizing_sup rfl
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes (alpha R) rfl))
      (hAQ.trans (Q R (alpha R)).le_normalizer)).symm
  have hle : ⁅Z R (alpha R) ⊔ zpowers (y : FreeAmalgam R), Q R (alpha R)⁆ ≤
      (⁅Z R s.middle, Q R (alpha R)⁆).map f := by
    rw [map_commutator, hQmap]
    rw [← hcomm]
    exact commutator_mono (sup_le_sup_left (zpowers_le.mpr hy) _) le_rfl
  have hKQ : ⁅Z R s.middle, Q R (alpha R)⁆ ≤ Q R (alpha R) :=
    (commutator_mono hZQ le_rfl).trans (commutator_le_self _)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (⁅Z R s.middle, Q R (alpha R)⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (hKQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  let : Finite ((⁅Z R s.middle, Q R (alpha R)⁆ : Subgroup (FreeAmalgam R)).map f) :=
    Finite.of_surjective _ (f.subgroupMap_surjective _)
  have hf : Function.Injective f := (MulAut.conj (embedM R m)).injective
  have hc := card_le_of_le hle
  rw [card_map_of_injective hf] at hc
  obtain ⟨modules⟩ := source.moduleFacts geometry common.large_distance
  exact hc.trans (Escape.PairingControl.moving_commutator_card_le_four source
    common.large_distance modules rfl (by
      have hn := midpoint_nu common radius hb s
      exact ⟨s.first_distance, hn.2⟩))


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.SpanPairing
