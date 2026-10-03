module

public import Stellmacher.Recognition.Parrott.SylowSeedOuterCentralization
public import Theory.SpecificGroups.Tits.RecognitionSylowFixedPoints
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# The commutator bound preceding Parrott's equation (18)

The outer-conjugate discrepancy q = x⁻¹bx(ba)⁻¹ belongs to the actual
self-centralizing elementary derived subgroup E. Since x fixes a and x²
centralizes b, conjugation by x inverts q. Its elementary membership makes
q an involution or the identity, hence fixed by x and contained in ⟨z,t⟩.
Both central coordinates commute with b, so [b,x]/a = q.

This uses the supplied seed's b throughout. No equality with the normalizer
fusion package's b, equation (17), or downstream completion is required.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, p.680, paragraph preceding equation (18).
-/

open Subgroup
set_option linter.unusedSimpArgs false
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] [Finite G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}
/-- The error in [b,x] belongs to the central four-group. Equation (17) and
compatibility with the initially chosen three-subgroup are not needed. -/
public theorem bx_div_a_mem (f : ParrottSylowSeedData n false) (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z)) :
    Tits.parrottCommutator f.b f.x / f.a ∈ closure ({z,n.t} : Set G) := by
  let q := f.x⁻¹*f.b*f.x*(f.b*f.a)⁻¹
  have hq : q ∈ closure ({z,n.t,n.v,f.u,f.w} : Set G) :=
    (f.outer_discrepancies_mem_derived h).1
  have hq2 : q^2=1 := by
    rw [f.derived_basis] at hq
    obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let : IsElementaryAbelian 2 D := hElem
    obtain ⟨d, hd, hdq⟩ := hq
    have hd2 : d^2=1 := elemPow_eq_one_of_isElementaryAbelian (A := D) d hd
    rw [← hdq]
    exact (map_pow (H.subtype.comp J.subtype) d 2).symm.trans
      ((congrArg (H.subtype.comp J.subtype) hd2).trans (map_one _))
  have hai : f.a⁻¹=f.a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.relations.a_sq)
  have hqi : q⁻¹=q := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hq2)
  let P : G ≃* G := MulAut.conj f.x⁻¹
  have Peq (s : G) : P s = f.x⁻¹*s*f.x := by simp [P]
  have Pa : P f.a = f.a := by
    rw [Peq]
    have hc := (Tits.parrottCommutator_eq_one_iff _ _).mp hax
    rw [mul_assoc, hc.eq, inv_mul_cancel_left]
  have P2b : P (P f.b) = f.b := by
    have hbxx : Commute f.b (f.x^2) := by
      have hz := f.relations.comm_zb.symm
      have hh := hby.mul_right hz.inv_right
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
    rw [Peq, Peq]
    calc
      _ = (f.x^2)⁻¹*f.b*(f.x^2) := by simp only [pow_two, mul_inv_rev]; group
      _ = f.b := by rw [mul_assoc, hbxx.eq, inv_mul_cancel_left]
  have hqP : P q = q := by
    calc
      P q = P (P f.b * (f.b*f.a)⁻¹) := by rw [Peq f.b]
      _ = f.b * (P f.b * f.a)⁻¹ := by rw [map_mul, map_inv, map_mul, P2b, Pa]
      _ = q⁻¹ := by dsimp only [q]; rw [Peq, mul_inv_rev, hai]; group
      _ = q := hqi
  have hfix : f.x⁻¹*q*f.x=q := by simpa only [Peq] using hqP
  have hqt : q ∈ closure ({z,n.t} : Set G) :=
    Tits.ParrottSylowSeedRelations.fixed_mem_pair f.relations
      (by intro ht; simpa [ht] using n.t_order) hq hfix
  have hqb : Commute q f.b := by
    have hl : closure ({z,n.t} : Set G) ≤ centralizer ({f.b} : Set G) := by
      apply (closure_le _).mpr
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      exact mem_centralizer_singleton_iff.mpr f.relations.comm_zb
      exact mem_centralizer_singleton_iff.mpr f.relations.comm_bt.symm
    exact mem_centralizer_singleton_iff.mp (hl hqt)
  have he : Tits.parrottCommutator f.b f.x / f.a = q := by
    calc
      _ = f.b⁻¹*q*f.b := by dsimp only [q]; rw [Tits.parrottCommutator, div_eq_mul_inv]; group
      _ = q := by rw [mul_assoc, hqb.eq, inv_mul_cancel_left]
  exact he ▸ hqt
/-- The four possibilities for [b,x] preceding equation (18). -/
public theorem bx_cases (f : ParrottSylowSeedData n false)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z)) :
    Tits.parrottCommutator f.b f.x = f.a ∨
      Tits.parrottCommutator f.b f.x = f.a*n.t ∨
      Tits.parrottCommutator f.b f.x = f.a*z ∨
      Tits.parrottCommutator f.b f.x = f.a*n.t*z := by
  have hm := f.bx_div_a_mem h hax hby
  have hz : z*z=1 := by simpa only [pow_two] using f.relations.z_sq
  have ht : n.t*n.t=1 := by simpa only [pow_two] using f.relations.t_sq
  rcases (mem_closure_pair_iff z n.t hz ht f.relations.comm_zt _).mp hm with
    he | he | he | he
  · exact Or.inl (by simpa only [one_mul] using (div_eq_iff_eq_mul).mp he)
  · exact Or.inr (Or.inr (Or.inl (by
      simpa only [f.relations.comm_az.symm.eq] using (div_eq_iff_eq_mul).mp he)))
  · exact Or.inr (Or.inl (by
      simpa only [f.relations.comm_at.symm.eq] using (div_eq_iff_eq_mul).mp he))
  · right; right; right
    calc
      _ = (z*n.t)*f.a := (div_eq_iff_eq_mul).mp he
      _ = f.a*n.t*z := by
        rw [mul_assoc, f.relations.comm_at.symm.eq, ← mul_assoc,
          f.relations.comm_az.symm.eq, mul_assoc, f.relations.comm_zt.eq, ← mul_assoc]

end Stellmacher.Recognition.ParrottSylowSeedData
