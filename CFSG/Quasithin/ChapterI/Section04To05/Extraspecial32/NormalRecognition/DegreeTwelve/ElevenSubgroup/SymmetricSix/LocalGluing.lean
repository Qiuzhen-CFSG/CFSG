module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.CubicModules
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.FixedLineCompatibility

/-!
# Gluing the two cubic four-groups

Choose the nonidentity vector b fixed by u in `[A(z),X]`. The conjugate-core
calculation places b*u*z in the fixed line in `[A(u),X₁]`, so v=b*u is a common
middle reflection. The cubic norm calculation proves both mixed braids, and
the two orbit spans prove the literal five-reflection generation equality.
Both choices of the source involution are covered.

The final theorem constructs the gluing data from the local hypotheses,
relative quaternion normality, fusion-eight data, source geometry and the
commuting cubic. It discharges the elementary module and fixed-vector
premises of the intermediate assemblies using `CubicModules` and
`FixedLineCompatibility`.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.6, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing

open Subgroup
variable {G : Type*} [Group G]

private theorem generator_of_card_three (X : Subgroup G) (hX : Nat.card X = 3) :
    ∃ x : G, zpowers x = X := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact X.isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card hX)

variable [Finite G] {z : G} {h : Hypotheses z} {a : SourceGeometry h}

/-- The centralizing clause of the second fixed line is automatic. Only
membership in the second moved four requires the conjugate-core argument. -/
public theorem other_vector_mem_fixedLine_iff (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) {b : G}
    (hb : b ∈ fixedLine z c.u (cubicInG h)) :
    b * c.u * z ∈ fixedLine c.u z c.X1 ↔ b * c.u * z ∈ movedFour c.u c.X1 := by
  constructor
  · exact fun ht => ht.1
  · intro ht
    refine ⟨ht, mem_centralizer_singleton_iff.mpr ?_⟩
    exact ((p.commutes_base hb.1).mul_left c.u_commutes_z).mul_left (Commute.refl z)

/-- A nonidentity vector of the first fixed line gives a nonidentity candidate
for the second line, for either allowed choice of the source involution. -/
public theorem other_vector_ne_one (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) {b : G}
    (hb : b ∈ fixedLine z c.u (cubicInG h)) : b * c.u * z ≠ 1 := by
  intro he
  have hu : c.u = b⁻¹ * z⁻¹ := by
    calc
      c.u = b⁻¹ * (b * c.u * z) * z⁻¹ := by group
      _ = b⁻¹ * z⁻¹ := by rw [he, mul_one]
  apply selected_involution_not_core c
  rw [hu]
  exact (coreInG z).mul_mem ((coreInG z).inv_mem (fusionCore_le z (p.moved_le hb.1)))
    ((coreInG z).inv_mem h.involution_mem_coreInG)

omit [Finite G] in
private theorem rotate_cube {s t : G} (he : (s * t) ^ 3 = 1) : (t * s) ^ 3 = 1 := by
  have hc := congrArg (MulAut.conj s⁻¹) he
  simpa only [map_pow, MulAut.conj_apply, inv_mul_cancel_left, inv_inv, one_mul,
    inv_mul_cancel, mul_one] using hc

/-- The two elementary cubic modules give the literal five-generator equality
as soon as their fixed vectors give the same middle reflection. -/
public theorem generated_of_fixed_vectors (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) (p1 : CubicFourData c.u z c.X1)
    {x x1 b : G} (hx : zpowers x = cubicInG h) (hx1 : zpowers x1 = c.X1)
    (hb : b ∈ fixedLine z c.u (cubicInG h)) (hbne : b ≠ 1)
    (hb1 : b * c.u * z ∈ fixedLine c.u z c.X1) :
    closure (Set.range (sourceChain z c.u x x1 (b * c.u))) =
      fusionCore z ⊔ fusionCore c.u ⊔ cubicInG h ⊔ c.X1 := by
  let H := closure (Set.range (sourceChain z c.u x x1 (b * c.u)))
  have hzH : z ∈ H := subset_closure ⟨0, rfl⟩
  have hx1zH : x1 * z ∈ H := subset_closure ⟨1, rfl⟩
  have hvH : b * c.u ∈ H := subset_closure ⟨2, rfl⟩
  have huxH : c.u * x ∈ H := subset_closure ⟨3, rfl⟩
  have huH : c.u ∈ H := subset_closure ⟨4, rfl⟩
  have hxH : x ∈ H := by simpa using H.mul_mem (H.inv_mem huH) huxH
  have hx1H : x1 ∈ H := by
    simpa only [mul_inv_cancel_right] using H.mul_mem hx1zH (H.inv_mem hzH)
  have hbH : b ∈ H := by
    simpa only [mul_inv_cancel_right] using H.mul_mem hvH (H.inv_mem huH)
  have hb1H : b * c.u * z ∈ H := H.mul_mem hvH hzH
  have hAz : fusionCore z ≤ H := p.fusion_le hx hb.1 hbne H hzH hbH hxH
  have hAu : fusionCore c.u ≤ H := p1.fusion_le hx1 hb1.1
    (other_vector_ne_one c p hb) H huH hb1H hx1H
  have hX : cubicInG h ≤ H := hx ▸ zpowers_le.mpr hxH
  have hX1 : c.X1 ≤ H := hx1 ▸ zpowers_le.mpr hx1H
  apply le_antisymm ?_ (sup_le (sup_le (sup_le hAz hAu) hX) hX1)
  let S := fusionCore z ⊔ fusionCore c.u ⊔ cubicInG h ⊔ c.X1
  have hAS : fusionCore z ≤ S := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hA1S : fusionCore c.u ≤ S := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hXS : cubicInG h ≤ S := le_sup_right.trans le_sup_left
  have hX1S : c.X1 ≤ S := le_sup_right
  have hzS : z ∈ S := hAS h.involution_mem_fusionCore
  have huA : c.u ∈ fusionCore c.u := by
    rw [← p1.decomposition]
    exact (le_sup_left : zpowers c.u ≤ zpowers c.u ⊔ movedFour c.u c.X1) (mem_zpowers c.u)
  have huS : c.u ∈ S := hA1S huA
  have hxS : x ∈ S := hXS (hx ▸ mem_zpowers x)
  have hx1S : x1 ∈ S := hX1S (hx1 ▸ mem_zpowers x1)
  have hbS : b ∈ S := hAS (p.moved_le hb.1)
  apply (closure_le _).mpr
  rintro t ⟨i, rfl⟩
  fin_cases i
  · exact hzS
  · exact S.mul_mem hx1S hzS
  · exact S.mul_mem hbS huS
  · exact S.mul_mem huS hxS
  · exact huS

/-- Conditional assembly of the local gluing. The remaining source assertion
is the compatibility of the two intrinsically defined fixed lines. -/
public theorem coxeterGluingData_of_four_data (c : CommutingCubicData h a)
    (p : CubicFourData z c.u (cubicInG h)) (p1 : CubicFourData c.u z c.X1)
    (halign : ∀ b ∈ fixedLine z c.u (cubicInG h), b ≠ 1 →
      b * c.u * z ∈ fixedLine c.u z c.X1) : Nonempty (CoxeterGluingData c) := by
  obtain ⟨x, hx⟩ := generator_of_card_three _ (cubicInG_card h)
  obtain ⟨x1, hx1⟩ := generator_of_card_three _ c.card_X1
  obtain ⟨b, hbne, _⟩ := (Nat.card_eq_two_iff' (1 : fixedLine z c.u (cubicInG h))).mp
    p.line_card
  have hb : (b : G) ∈ fixedLine z c.u (cubicInG h) := b.property
  have hbne' : (b : G) ≠ 1 := fun he => hbne (Subtype.ext he)
  have hb1 := halign b hb hbne'
  have hx3 : x ^ 3 = 1 := by
    have ho : orderOf x = 3 := by rw [← Nat.card_zpowers, hx, cubicInG_card]
    simpa only [ho] using pow_orderOf_eq_one x
  have hx13 : x1 ^ 3 = 1 := by
    have ho : orderOf x1 = 3 := by rw [← Nat.card_zpowers, hx1, c.card_X1]
    simpa only [ho] using pow_orderOf_eq_one x1
  have hu2 : c.u * c.u = 1 := by
    simpa only [c.u_order, pow_two] using pow_orderOf_eq_one c.u
  have hbu : Commute (b : G) c.u := mem_centralizer_singleton_iff.mp hb.2
  have hvz : Commute ((b : G) * c.u) z :=
    (p.commutes_base hb.1).mul_left c.u_commutes_z
  refine ⟨{
    x := x
    x_generator := hx
    x1 := x1
    x1_generator := hx1
    v := b * c.u
    v_sq := ?_
    v_commutes_z := hvz
    v_commutes_u := hbu.mul_left (Commute.refl c.u)
    left_braid := ?_
    right_braid := ?_
    generated := generated_of_fixed_vectors c p p1 hx hx1 hb hbne' hb1 }⟩
  · rw [← pow_two, hbu.mul_pow, pow_two, pow_two, p.square hb.1, hu2, one_mul]
  · have he : (x1 * z) * ((b : G) * c.u) = x1 * ((b : G) * c.u * z) := by
      rw [mul_assoc, hvz.eq.symm, ← mul_assoc]
    rw [he]
    exact rotate_cube (p1.cube hx1 hx13 hb1.1)
  · have he : ((b : G) * c.u) * (c.u * x) = (b : G) * x := by
      rw [mul_assoc, ← mul_assoc c.u, hu2, one_mul]
    rw [he]
    exact p.cube hx hx3 hb.1

/-- The source inputs supply both elementary-eight action contexts; only
calculation of their moved fours and compatibility of their fixed lines
remain to complete the gluing theorem. -/
public theorem coxeterGluingData_of_local_calculations (h : Hypotheses z)
    (d : FusionEightData z) {a : SourceGeometry h} (c : CommutingCubicData h a)
    (moduleCalculation : ∀ r q (X : Subgroup G),
      CubicEightContext r q X → CubicFourData r q X)
    (compatibility : CubicFourData z c.u (cubicInG h) → CubicFourData c.u z c.X1 →
      ∀ b ∈ fixedLine z c.u (cubicInG h), b ≠ 1 →
        b * c.u * z ∈ movedFour c.u c.X1) : Nonempty (CoxeterGluingData c) := by
  obtain ⟨ctx, ctx1⟩ := cubicEightContexts h d c
  have p := moduleCalculation z c.u (cubicInG h) ctx
  have p1 := moduleCalculation c.u z c.X1 ctx1
  apply coxeterGluingData_of_four_data c p p1
  intro b hb hbne
  exact (other_vector_mem_fixedLine_iff c p hb).mpr (compatibility p p1 b hb hbne)

/-- The local calculation of Lemma 4.6 for the supplied source geometry and
commuting cubic. Both moved-four calculations and their conjugate-core
compatibility are proved from the inputs, giving actual cubic generators,
the common middle reflection, both mixed braids and the literal generation
equality. No choice of the ambient order alternative is required. -/
public theorem coxeterGluingData_of_commutingCubic (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) (c : CommutingCubicData h a) :
    Nonempty (CoxeterGluingData c) := by
  exact coxeterGluingData_of_local_calculations h d c
    (fun _ _ _ k => cubicFourData_of_cubicEightContext k)
    (selected_compatible_fixed_vector h hn d c)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
