module
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Odd-order displacement on the native ten-dimensional M22 modules

Odd-order averaging makes fixed dimensions additive across the actual pair
line in the eleven-dimensional cocode. Thus quotienting preserves displacement.
The proved native M24 point restrictions give the odd-prime bound six, its
literal six-fixed-point equality criterion, and the fixed dimensions zero and
one at orders eleven and seven. Cauchy's theorem supplies an actual attaining
cubic element. Equivariant coordinate duality transfers every cyclic result
to the existing code hyperplane.

Source: Aschbacher--Smith, H.13.1--2 and the parameter discussion, printed
pp.395--396, combined manuscript of 1 March 2004. No Atlas class-name
identification is assumed in the numerical equality criterion.
-/

public section
noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender
namespace MathieuCode

theorem m22Outer_code_cocode_fixedCodim_zpowers (g : m22PairStabilizer) :
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) =
      fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) := by
  have he := fixedCodim_map_equivariant m22OuterCodeRepresentation
    m22OuterCocodeRepresentation.dual (MonoidHom.id m22PairStabilizer)
    m22CodeCocodeDuality m22CodeCocodeDuality_equivariant (Subgroup.zpowers g)
  simpa only [Subgroup.map_id, fixedCodim_zpowers_dual] using he

theorem m22_code_cocode_fixedCodim_zpowers (g : M22) :
    fixedCodim m22CodeRepresentation (Subgroup.zpowers g) =
      fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) := by
  have he := fixedCodim_map_equivariant m22CodeRepresentation
    m22CocodeRepresentation.dual (MonoidHom.id M22)
    m22CodeCocodeDuality m22CodeCocodeDuality_equivariant_native (Subgroup.zpowers g)
  simpa only [Subgroup.map_id, fixedCodim_zpowers_dual] using he

theorem m22_code_cocode_fixedCodim_cyclic (D : Subgroup M22) [IsCyclic D] :
    fixedCodim m22CodeRepresentation D = fixedCodim m22CocodeRepresentation D := by
  obtain ⟨g, rfl⟩ := D.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  exact m22_code_cocode_fixedCodim_zpowers g

theorem m22Outer_cocode_fixed_finrank_of_odd (D : Subgroup m22PairStabilizer)
    (ho : Odd (Nat.card D)) :
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation D) + 1 =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (D.map m22PairStabilizer.subtype)) := by
  have h := finrank_fixedSpace_quotient_of_odd
    (cocodeRepresentation.comp m22PairStabilizer.subtype) m22PairLineSubrepresentation D ho
  have ht : fixedSpace m22PairLineSubrepresentation.toRepresentation D = ⊤ := by
    apply top_unique
    intro v _ a
    apply Subtype.ext
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.property
    change cocodeRepresentation a.val.val v.val = v.val
    rw [← hc, map_smul, m22PairClass_invariant]
  rw [ht, finrank_top] at h
  change Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation D) +
    Module.finrank (ZMod 2) m22PairLine = _ at h
  rw [finrank_m22PairLine, fixedSpace_comp_map] at h
  exact h

theorem m22Outer_cocode_fixedCodim_of_odd (D : Subgroup m22PairStabilizer)
    (ho : Odd (Nat.card D)) :
    fixedCodim m22OuterCocodeRepresentation D =
      fixedCodim cocodeRepresentation (D.map m22PairStabilizer.subtype) := by
  have h := m22Outer_cocode_fixed_finrank_of_odd D ho
  have hq := fixedCodim_add_finrank m22OuterCocodeRepresentation D
  have ha := fixedCodim_add_finrank cocodeRepresentation (D.map m22PairStabilizer.subtype)
  rw [finrank_m22Cocode] at hq
  rw [finrank_cocode] at ha
  omega

private theorem m22ToPairStabilizer_injective : Function.Injective m22ToPairStabilizer := by
  intro a b h
  exact m22Embedding_injective (congrArg Subtype.val h)

theorem m22_cocode_fixed_finrank_of_odd (D : Subgroup M22) (ho : Odd (Nat.card D)) :
    Module.finrank (ZMod 2) (fixedSpace m22CocodeRepresentation D) + 1 =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (D.map m22Embedding)) := by
  have h := m22Outer_cocode_fixed_finrank_of_odd (D.map m22ToPairStabilizer)
    (by rwa [Subgroup.card_map_of_injective m22ToPairStabilizer_injective])
  rw [Subgroup.map_map] at h
  change Module.finrank (ZMod 2)
    (fixedSpace (m22OuterCocodeRepresentation.comp m22ToPairStabilizer) D) + 1 = _
  rw [fixedSpace_comp_map]
  exact h

theorem m22_cocode_fixedCodim_of_odd (D : Subgroup M22) (ho : Odd (Nat.card D)) :
    fixedCodim m22CocodeRepresentation D =
      fixedCodim cocodeRepresentation (D.map m22Embedding) := by
  have h := m22_cocode_fixed_finrank_of_odd D ho
  have hq := fixedCodim_add_finrank m22CocodeRepresentation D
  have ha := fixedCodim_add_finrank cocodeRepresentation (D.map m22Embedding)
  rw [finrank_m22Cocode] at hq
  rw [finrank_cocode] at ha
  omega

theorem m22_cocode_fixedCodim_ge_six (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    6 ≤ fixedCodim m22CocodeRepresentation D := by
  rw [m22_cocode_fixedCodim_of_odd D (hD.symm ▸ ho)]
  exact cocode_fixedCodim_ge_six _ hp ho
    ((Subgroup.card_map_of_injective m22Embedding_injective).trans hD)

theorem m22_cocode_fixedCodim_eq_six_iff (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m22CocodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints (D.map m22Embedding) (Fin 24)) = 6 := by
  rw [m22_cocode_fixedCodim_of_odd D (hD.symm ▸ ho)]
  exact cocode_fixedCodim_eq_six_iff _ hp ho
    ((Subgroup.card_map_of_injective m22Embedding_injective).trans hD)

theorem m22_code_fixedCodim_ge_six (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    6 ≤ fixedCodim m22CodeRepresentation D := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [m22_code_cocode_fixedCodim_cyclic]
  exact m22_cocode_fixedCodim_ge_six D hp ho hD

theorem m22_code_fixedCodim_eq_six_iff (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m22CodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints (D.map m22Embedding) (Fin 24)) = 6 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [m22_code_cocode_fixedCodim_cyclic]
  exact m22_cocode_fixedCodim_eq_six_iff D hp ho hD

/-- The exact fixed-dimension equation on the literal ten-dimensional quotient. -/
theorem m22_prime_cocode_fixed_point_equation (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    2 * (Module.finrank (ZMod 2) (fixedSpace m22CocodeRepresentation D) + 2) * p =
      24 + (p - 1) * Nat.card (MulAction.fixedPoints (D.map m22Embedding) (Fin 24)) := by
  have h := prime_cocode_fixed_point_equation (D.map m22Embedding) hp ho
    ((Subgroup.card_map_of_injective m22Embedding_injective).trans hD)
  rw [← m22_cocode_fixed_finrank_of_odd D (hD.symm ▸ ho)] at h
  simpa only [Nat.add_assoc] using h

theorem m22_cocode_fixed_finrank_eleven (D : Subgroup M22) (hD : Nat.card D = 11) :
    Module.finrank (ZMod 2) (fixedSpace m22CocodeRepresentation D) = 0 := by
  have he := m22_prime_cocode_fixed_point_equation D (by decide) (by decide) hD
  have hp := m24_odd_prime_point_restriction (D.map m22Embedding) (by decide) (by decide)
    ((Subgroup.card_map_of_injective m22Embedding_injective).trans hD)
  omega

theorem m22_cocode_fixed_finrank_seven (D : Subgroup M22) (hD : Nat.card D = 7) :
    Module.finrank (ZMod 2) (fixedSpace m22CocodeRepresentation D) = 1 := by
  have he := m22_prime_cocode_fixed_point_equation D (by decide) (by decide) hD
  have hp := m24_odd_prime_point_restriction (D.map m22Embedding) (by decide) (by decide)
    ((Subgroup.card_map_of_injective m22Embedding_injective).trans hD)
  omega

theorem m22_code_cocode_fixed_finrank_cyclic (D : Subgroup M22) [IsCyclic D] :
    Module.finrank (ZMod 2) (fixedSpace m22CodeRepresentation D) =
      Module.finrank (ZMod 2) (fixedSpace m22CocodeRepresentation D) := by
  have hc := fixedCodim_add_finrank m22CodeRepresentation D
  have ht := fixedCodim_add_finrank m22CocodeRepresentation D
  rw [finrank_m22Code] at hc
  rw [finrank_m22Cocode] at ht
  have := m22_code_cocode_fixedCodim_cyclic D
  omega

theorem m22_code_fixed_finrank_eleven (D : Subgroup M22) (hD : Nat.card D = 11) :
    Module.finrank (ZMod 2) (fixedSpace m22CodeRepresentation D) = 0 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [m22_code_cocode_fixed_finrank_cyclic]
  exact m22_cocode_fixed_finrank_eleven D hD

theorem m22_code_fixed_finrank_seven (D : Subgroup M22) (hD : Nat.card D = 7) :
    Module.finrank (ZMod 2) (fixedSpace m22CodeRepresentation D) = 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [m22_code_cocode_fixed_finrank_cyclic]
  exact m22_cocode_fixed_finrank_seven D hD

/-- Cubic subgroups of M22 fix six points on the ambient 24-point set. -/
theorem m22_cubic_six_fixed (D : Subgroup M22) (hD : Nat.card D = 3) :
    Nat.card (MulAction.fixedPoints (D.map m22Embedding) (Fin 24)) = 6 := by
  have hp := m24_odd_prime_point_restriction (D.map m22Embedding) (by decide) (by decide)
    ((Subgroup.card_map_of_injective m22Embedding_injective).trans hD)
  have hn : Nonempty (MulAction.fixedPoints (D.map m22Embedding) (Fin 24)) := by
    refine ⟨⟨0, ?_⟩⟩
    rintro ⟨_, g, hg, rfl⟩
    exact m22Embedding_fixed_zero g
  have hpos := (Nat.card_pos_iff.mpr ⟨hn, inferInstance⟩)
  omega

theorem m22_cubic_cocode_displacement (D : Subgroup M22) (hD : Nat.card D = 3) :
    fixedCodim m22CocodeRepresentation D = 6 :=
  (m22_cocode_fixedCodim_eq_six_iff D (by decide) (by decide) hD).mpr
    ⟨rfl, m22_cubic_six_fixed D hD⟩

theorem m22_cubic_code_displacement (D : Subgroup M22) (hD : Nat.card D = 3) :
    fixedCodim m22CodeRepresentation D = 6 :=
  (m22_code_fixedCodim_eq_six_iff D (by decide) (by decide) hD).mpr
    ⟨rfl, m22_cubic_six_fixed D hD⟩

/-- A genuine order-three element attains the bound on both native modules. -/
theorem exists_m22_displacement_six : ∃ g : M22, orderOf g = 3 ∧
    fixedCodim m22CodeRepresentation (Subgroup.zpowers g) = 6 ∧
    fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) = 6 := by
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := M22) 3
    (by rw [m22_order]; norm_num)
  have hD : Nat.card (Subgroup.zpowers g) = 3 := (Nat.card_zpowers g).trans hg
  exact ⟨g, hg, m22_cubic_code_displacement _ hD, m22_cubic_cocode_displacement _ hD⟩

/-- In the native M22 subgroup, the six-fixed-point condition is automatic at order three. -/
theorem m22_cocode_fixedCodim_eq_six_iff_cubic (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m22CocodeRepresentation D = 6 ↔ p = 3 := by
  rw [m22_cocode_fixedCodim_eq_six_iff D hp ho hD]
  exact ⟨And.left, fun h => ⟨h, m22_cubic_six_fixed D (hD.trans h)⟩⟩

theorem m22_code_fixedCodim_eq_six_iff_cubic (D : Subgroup M22) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m22CodeRepresentation D = 6 ↔ p = 3 := by
  rw [m22_code_fixedCodim_eq_six_iff D hp ho hD]
  exact ⟨And.left, fun h => ⟨h, m22_cubic_six_fixed D (hD.trans h)⟩⟩

theorem m22Outer_cocode_fixedCodim_ge_six (D : Subgroup m22PairStabilizer) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    6 ≤ fixedCodim m22OuterCocodeRepresentation D := by
  rw [m22Outer_cocode_fixedCodim_of_odd D (hD.symm ▸ ho)]
  exact cocode_fixedCodim_ge_six _ hp ho
    ((Subgroup.card_map_of_injective m22PairStabilizer.subtype_injective).trans hD)

theorem m22Outer_cocode_fixedCodim_eq_six_iff (D : Subgroup m22PairStabilizer) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m22OuterCocodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints (D.map m22PairStabilizer.subtype) (Fin 24)) = 6 := by
  rw [m22Outer_cocode_fixedCodim_of_odd D (hD.symm ▸ ho)]
  exact cocode_fixedCodim_eq_six_iff _ hp ho
    ((Subgroup.card_map_of_injective m22PairStabilizer.subtype_injective).trans hD)

theorem m22Outer_code_cocode_fixedCodim_cyclic (D : Subgroup m22PairStabilizer) [IsCyclic D] :
    fixedCodim m22OuterCodeRepresentation D = fixedCodim m22OuterCocodeRepresentation D := by
  obtain ⟨g, rfl⟩ := D.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  exact m22Outer_code_cocode_fixedCodim_zpowers g

theorem m22Outer_code_fixedCodim_ge_six (D : Subgroup m22PairStabilizer) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    6 ≤ fixedCodim m22OuterCodeRepresentation D := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [m22Outer_code_cocode_fixedCodim_cyclic]
  exact m22Outer_cocode_fixedCodim_ge_six D hp ho hD

theorem m22Outer_code_fixedCodim_eq_six_iff (D : Subgroup m22PairStabilizer) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hD : Nat.card D = p) :
    fixedCodim m22OuterCodeRepresentation D = 6 ↔
      p = 3 ∧ Nat.card (MulAction.fixedPoints (D.map m22PairStabilizer.subtype) (Fin 24)) = 6 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [m22Outer_code_cocode_fixedCodim_cyclic]
  exact m22Outer_cocode_fixedCodim_eq_six_iff D hp ho hD

/-- The attaining native element also attains the bound in the actual outer extension. -/
theorem exists_m22Outer_displacement_six : ∃ g : m22PairStabilizer, orderOf g = 3 ∧
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 6 ∧
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 6 := by
  obtain ⟨g, hg, hc, ht⟩ := exists_m22_displacement_six
  refine ⟨m22ToPairStabilizer g,
    (orderOf_injective m22ToPairStabilizer m22ToPairStabilizer_injective g).trans hg, ?_, ?_⟩
  · rw [← MonoidHom.map_zpowers, fixedCodim, ← fixedSpace_comp_map]
    exact hc
  · rw [← MonoidHom.map_zpowers, fixedCodim, ← fixedSpace_comp_map]
    exact ht

end MathieuCode
