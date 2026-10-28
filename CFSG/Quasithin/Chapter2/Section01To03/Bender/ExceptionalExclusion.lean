module

public import Theory.Representation.GoldschmidtONan.ExceptionalOrbit
public import Theory.ElementaryAbelian.VectorSpace
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionLocalControl

/-!
# Excluding the exceptional actor in the source Bender reduction

The actor is the actual image of M in the automorphism group of the
selected elementary abelian subgroup U. Its binary representation on
Additive U is constructed here, is faithful, and agrees with the literal
ambient conjugation. If its dimension is three and its order is 21, the
seven-point orbit theorem makes every nonidentity element of U conjugate
to the selected z inside M. Conjugating C_G(z) ≤ M then gives C_G(u) ≤ M
for every such u. This contradicts the source choice of u in J.

Source: Aschbacher–Smith, Proposition 2.2.2, printed pp.519–520. The
component/TI geometry constructing the remaining GO Input fields is
separate; no such geometry or full GO alternatives is asserted here.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M : Subgroup G}

/-- The literal Aut_M(U), retaining its surjection from M. -/
abbrev sourceActionImage (w : LocalControlWitness T M) :=
  (conjugationAction M w.U w.normalizes).range

variable (w : LocalControlWitness T M) [IsElementaryAbelian 2 w.U]

/-- The faithful image acts linearly on the original selected U. The
elementary-abelian instance is supplied by the field `w.elementary`. -/
noncomputable def sourceImageRepresentation :
    Representation (ZMod 2) (sourceActionImage w) (Additive w.U) where
  toFun a := (a : MulAut w.U).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    rfl

omit [Finite G] in
/-- Passing to the actual action image proves faithfulness. -/
theorem sourceImageRepresentation_injective :
    Function.Injective (sourceImageRepresentation w) := by
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro u
  exact congrArg (fun f : Module.End (ZMod 2) (Additive w.U) =>
    (f (Additive.ofMul u)).toMul) hab

omit [Finite G] in
/-- The marking used by the source agrees with ambient conjugation. -/
theorem sourceImageRepresentation_apply (m : M) (v : Additive w.U) :
    ((sourceImageRepresentation w
      ((conjugationAction M w.U w.normalizes).rangeRestrict m) v).toMul : G) =
      (m : G) * (v.toMul : G) * (m : G)⁻¹ := rfl

omit [Finite G] in
private theorem centralizer_le_of_conjugate {N : Subgroup G} {z u m : G}
    (hC : centralizer ({z} : Set G) ≤ N) (hm : m ∈ N)
    (he : m * z * m⁻¹ = u) : centralizer ({u} : Set G) ≤ N := by
  rw [← he]
  intro g hg
  have hc : Commute g (m * z * m⁻¹) := mem_centralizer_singleton_iff.mp hg
  have hd : Commute (m⁻¹ * g * m) z := by
    have hh := hc.map (MulAut.conj m⁻¹).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hmem := N.mul_mem (N.mul_mem hm
    (hC (mem_centralizer_singleton_iff.mpr hd.eq))) (N.inv_mem hm)
  have hcancel : m * (m⁻¹ * g * m) * m⁻¹ = g := by group
  exact hcancel ▸ hmem

omit [Finite G] in
/-- Transitivity on the actual selected U forces all its nonidentity
centralizers into M, by transport of the distinguished z-centralizer. -/
theorem LocalControlWitness.centralizers_le_of_image_transitive
    (htrans : Representation.GoldschmidtONan.NonzeroTransitive
      (sourceImageRepresentation w)) :
    ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M := by
  intro u hu hune
  let zV : Additive w.U := Additive.ofMul ⟨w.z, w.z_mem⟩
  let uV : Additive w.U := Additive.ofMul ⟨u, hu⟩
  have hzV : zV ≠ 0 := fun he => w.z_ne_one
    (congrArg (fun v : Additive w.U => (v.toMul : G)) he)
  have huV : uV ≠ 0 := fun he => hune
    (congrArg (fun v : Additive w.U => (v.toMul : G)) he)
  obtain ⟨a, ha⟩ := htrans zV hzV uV huV
  obtain ⟨m, hm⟩ := a.property
  have he := congrArg (fun v : Additive w.U => (v.toMul : G)) ha
  change (((a : MulAut w.U) ⟨w.z, w.z_mem⟩) : G) = u at he
  rw [← hm] at he
  change (m : G) * w.z * (m : G)⁻¹ = u at he
  exact centralizer_le_of_conjugate w.centralizer_le m.property he

/-- The numerical exceptional alternative on the actual actor suffices;
no Frobenius-model equivalence or character theory is required. -/
theorem LocalControlWitness.centralizers_le_of_image_order_twenty_one
    (hdim : Module.finrank (ZMod 2) (Additive w.U) = 3)
    (hcard : Nat.card (sourceActionImage w) = 21) :
    ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M := by
  apply w.centralizers_le_of_image_transitive
  exact Representation.GoldschmidtONan.nonzeroTransitive_of_finrank_three_of_seven_dvd
    (sourceImageRepresentation_injective w) hdim (by rw [hcard]; decide)

/-- The exact J-nonempty source hypothesis excludes alternative (iv) of
the GO theorem on the actual Aut_M(U) action. -/
theorem LocalControlWitness.not_exceptional_of_bad_centralizer
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    (Y : Subgroup (sourceActionImage w)) :
    ¬ Representation.GoldschmidtONan.ExceptionalCase (sourceImageRepresentation w) Y := by
  intro he
  obtain ⟨u, hu, hune, hC⟩ := hbad
  exact hC (w.centralizers_le_of_image_order_twenty_one he.2.1 he.2.2.1 u hu hune)

end CFSG.Quasithin.Chapter2.BenderFusion
