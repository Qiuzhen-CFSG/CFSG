module
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.Properties.FixedHexads

/-!
# A native complement in every degree-22 hexad stabilizer

A nonidentity element of the pointwise kernel is an involution, whose fixed
points form exactly the original hexad. Thus this kernel acts freely on the
sixteen complementary points. Its order sixteen makes the action regular.
Restriction of the literal alternating quotient to a complementary-point
stabilizer is consequently bijective; its inverse is a genuine section.

Source: Aschbacher--Smith, I.2.2(6), printed p.412 (PDF p.423), the complement
to the E16 kernel used in the proof. The fixed-point and kernel facts come
from the concrete degree-22 and degree-23 Witt-design actions.
-/

@[expose] public section
namespace Sporadic.Mathieu
open scoped Pointwise
noncomputable section

/-- The literal six-point quotient map. -/
def m22HexadSixMap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    MulAction.stabilizer M22 B →* alternatingGroup (Fin 6) :=
  (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
    (QuotientGroup.mk' (m22SetAction B).ker)

@[simp] theorem m22HexadSixMap_coe {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) :
    (m22HexadSixMap hB g).val = m22HexadAction hB g := rfl

theorem m22HexadSixMap_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22HexadSixMap hB).ker = (m22SetAction B).ker :=
  (MonoidHom.ker_mulEquiv_comp _ (m22HexadQuotientAlternatingEquiv hB)).trans
    (QuotientGroup.ker_mk' _)

theorem m22HexadSixMap_surjective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (m22HexadSixMap hB) :=
  (m22HexadQuotientAlternatingEquiv hB).surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- A point outside a hexad has trivial stabilizer in its pointwise kernel. -/
theorem m22HexadKernel_eq_one_of_fix {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (u : (m22SetAction B).ker) {a : Fin 22} (ha : a ∉ B)
    (hu : u.val.val • a = a) : u = 1 := by
  by_contra hne
  let := m22HexadKernel_elementaryAbelian hB
  have hu2 : orderOf u = 2 := orderOf_eq_prime_iff.mpr
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (m22SetAction B).ker) u, hne⟩
  have hu2' : orderOf u.val.val = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu2]
  obtain ⟨D, hD, hfix⟩ := m22_exists_fixed_hexad u.val.val hu2'
  have hBD : B = D := Finset.eq_of_subset_of_card_le
    (fun x hx => (hfix x).mp ((mem_m22SetAction_ker B u.val).mp u.property x hx))
    (by rw [m22Block_card _ hD, m22Block_card _ hB])
  exact ha (hBD ▸ (hfix a).mp hu)

theorem m22Hexad_complement_stable {B : Finset (Fin 22)}
    (g : MulAction.stabilizer M22 B) {a : Fin 22} (ha : a ∉ B) : g.val • a ∉ B := by
  intro h
  have hi := (MulAction.mem_stabilizer_finset.mp g⁻¹.property) (g.val • a)
  exact ha (by simpa using hi.mpr h)

/-- Evaluation of the actual kernel on any complementary point is bijective. -/
theorem m22HexadKernel_regular {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {a : Fin 22} (ha : a ∉ B) :
    Function.Bijective (fun u : (m22SetAction B).ker =>
      (⟨u.val.val • a, m22Hexad_complement_stable u.val ha⟩ : {x : Fin 22 // x ∉ B})) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro u v huv
    have he : v⁻¹ * u = 1 := m22HexadKernel_eq_one_of_fix hB _ ha (by
      change v.val.val⁻¹ • (u.val.val • a) = a
      rw [show u.val.val • a = v.val.val • a from congrArg Subtype.val huv, inv_smul_smul])
    exact (inv_mul_eq_one.mp he).symm
  · rw [m22HexadKernel_card hB, Nat.card_eq_fintype_card]
    have hc : Fintype.card {x : Fin 22 // x ∉ B} = 22 - B.card := by
      simp [Fintype.card_subtype_compl]
    rw [hc, m22Block_card _ hB]

/-- The quotient restricts bijectively to a complementary-point stabilizer. -/
theorem m22HexadSixMap_pointStabilizer_bijective {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) {a : Fin 22} (ha : a ∉ B) :
    Function.Bijective ((m22HexadSixMap hB).comp
      (MulAction.stabilizer (MulAction.stabilizer M22 B) a).subtype) := by
  let q := m22HexadSixMap hB
  constructor
  · intro g h hgh
    have hk : g.val * h.val⁻¹ ∈ (m22SetAction B).ker := by
      rw [← m22HexadSixMap_ker hB]
      change q (g.val * h.val⁻¹) = 1
      rw [map_mul, map_inv, show q g.val = q h.val from hgh, mul_inv_cancel]
    have he := m22HexadKernel_eq_one_of_fix hB ⟨g.val * h.val⁻¹, hk⟩ ha (by
      change (g.val * h.val⁻¹) • a = a
      rw [mul_smul, show h.val⁻¹ • a = a from inv_smul_eq_iff.mpr h.property.symm, g.property])
    apply Subtype.ext
    exact mul_inv_eq_one.mp (congrArg Subtype.val he)
  · intro z
    obtain ⟨g, hg⟩ := m22HexadSixMap_surjective hB z
    obtain ⟨u, hu⟩ := (m22HexadKernel_regular hB (m22Hexad_complement_stable g ha)).surjective
      ⟨a, ha⟩
    have hp : u.val * g ∈ MulAction.stabilizer (MulAction.stabilizer M22 B) a :=
      congrArg Subtype.val hu
    refine ⟨⟨u.val * g, hp⟩, ?_⟩
    change q (u.val * g) = z
    have hqu : q u.val = 1 := by
      change u.val ∈ q.ker
      rw [m22HexadSixMap_ker hB]
      exact u.property
    rw [map_mul, hqu, one_mul]
    exact hg

/-- A section fixing the supplied complementary point. -/
def m22HexadPointSection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {a : Fin 22} (ha : a ∉ B) :
    alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B :=
  (MulAction.stabilizer (MulAction.stabilizer M22 B) a).subtype.comp
    (MulEquiv.ofBijective _ (m22HexadSixMap_pointStabilizer_bijective hB ha)).symm.toMonoidHom

@[simp] theorem m22HexadSixMap_pointSection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {a : Fin 22} (ha : a ∉ B) (z : alternatingGroup (Fin 6)) :
    m22HexadSixMap hB (m22HexadPointSection hB ha z) = z :=
  (MulEquiv.ofBijective _ (m22HexadSixMap_pointStabilizer_bijective hB ha)).apply_symm_apply z

@[simp] theorem m22HexadPointSection_fixes {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {a : Fin 22} (ha : a ∉ B) (z : alternatingGroup (Fin 6)) :
    (m22HexadPointSection hB ha z).val • a = a :=
  ((MulEquiv.ofBijective _
    (m22HexadSixMap_pointStabilizer_bijective hB ha)).symm z).property

end
end Sporadic.Mathieu
