module

public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-!
# Central restrictions and quotient automorphisms

For a characteristic self-centralizing subgroup V of H, an automorphism whose
restriction to V is central in Aut(V) acts trivially on H/V. Naturality of
conjugation puts each displacement x⁻¹a(x) in the centralizer of V.
This is the quotient compatibility needed for the scalar obstruction in
Aschbacher–Smith, §13.1, printed p.876. The imported restriction-kernel theorem
also proves that the kernel is a p-group whenever V is a finite p-group.
-/

namespace Subgroup

/-- Central restriction to a characteristic self-centralizing subgroup forces
trivial action on the quotient. -/
public theorem quotientAut_eq_one_of_restriction_mem_center
    {H : Type*} [Group H] (V : Subgroup H) [V.Characteristic]
    (hself : centralizer (V : Set H) ≤ V) (a : MulAut H)
    (ha : MulAut.characteristic V a ∈ center (MulAut V)) : quotientAut V a = 1 := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change quotientAut V a (QuotientGroup.mk' V x) = QuotientGroup.mk' V x
    rw [quotientAut_apply_mk]
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    apply hself
    intro v hv
    obtain ⟨w, hw⟩ := (MulAut.characteristic V a).surjective (⟨v, hv⟩ : V)
    have h := congrArg Subtype.val
      (DFunLike.congr_fun (mem_center_iff.mp ha (MulAut.conjNormal x)) w)
    change x * a w * x⁻¹ = a (x * w * x⁻¹) at h
    have hw' : a w = v := congrArg Subtype.val hw
    rw [map_mul, map_mul, map_inv, hw'] at h
    have hh := congrArg (fun t : H => x⁻¹ * t * a x) h
    group at hh
    simpa only [mul_assoc, zpow_neg_one] using hh

/-- The natural map between characteristic quotients intertwines their automorphism actions. -/
public theorem quotientAut_map_compatibility {H : Type*} [Group H] (V W : Subgroup H)
    [V.Characteristic] [W.Characteristic] (hVW : V ≤ W) (a : MulAut H)
    (x : H ⧸ V) :
    QuotientGroup.map V W (MonoidHom.id H) (by simpa using hVW) (quotientAut V a x) =
      quotientAut W a (QuotientGroup.map V W (MonoidHom.id H) (by simpa using hVW) x) := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.map V W (MonoidHom.id H) (by simpa using hVW)
      (quotientAut V a (QuotientGroup.mk' V x)) = _
    rw [quotientAut_apply_mk]
    simp only [QuotientGroup.mk'_apply, QuotientGroup.map_mk, MonoidHom.id_apply]
    exact (quotientAut_apply_mk W a x).symm

/-- An automorphism fixing H/V also fixes H/W whenever V ≤ W. -/
public theorem quotientAut_ker_mono {H : Type*} [Group H] (V W : Subgroup H)
    [V.Characteristic] [W.Characteristic] (hVW : V ≤ W) :
    (quotientAut V).ker ≤ (quotientAut W).ker := by
  intro a ha
  change quotientAut W a = 1
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change quotientAut W a (QuotientGroup.mk' W x) = QuotientGroup.mk' W x
    rw [quotientAut_apply_mk]
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    apply hVW
    apply QuotientGroup.eq.mp
    have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp ha) (QuotientGroup.mk' V x)
    rw [quotientAut_apply_mk] at h
    simpa only [MulAut.one_apply, QuotientGroup.mk'_apply] using h.symm


/-- Inversion on a characteristic subgroup is central in its automorphism group. -/
public theorem restriction_mem_center_of_inverts
    {H : Type*} [Group H] (V : Subgroup H) [V.Characteristic]
    (a : MulAut H) (ha : ∀ v : V, a v = (v : H)⁻¹) :
    MulAut.characteristic V a ∈ center (MulAut V) := by
  apply mem_center_iff.mpr
  intro b
  apply MulEquiv.ext
  intro v
  have hi (w : V) : MulAut.characteristic V a w = w⁻¹ := Subtype.ext (ha w)
  change b (MulAut.characteristic V a v) = MulAut.characteristic V a (b v)
  rw [hi, hi, map_inv]
end Subgroup
