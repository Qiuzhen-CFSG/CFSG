module
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Cubic
public import CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition.Restriction
public import Theory.Representation.BinaryOddDisplacement

/-!
# Odd-prime displacement of the twelve-dimensional triple Mathieu module

The ambient quotient has order dividing two, so every odd-prime actor lies
in L. The genuine cover has odd-prime spectrum three, five, seven and eleven.
The cubic calculation gives eight (or twelve for central actors); the actual
Frobenius subgroup of order 55 gives the five bound; binary prime degree gives
the eleven bound. For seven, James uniqueness identifies the irreducible
restriction with its faithful binary dual. The central cubic scalar has no
fixed vectors, so the generic self-dual three-seven calculation gives full
displacement twelve. A noncentral cubic element supplies attainment of eight.

Every structural, restriction and self-duality premise is discharged from
`IsTripleM22 L`, the literal equality F*(G) = L, and the given module hypotheses.
Source: Aschbacher–Smith H.12.1(11), printed pp.393–394 (PDF pp.404–405).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
private theorem dual_irreducible (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible] :
    ρ.dual.IsIrreducible := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

/-- James uniqueness identifies the actual restricted representation with its binary dual. -/
theorem restriction_selfDual (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12) :
    Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))) := by
  let : L.Normal := hF ▸ inferInstance
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  have hf : Function.Injective σ := hρ.comp L.subtype_injective
  let : σ.IsIrreducible := TripleRecognition.irreducible_restriction L hL ρ hρ hd
  let : σ.dual.IsIrreducible := dual_irreducible σ
  have hfd : Function.Injective σ.dual := by
    intro g h he
    apply inv_injective
    apply hf
    ext v
    apply Module.eval_apply_injective (ZMod 2)
    ext f
    exact congrArg (fun a : Module.Dual (ZMod 2) V => a v) (LinearMap.congr_fun he f)
  exact hL.equiv_of_finrank_twelve σ hf σ.dual hfd hd
    ((Subspace.dual_finrank_eq (K := ZMod 2) (V := V)).trans hd)

/-- The Frobenius subgroup of order 55 forces displacement at least eight at order five. -/
theorem eight_le_fixedCodim_five (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (x : G) (hx : orderOf x = 5) : 8 ≤ fixedCodim ρ (zpowers x) := by
  have hm := AmbientActors.odd_prime_mem L hL hF Nat.prime_five (by decide) x hx
  let y : L := ⟨x, hm⟩
  have hy : orderOf y = 5 := (Subgroup.orderOf_coe y).symm.trans hx
  obtain ⟨K, hK, hn, hf, _⟩ := AmbientActors.exists_eleven_five hL y hy
  have hb := eight_le_fixedCodim_of_five_normalizes_eleven (ρ.comp L.subtype)
    (hρ.comp L.subtype_injective) y hy K hK (hn (mem_zpowers y)) (fun k hk =>
      Subtype.ext (hf y (mem_zpowers y) (by
        intro h
        simp [h] at hy) k k.property hk))
  unfold fixedCodim at hb ⊢
  rwa [fixedSpace_comp_map, MonoidHom.map_zpowers] at hb

/-- Every septic actor has full displacement on the twelve-dimensional ambient module. -/
theorem seven_fixedCodim_eq_twelve (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12)
    (x : G) (hx : orderOf x = 7) : fixedCodim ρ (zpowers x) = 12 := by
  have hm := AmbientActors.odd_prime_mem L hL hF Nat.prime_seven (by decide) x hx
  let y : L := ⟨x, hm⟩
  have hy : orderOf y = 7 := (Subgroup.orderOf_coe y).symm.trans hx
  obtain ⟨e⟩ := restriction_selfDual L hL hF ρ hρ hd
  have hzfix : invariants ((ρ.comp L.subtype).comp (zpowers hL.centralScalar).subtype) = ⊥ := by
    change fixedSpace (ρ.comp L.subtype) (zpowers hL.centralScalar) = ⊥
    rw [← hL.center_eq_zpowers_centralScalar, fixedSpace_comp_map]
    exact center_fixedSpace_eq_bot L hL hF ρ hρ
  have hzcomm : Commute hL.centralScalar y :=
    (mem_center_iff.mp hL.centralScalar_mem_center y).symm
  have hb := fixedCodim_eq_twelve_of_selfDual_three_seven (ρ.comp L.subtype)
    (hρ.comp L.subtype_injective) (RepEquiv.ofRepresentationEquiv e) hL.centralScalar y hL.centralScalar_order hy
    hzcomm hzfix hd
  unfold fixedCodim at hb ⊢
  rwa [fixedSpace_comp_map, MonoidHom.map_zpowers] at hb

/-- The exact noncentral cubic displacement on the original restricted module. -/
theorem noncentral_three_fixedCodim_eq_eight (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12)
    (x : L) (hx : orderOf x = 3) (hxc : x ∉ center L) :
    fixedCodim (ρ.comp L.subtype) (zpowers x) = 8 := by
  rw [noncentral_three_restriction_fixedCodim L hL hF ρ hρ x hx hxc, hd]

/-- Every odd-prime-order ambient element moves at least eight dimensions. -/
theorem eight_le_fixedCodim_odd_prime (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : G) (hx : orderOf x = p) :
    8 ≤ fixedCodim ρ (zpowers x) := by
  rcases AmbientActors.ambient_odd_prime_order_cases L hL hF hp hp2 x hx with
    rfl | rfl | rfl | rfl
  · have hb := four_mul_sixth_le_fixedCodim_three L hL hF ρ hρ x hx
    simpa only [hd] using hb
  · exact eight_le_fixedCodim_five L hL hF ρ hρ x hx
  · rw [seven_fixedCodim_eq_twelve L hL hF ρ hρ hd x hx]
    decide
  · exact (by decide : 8 ≤ 10).trans (ten_le_fixedCodim_of_order_eleven ρ hρ x hx)

/-- An actual ambient order-three element attains the odd-prime lower bound. -/
theorem exists_three_fixedCodim_eq_eight (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12) :
    ∃ x : G, x ∈ L ∧ orderOf x = 3 ∧ fixedCodim ρ (zpowers x) = 8 := by
  obtain ⟨x, hx, hxc⟩ := exists_noncentral_three hL
  refine ⟨x, x.property, (Subgroup.orderOf_coe x).trans hx, ?_⟩
  rw [noncentral_three_fixedCodim L hL hF ρ hρ x hx hxc, hd]
end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
