module
public import Theory.Representation.BinaryTransvectionGroups.RootForms.Exchange
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.ElementaryAbelian.Injective
public import Mathlib.FieldTheory.Finiteness

/-!
# The full common-center radical in a binary linear group

The radical of a line is elementary abelian of order 2^(dim V-1).
Its nonidentity elements are conjugate by transformations fixing the center,
and it lies in every Sylow subgroup fixing that center. These are the precise
root-group inputs used in G.10.4 to propagate quadratic action.
-/

@[expose] public section
open Module Subgroup BinaryTransvectionGroups
namespace BinaryLinear.LineRadical
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem scalar_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 :=
  (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc

private theorem common_one {f k : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (hk : k ≠ 0) :
    ∃ b, f b = 1 ∧ k b = 1 := by
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hk) 1
  by_cases hky : k x = 0
  · by_cases hfy : f y = 0
    · exact ⟨x+y, by simp [hx,hfy], by simp [hky,hy]⟩
    · exact ⟨y,scalar_one hfy,hy⟩
  · exact ⟨x,hx,scalar_one hky⟩

/-- Conjugacy inside the stabilizer of the original center vector. -/
theorem conjugate_fixing_center (a : V) (ha : a ≠ 0)
    (f : Module.Dual (ZMod 2) V) (hf : f ≠ 0) (hfa : f a = 0)
    {t : BinaryLinear.GL V} (ht : t ∈ radical (Submodule.span (ZMod 2) {a})) (ht1 : t ≠ 1) :
    ∃ c : BinaryLinear.GL V, c a = a ∧ c * transvection a f hfa * c⁻¹ = t := by
  obtain ⟨k,hk,hka,hkt⟩ := exists_transvection_of_mem_line_radical ha ht ht1
  obtain ⟨b,hfb,hkb⟩ := common_one hf hk
  let c := transvection b (f+k) (by simp [hfb,hkb]; decide)
  have hca : c a = a := by simp [c,transvection,hfa,hka]
  have hkc (u : V) : k (c u) = f u := by
    change k (u + (f+k) u • b) = f u
    simp only [map_add,map_smul,LinearMap.add_apply,hkb,smul_eq_mul,mul_one]
    have hh : k u + k u = 0 := (by decide : ∀ r : ZMod 2, r+r=0) _
    calc
      k u + (f u + k u) = f u + (k u + k u) := by abel
      _ = f u := by rw [hh,add_zero]
  refine ⟨c,hca,mul_inv_eq_iff_eq_mul.mpr ?_⟩
  ext u
  change c (u + f u • a) = t (c u)
  rw [map_add,map_smul,hca,hkt,hkc]

/-- Every point-fixed Sylow contains the full radical of that point. -/
theorem le_sylow_of_fixes (S : Sylow 2 (BinaryLinear.GL V)) (a : V)
    (ha : ∀ s ∈ S, s a = a) : radical (Submodule.span (ZMod 2) {a}) ≤ S := by
  let L := Submodule.span (ZMod 2) {a}
  have hSP : (S : Subgroup (BinaryLinear.GL V)) ≤ parabolic L := by
    intro s hs w
    constructor
    · intro hw
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
      exact Submodule.mem_span_singleton.mpr ⟨r, s.injective (by
        rw [map_smul,ha s hs]
        exact hr)⟩
    · intro hw
      obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul,ha s hs]
      exact L.smul_mem _ (Submodule.mem_span_singleton_self a)
  have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (radical_two L)
    (hSP.trans (parabolic_le_normalizer L))) le_sup_left
  exact he ▸ le_sup_right

/-- The root radical is elementary, without choosing coordinates. -/
theorem elementary (a : V) : IsElementaryAbelian 2 (radical (Submodule.span (ZMod 2) {a})) :=
  elementaryAbelian_of_le_radical (radical (Submodule.span (ZMod 2) {a})).subtype
    Subtype.val_injective _ (fun x => x.property)

/-- The order of the literal common-center radical. -/
theorem card [FiniteDimensional (ZMod 2) V] (a : V) (ha : a ≠ 0) :
    Nat.card (radical (Submodule.span (ZMod 2) {a})) = 2 ^ (finrank (ZMod 2) V - 1) := by
  have hR : rootGroup (⊤ : Subgroup (BinaryLinear.GL V)) a =
      radical (Submodule.span (ZMod 2) {a}) := by simp [rootGroup,centerLine]
  have hF : rootForms (⊤ : Subgroup (BinaryLinear.GL V)) a =
      (Submodule.span (ZMod 2) {a}).dualAnnihilator := by
    ext f
    exact ⟨fun hf => (mem_line_annihilator a f).mpr hf.1,
      fun hf => ⟨(mem_line_annihilator a f).mp hf, Subgroup.mem_top _⟩⟩
  rw [← hR, ← rootForms_card_eq _ ha, hF, Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  congr 1
  have he := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span (ZMod 2) {a})
  rw [finrank_span_singleton ha] at he
  omega

/-- A full common-center radical in dimension at least three contains a four-group. -/
theorem exists_four [FiniteDimensional (ZMod 2) V] (a : V) (ha : a ≠ 0)
    (hd : 3 ≤ finrank (ZMod 2) V) :
    ∃ E : Subgroup (BinaryLinear.GL V), E ≤ radical (Submodule.span (ZMod 2) {a}) ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  let R := radical (Submodule.span (ZMod 2) {a})
  let : IsElementaryAbelian 2 R := elementary a
  have hc : 2^2 ≤ Nat.card R := by
    rw [card a ha]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨E,hE⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (by decide : Nat.Prime 2)
    (IsElementaryAbelian.isPGroup 2 R) hc
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective E.subtype E.subtype_injective
  refine ⟨E.map R.subtype, map_subtype_le _, ?_, ?_⟩
  · exact IsElementaryAbelian.of_injective
      (E.equivMapOfInjective R.subtype R.subtype_injective).symm.toMonoidHom
      (E.equivMapOfInjective R.subtype R.subtype_injective).symm.injective
  · rw [Subgroup.card_map_of_injective R.subtype_injective,hE]
    decide

/-- Each nonidentity common-center root fixes exactly the center annihilator
in the contragredient module. -/
theorem dual_fixed_iff (a : V) (ha : a ≠ 0) {t : BinaryLinear.GL V}
    (ht : t ∈ radical (Submodule.span (ZMod 2) {a})) (ht1 : t ≠ 1)
    (l : Module.Dual (ZMod 2) V) : t.symm.dualMap l = l ↔ l a = 0 := by
  obtain ⟨f,hf,hfa,he⟩ := exists_transvection_of_mem_line_radical ha ht ht1
  have heq : t = transvection a f hfa := LinearEquiv.ext he
  rw [heq]
  constructor
  · intro hl
    obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
    have hh := congrArg (fun q : Module.Dual (ZMod 2) V => q b) hl
    change l (b + f b • a) = l b at hh
    rw [hb,one_smul,map_add] at hh
    exact add_eq_left.mp hh
  · intro hl
    ext b
    change l (b + f b • a) = l b
    rw [map_add,map_smul,hl,smul_zero,add_zero]

end BinaryLinear.LineRadical
