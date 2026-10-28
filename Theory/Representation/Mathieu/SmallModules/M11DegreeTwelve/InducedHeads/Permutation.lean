module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Invariants

/-!
# Simple quotients of twelve-point binary permutation modules

The constant line lies in the augmentation hyperplane in even degree.
A simple quotient of dimension greater than one is already a quotient of
that hyperplane and kills its constant line, so its dimension is at most ten.
An orbit map applies this bound to a vector fixed by an index-twelve subgroup.
This is the permutation-module step in the M11 degree gap used in
Aschbacher--Smith K.4, printed p.457; James, J. Algebra 27 (1973), 57--111.
-/

public noncomputable section
namespace Representation.MathieuSmall.M11DegreeTwelve.InducedHeads
open BinaryPermutation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem permutation_quotient_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (φ : G →* Equiv.Perm Ω) (hc : Fintype.card Ω = 12)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hd : 1 < Module.finrank (ZMod 2) V)
    (f : IntertwiningMap ((representation Ω).comp φ) ρ) (hf : f ≠ 0) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  let α := (representation Ω).comp φ
  let C : Subrepresentation α := ⟨core Ω, fun g _ hv => core_invariant Ω (φ g) hv⟩
  let L : Subrepresentation α :=
    ⟨constants Ω, fun g _ hv => constants_invariant Ω (φ g) hv⟩
  let iC : C.toRepresentation.IntertwiningMap α := ⟨C.toSubmodule.subtype, fun _ => rfl⟩
  let iL : L.toRepresentation.IntertwiningMap α := ⟨L.toSubmodule.subtype, fun _ => rfl⟩
  have hs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hr := f.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  have hCdim : Module.finrank (ZMod 2) C.toSubmodule = 11 := by
    exact (finrank_core Ω).trans (by rw [hc])
  have hAdim : Module.finrank (ZMod 2) (Full Ω) = 12 := (finrank_full Ω).trans hc
  have hfc : f.comp iC ≠ 0 := by
    intro hz
    have hk : C.toSubmodule ≤ f.toLinearMap.ker := by
      intro v hv
      exact congrArg (fun t : C.toRepresentation.IntertwiningMap ρ => t ⟨v, hv⟩) hz
    have := Submodule.finrank_mono hk
    omega
  have hfl : f.comp iL = 0 := by
    rcases IsIrreducible.surjective_or_eq_zero (f.comp iL) with h | h
    · have := LinearMap.finrank_le_finrank_of_surjective h
      have hLdim : Module.finrank (ZMod 2) L.toSubmodule = 1 := finrank_constants Ω
      omega
    · exact h
  have hLC : L.toSubmodule ≤ C.toSubmodule :=
    (constants_le_core_iff Ω).mpr (by rw [hc]; decide)
  have hk : L.toSubmodule.comap C.toSubmodule.subtype ≤
      (f.comp iC).toLinearMap.ker := by
    intro v hv
    exact congrArg (fun t : L.toRepresentation.IntertwiningMap ρ => t ⟨v.val, hv⟩) hfl
  have hkdim := Submodule.finrank_mono hk
  rw [(Submodule.comapSubtypeEquivOfLe hLC).finrank_eq, finrank_constants] at hkdim
  have hrC := (f.comp iC).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    ((IsIrreducible.surjective_or_eq_zero (f.comp iC)).resolve_right hfc), finrank_top] at hrC
  omega

/-- A nontrivial simple binary module with a vector fixed by an index-twelve
subgroup has dimension at most ten. The subgroup need not be normal. -/
theorem finrank_le_ten_of_index_twelve_fixed [Finite G]
    (K : Subgroup G) (hK : K.index = 12)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hd : 1 < Module.finrank (ZMod 2) V)
    (hfixed : invariants (ρ.comp K.subtype) ≠ ⊥) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  classical
  let Ω := G ⧸ K
  let : Fintype Ω := Fintype.ofFinite Ω
  let φ := MulAction.toPermHom G Ω
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  let value (q : Ω) : V := ρ q.out v
  have hvalue (g : G) (q : Ω) (hg : (g : G ⧸ K) = q) : value q = ρ g v := by
    have hm : q.out⁻¹ * g ∈ K := QuotientGroup.eq.mp (Quotient.out_eq q |>.trans hg.symm)
    have hh := hv ⟨q.out⁻¹ * g, hm⟩
    change ρ (q.out⁻¹ * g) v = v at hh
    have he := congrArg (ρ q.out) hh
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value ((1 : G) : Ω) = v := by
    simpa only [map_one, Module.End.one_apply] using hvalue 1 _ rfl
  have hvalue_act (g : G) (q : Ω) : value (g • q) = ρ g (value q) := by
    rw [hvalue (g * q.out) _ (MulAction.Quotient.coe_smul_out K g q), map_mul]
    rfl
  let f : IntertwiningMap ((representation Ω).comp φ) ρ := {
    toLinearMap := {
      toFun a := ∑ i : Ω, a i • value i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Ω, a ((φ g).symm i) • value i) = ρ g (∑ i : Ω, a i • value i)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp (φ g)
        (fun i => a ((φ g).symm i) • value i)).symm.trans (by
          simp only [_root_.Equiv.symm_apply_apply]; rfl) }
  apply permutation_quotient_bound φ (by
    change Fintype.card (G ⧸ K) = 12
    rw [← Nat.card_eq_fintype_card]
    exact hK) ρ hd f
  intro hz
  have he := congrArg (fun t : IntertwiningMap ((representation Ω).comp φ) ρ =>
    t (Pi.single ((1 : G) : Ω) 1)) hz
  have hf : f (Pi.single ((1 : G) : Ω) 1) = v := by
    change (∑ i : Ω, (Pi.single ((1 : G) : Ω) (1 : ZMod 2) : Ω → ZMod 2) i • value i) = v
    simp [hvalue_o]
  exact hv0 (hf.symm.trans he)

end Representation.MathieuSmall.M11DegreeTwelve.InducedHeads
