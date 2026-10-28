module

public import CFSG.Quasithin.ChapterK.Section01To04.Preliminaries
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Field involutions in the K.4.5 module

For a Frobenius-semilinear involution over F₄, its displacement image equals
its fixed space: if w is fixed and c²-c=1, the displacement of c w is w.
Rank-nullity then gives fixed dimension six in binary dimension twelve.
The argument requires the actual semilinear action, not an assumed dimension.
Source: Aschbacher–Smith, K.4.5, printed p.460, first paragraph.
-/

public section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Representation Representation.BinaryOffender

variable {K G U : Type*} [Field K] [Group G]
  [AddCommGroup U] [Module K U] [Module (ZMod 2) U]

/-- A Frobenius-semilinear involution has coincident displacement and fixed spaces. -/
theorem field_involution_range_eq_fixed (ρ : Representation (ZMod 2) G U)
    (i : G) (hi : i ^ 2 = 1) (c : K) (hc : c ^ 2 - c = 1)
    (hsemi : ∀ (r : K) (v : U), ρ i (r • v) = r ^ 2 • ρ i v) :
    LinearMap.range (ρ i - LinearMap.id) = fixedSpace ρ (Subgroup.zpowers i) := by
  have hii (v : U) : ρ i (ρ i v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hi, map_one, Module.End.one_apply]
  have hneg (v : U) : -v = v := by
    have hv : v + v = 0 := by
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun r : ZMod 2 => r • v) (by decide : (1 : ZMod 2) + 1 = 0)
    exact neg_eq_of_add_eq_zero_left hv
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    change ρ i (ρ i v - v) = ρ i v - v
    rw [map_sub, hii]
    simp only [sub_eq_add_neg, hneg, add_comm]
  · intro v hv
    have hfix := (mem_fixedSpace_zpowers_iff ρ i v).mp hv
    refine ⟨c • v, ?_⟩
    change ρ i (c • v) - c • v = v
    rw [hsemi, hfix, ← sub_smul, hc, one_smul]

/-- Both halves have binary dimension six; neither dimension is assumed. -/
theorem field_involution_dimensions [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) G U) (hdim : Module.finrank (ZMod 2) U = 12)
    (i : G) (hi : i ^ 2 = 1) (c : K) (hc : c ^ 2 - c = 1)
    (hsemi : ∀ (r : K) (v : U), ρ i (r • v) = r ^ 2 • ρ i v) :
    fixedCodim ρ (Subgroup.zpowers i) = 6 ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers i)) = 6 := by
  have hr := field_involution_range_eq_fixed ρ i hi c hc hsemi
  have he := fixedCodim_zpowers_eq_displacement_rank ρ i
  rw [hr] at he
  have hd := fixedCodim_add_finrank ρ (Subgroup.zpowers i)
  omega

/-- The common fixed space of a semilinear actor and a linear actor
has at most half the dimension of the latter's fixed space. The injection
sends (x,y) to x + c y; applying the field actor proves injectivity. -/
theorem common_fixed_finrank_bound [FiniteDimensional (ZMod 2) U]
    [SMulCommClass (ZMod 2) K U]
    (ρ : Representation (ZMod 2) G U) (A : Subgroup G)
    (i : G) (hiA : i ∈ A) (a : G) (haA : a ∈ A)
    (c : K) (hc : c ^ 2 - c = 1)
    (hsemi : ∀ (r : K) (v : U), ρ i (r • v) = r ^ 2 • ρ i v)
    (hlinear : ∀ (r : K) (v : U), ρ a (r • v) = r • ρ a v) :
    2 * Module.finrank (ZMod 2) (fixedSpace ρ A) ≤
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) := by
  let C := fixedSpace ρ A
  let F := fixedSpace ρ (Subgroup.zpowers a)
  let f : C × C →ₗ[ZMod 2] F :=
    { toFun := fun p => ⟨p.1.val + c • p.2.val, by
        apply (mem_fixedSpace_zpowers_iff ρ a _).mpr
        have hx : ρ a p.1.val = p.1.val := p.1.property ⟨a, haA⟩
        have hy : ρ a p.2.val = p.2.val := p.2.property ⟨a, haA⟩
        rw [map_add, hlinear, hx, hy]⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        change (p.1.val + q.1.val) + c • (p.2.val + q.2.val) =
          (p.1.val + c • p.2.val) + (q.1.val + c • q.2.val)
        simp only [smul_add, add_add_add_comm]
      map_smul' := by
        intro r p
        apply Subtype.ext
        change r • p.1.val + c • (r • p.2.val) = r • (p.1.val + c • p.2.val)
        rw [smul_add, smul_comm r c] }
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x, y⟩ h
    have hxy : x.val + c • y.val = 0 := congrArg Subtype.val h
    have hxy' := congrArg (ρ i) hxy
    have hxi : ρ i x.val = x.val := x.property ⟨i, hiA⟩
    have hyi : ρ i y.val = y.val := y.property ⟨i, hiA⟩
    rw [map_add, hsemi, hxi, hyi, map_zero] at hxy'
    have hy : y.val = 0 := by
      have he : c ^ 2 • y.val = c • y.val := add_left_cancel (hxy'.trans hxy.symm)
      have hh : (c ^ 2 - c) • y.val = 0 := by rw [sub_smul, he, sub_self]
      simpa only [hc, one_smul] using hh
    have hx : x.val = 0 := by simpa only [hy, smul_zero, add_zero] using hxy
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_prod, ← two_mul] using hdim

/-- The common fixed-space bound gives codimension at least eight in binary
dimension twelve as soon as the inner involution displaces at least four. -/
theorem outer_actor_codim_bound [FiniteDimensional (ZMod 2) U]
    [SMulCommClass (ZMod 2) K U]
    (ρ : Representation (ZMod 2) G U) (hdim : Module.finrank (ZMod 2) U = 12)
    (A : Subgroup G) (i : G) (hiA : i ∈ A) (a : G) (haA : a ∈ A)
    (ha : 4 ≤ fixedCodim ρ (Subgroup.zpowers a))
    (c : K) (hc : c ^ 2 - c = 1)
    (hsemi : ∀ (r : K) (v : U), ρ i (r • v) = r ^ 2 • ρ i v)
    (hlinear : ∀ (r : K) (v : U), ρ a (r • v) = r • ρ a v) :
    8 ≤ fixedCodim ρ A := by
  have h := common_fixed_finrank_bound ρ A i hiA a haA c hc hsemi hlinear
  have hA := fixedCodim_add_finrank ρ A
  have ha' := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  omega

end CFSG.Quasithin.ChapterK.JankoTwo
