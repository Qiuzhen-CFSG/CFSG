module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# A fixed-space family from uniform fixed spaces outside a small subgroup

Let an elementary abelian group A act through a homomorphism f. If all
actors outside C have the same fixed space as f(A), then every subgroup
of f(A) whose inverse image cannot fit in C has that same fixed space.
An index bound |A:C|≥2^j supplies precisely the j-th fixed-space family.

This is the index argument after (*) in Aschbacher–Smith 10.2.12,
printed pp.754–755. It retains the literal action image and allows C to
contain the action kernel; no faithfulness of the original actor is assumed.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
variable {A X W : Type*} [Group A] [Finite A] [Group X]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Uniform fixed spaces outside an index-2^j subgroup give an actual A_j member. -/
theorem range_mem_fixedSpaceFamily_of_uniform_outside
    [IsElementaryAbelian 2 A] (ρ : Representation (ZMod 2) X W)
    (f : A →* X) (hf : f ≠ 1) (C : Subgroup A) {j : ℕ}
    (hj : 0 < j) (hC : 2 ^ j ≤ C.index)
    (hfix : ∀ a : A, a ∉ C →
      fixedSpace ρ f.range = fixedSpace ρ (zpowers (f a))) :
    f.range ∈ fixedSpaceFamily ρ j := by
  refine ⟨hj,⟨?_,IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective⟩,?_⟩
  · intro he
    apply hf
    ext a
    exact mem_bot.mp (he ▸ (show f a ∈ f.range from ⟨a,rfl⟩))
  · intro B hB hidx
    have hsmall : (B.comap f).index < 2 ^ j := by
      rw [index_comap]
      exact Nat.lt_pow_of_log_lt (by decide) hidx
    have hn : ¬ B.comap f ≤ C := by
      intro hle
      have hpos : 0 < (B.comap f).index := Nat.card_pos
      have hh := Nat.le_of_dvd hpos (index_dvd_of_le hle)
      omega
    obtain ⟨a,ha,hac⟩ := Set.not_subset.mp hn
    apply le_antisymm (fixedSpace_antitone ρ hB)
    rw [hfix a hac]
    exact fixedSpace_antitone ρ (zpowers_le.mpr ha)

/-- The ambient centralizer form of the same criterion, on the literal automizer. -/
theorem inducedAutomizer_mem_fixedSpaceFamily_of_uniform_outside
    {G : Type*} [Group G] [Finite G] (V A C : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (V : Set G)) (hn : ¬ A ≤ centralizer (V : Set G))
    {j : ℕ} (hj : 0 < j) (hC : 2 ^ j ≤ C.relIndex A)
    (hfix : ∀ a ∈ A, a ∉ C → V ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) :
    inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) j := by
  let f : A →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hAN)
  have hf : f.range = inducedAutomizer V A := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hfn : f ≠ 1 := by
    intro he
    apply hn
    apply (inducedAutomizer_eq_bot_iff hAN).mp
    rw [← hf,he]
    exact MonoidHom.range_one
  rw [← hf]
  apply range_mem_fixedSpaceFamily_of_uniform_outside (automizerRepresentation V)
    f hfn (C.subgroupOf A) hj hC
  intro a hac
  apply le_antisymm (fixedSpace_antitone (automizerRepresentation V)
    (show zpowers (f a) ≤ f.range from zpowers_le.mpr ⟨a,rfl⟩))
  intro v hv
  rw [hf]
  apply (mem_fixedSpace_inducedAutomizer V A hAN v).mpr
  apply hfix a a.property hac
  refine ⟨v.toMul.property,?_⟩
  have he := (mem_fixedSpace_zpowers_iff (automizerRepresentation V) (f a) v).mp hv
  have hh := congrArg (fun w : Additive V => (w.toMul : G)) he
  change (a : G) * (v.toMul : G) * (a : G)⁻¹ = (v.toMul : G) at hh
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The same lower bound inside the image of a specified ambient actor M. -/
theorem moduleA_localAutomizer_ge_of_uniform_outside
    {G : Type*} [Group G] [Finite G] (V A C M : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (V : Set G)) (hAM : A ≤ M)
    (hn : ¬ A ≤ centralizer (V : Set G))
    {j : ℕ} (hj : 0 < j) (hC : 2 ^ j ≤ C.relIndex A)
    (hfix : ∀ a ∈ A, a ∉ C → V ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) :
    (j : ℕ∞) ≤ moduleA ((automizerRepresentation V).comp (inducedAutomizer V M).subtype) := by
  let H := inducedAutomizer V M
  let f₀ : A →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hAN)
  let f : A →* H := f₀.codRestrict H (fun a => ⟨⟨a,hAN a.property⟩,hAM a.property,rfl⟩)
  let ρ := (automizerRepresentation V).comp H.subtype
  have hfn : f ≠ 1 := by
    intro he
    apply hn
    intro a ha v hv
    have hh := congrArg (fun k : H => ((k : Automizer V) : MulAut V) ⟨v,hv⟩)
      (congrArg (fun k : A →* H => k ⟨a,ha⟩) he)
    have hh' := congrArg (fun w : V => (w : G)) hh
    change a * v * a⁻¹ = v at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  apply le_moduleA_of_mem ρ
  apply range_mem_fixedSpaceFamily_of_uniform_outside ρ f hfn (C.subgroupOf A) hj hC
  intro a hac
  apply le_antisymm (fixedSpace_antitone ρ
    (show zpowers (f a) ≤ f.range from zpowers_le.mpr ⟨a,rfl⟩))
  intro v hv b
  obtain ⟨d,hd⟩ := b.property
  have he := (mem_fixedSpace_zpowers_iff ρ (f a) v).mp hv
  have hh := congrArg (fun w : Additive V => (w.toMul : G)) he
  change (a : G) * (v.toMul : G) * (a : G)⁻¹ = (v.toMul : G) at hh
  have hvc : (v.toMul : G) ∈ centralizer (A : Set G) :=
    hfix a a.property hac ⟨v.toMul.property,
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
  change ρ (b : H) v = v
  rw [← hd]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change (d : G) * (v.toMul : G) * (d : G)⁻¹ = (v.toMul : G)
  rw [hvc d d.property, mul_inv_cancel_right]

end CFSG.Quasithin.ChapterE
