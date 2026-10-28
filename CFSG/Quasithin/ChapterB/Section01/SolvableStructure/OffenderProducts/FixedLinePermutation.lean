module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedLines
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.NaturalModels

/-!
# Fixed lines detect their natural factors

Ambient conjugation transports a factor support and its actor-fixed part
simultaneously. If the actor moves a factor, its common fixed space meets
that factor support trivially. An element normalizing the actor fixes the
nonzero vector of an order-two fixed line exactly when it normalizes the
corresponding factor.

This supplies the point/factor stabilizer comparison for the literal
Baumann fixed lines in Aschbacher–Smith 13.2.11(3)–(4), printed p.881.
The original centralizer-quotient application is in
`Chapter13/Section02/A5Outside/FixedLineCentralizers`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (c : SolvableFFFactors ρ)

theorem support_disjoint_fixedSpace_of_factor_moved
    (A : Subgroup G) (i : Fin c.count) (g : A)
    (hg : c.factorConjugation (g : G) i ≠ i) :
    Disjoint (subspaceCommutator ρ ⊤ (c.factor i)) (fixedSpace ρ A) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hfix
  have hmove := c.action_mem_factor_support (g : G) i hv
  have hfg : ρ (g : G) v = v := hfix g
  rw [hfg] at hmove
  exact Submodule.disjoint_def.mp (c.supports_independent.pairwiseDisjoint hg.symm)
    v hv hmove

theorem factorFixedSpace_disjoint_fixedSpace_of_factor_moved
    (A B : Subgroup G) (i : Fin c.count) (g : B)
    (hg : c.factorConjugation (g : G) i ≠ i) :
    Disjoint (c.factorFixedSpace A i) (fixedSpace ρ B) :=
  (c.support_disjoint_fixedSpace_of_factor_moved B i g hg).mono_left inf_le_left

theorem factorFixedSpace_map_conj (A : Subgroup G) (g : G) (i : Fin c.count) :
    (c.factorFixedSpace A i).map (ρ g) =
      c.factorFixedSpace (A.map (MulAut.conj g).toMonoidHom)
        (c.factorConjugation g i) := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨c.action_mem_factor_support g i hw.1,?_⟩
    intro b
    obtain ⟨a,ha,hab⟩ := b.property
    have hwa : ρ a w = w := hw.2 ⟨a,ha⟩
    change ρ (b : G) (ρ g w) = ρ g w
    rw [← hab]
    change ρ (g * a * g⁻¹) (ρ g w) = _
    rw [map_mul,map_mul]
    simpa only [Module.End.mul_apply,hinv] using congrArg (ρ g) hwa
  · intro hv
    refine ⟨ρ g⁻¹ v,⟨?_,?_⟩,hginv v⟩
    · simpa using c.action_mem_factor_support g⁻¹ (c.factorConjugation g i) hv.1
    · intro a
      have hvf : ρ (g * (a : G) * g⁻¹) v = v :=
        hv.2 ⟨g * (a : G) * g⁻¹,⟨a,a.property,rfl⟩⟩
      have hh := congrArg (ρ g⁻¹) hvf
      rw [map_mul,map_mul] at hh
      change ρ (a : G) (ρ g⁻¹ v) = ρ g⁻¹ v
      simpa only [Module.End.mul_apply,hinv] using hh
theorem factorFixedSpace_map_of_normalizes (A : Subgroup G) (g : G)
    (hg : g ∈ normalizer (A : Set G)) (i : Fin c.count) :
    (c.factorFixedSpace A i).map (ρ g) =
      c.factorFixedSpace A (c.factorConjugation g i) := by
  have hn : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [c.factorFixedSpace_map_conj,hn]

theorem factorFixedSpace_fixed_iff (A : Subgroup G) (g : G)
    (hg : g ∈ normalizer (A : Set G)) (i : Fin c.count)
    (hcard : Nat.card (c.factorFixedSpace A i) = 2)
    (v : V) (hv : v ∈ c.factorFixedSpace A i) (hv0 : v ≠ 0) :
    ρ g v = v ↔ c.factorConjugation g i = i := by
  constructor
  · intro hfix
    by_contra hmove
    have hw := c.action_mem_factor_support g i hv.1
    rw [hfix] at hw
    exact hv0 (Submodule.disjoint_def.mp
      (c.supports_independent.pairwiseDisjoint (Ne.symm hmove)) v hv.1 hw)
  · intro hfix
    have hmap := c.factorFixedSpace_map_of_normalizes A g hg i
    rw [hfix] at hmap
    have hgv : ρ g v ∈ c.factorFixedSpace A i :=
      hmap ▸ Submodule.mem_map_of_mem hv
    have hgv0 : ρ g v ≠ 0 := by
      intro he
      have hh := congrArg (ρ g⁻¹) he
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] at hh
      exact hv0 hh
    exact congrArg Subtype.val (((Nat.card_eq_two_iff' (0 : c.factorFixedSpace A i)).mp
      hcard).unique
        (show (⟨ρ g v,hgv⟩ : c.factorFixedSpace A i) ≠ 0 from
          fun he => hgv0 (congrArg Subtype.val he))
        (show (⟨v,hv⟩ : c.factorFixedSpace A i) ≠ 0 from
          fun he => hv0 (congrArg Subtype.val he)))

theorem factorFixedSpace_fixed_iff_normalizes_factor
    (A : Subgroup G) (g : G) (hg : g ∈ normalizer (A : Set G))
    (i : Fin c.count) (hcard : Nat.card (c.factorFixedSpace A i) = 2)
    (v : V) (hv : v ∈ c.factorFixedSpace A i) (hv0 : v ≠ 0) :
    ρ g v = v ↔ g ∈ normalizer (c.factor i : Set G) := by
  rw [c.factorFixedSpace_fixed_iff A g hg i hcard v hv hv0]
  constructor
  · intro hi
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (c.factor i).map (MulAut.conj g).toMonoidHom = c.factor i
    rw [c.factor_map_conj,hi]
  · intro hi
    apply c.factor_injective
    rw [← c.factor_map_conj]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hi

end CFSG.Quasithin.ChapterB.SolvableFFFactors
