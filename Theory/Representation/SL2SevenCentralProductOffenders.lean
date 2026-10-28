module

public import Theory.Representation.BinaryOffender.TimmesfeldCentralizer
public import Theory.Representation.BinaryOffender.DisplacementFaithfulness
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SL2SevenCentralProductOffenders.GroupBounds
public import Theory.Representation.SL2SevenCentralProductOffenders.DimensionBound

/-!
# Best offenders in faithful SL₂(7) central-product actions

The general reductions here handle elementary actors with coordinates in both
commuting factors. For a faithful binary action with `[L,A] = L` and
`[V,L] = V`, Timmesfeld replacement gives a nontrivial best offender inside A
that meets every subgroup of `C_H(L)` trivially. Thus replacement preserves
an image outside a commuting factor; this is proved, not assumed.

If such disjoint elementary actors have rank at most two, their individual
elements have displacement rank at most two. If three conjugates of a
nonidentity element generate a subgroup containing L, their displacement
spaces span V, giving `dim V ≤ 6`. A lower bound `7 ≤ dim V` then excludes
the original best offender. The supporting modules prove the group-generation,
elementary-rank and lower-dimension statements for the literal SL₂(7).
The final theorem discharges these premises and places every best offender
in the two-core, using only the faithful action, commuting-factor generation,
exact central overlap and full commutator generation.

Source motivation: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.31–34, printed pp.135–137, and B.2.3–5, printed pp.75–76. Replacement
uses GLS, vol.2, Theorem 26.23(i); the displacement-centralizer argument is
the linear step of Theorem 26.24, Step 3. These reductions do not assume a
pushing-up theorem or a catalogue of modules.
-/

public section

namespace Representation.BinaryOffender.SL2SevenCentralProduct
open Subgroup
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V)

private theorem span_component_displacements (L : Subgroup H) :
    Submodule.span (ZMod 2) (Set.range fun lv : L × V => ρ lv.1 lv.2 - lv.2) =
      subspaceCommutator ρ ⊤ L := by
  congr 1
  ext v
  constructor
  · rintro ⟨⟨l, w⟩, rfl⟩
    exact ⟨l, l.property, w, Submodule.mem_top, rfl⟩
  · rintro ⟨l, hl, w, _, rfl⟩
    exact ⟨(⟨l, hl⟩, w), rfl⟩

variable [FiniteDimensional (ZMod 2) V]

/-- If three conjugates generate a subgroup containing L, and L generates V
by displacements, V has dimension at most three times the displacement rank
of the original element. No semisimplicity is needed. -/
theorem finrank_le_three_mul_fixedCodim_of_three_conjugates
    (L : Subgroup H) (hV : subspaceCommutator ρ ⊤ L = ⊤)
    (a g h : H)
    (hgen : L ≤ zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹)) :
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers a) := by
  let U := LinearMap.range (ρ a - LinearMap.id)
  let W := LinearMap.range (ρ (g * a * g⁻¹) - LinearMap.id)
  let X := LinearMap.range (ρ (h * a * h⁻¹) - LinearMap.id)
  let S := U ⊔ W ⊔ X
  let D : Subgroup H := {
    carrier := {b | ∀ v : V, ρ b v - v ∈ S}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro b c hb hc v
      have he : ρ (b * c) v - v = (ρ b (ρ c v) - ρ c v) + (ρ c v - v) := by
        rw [map_mul, Module.End.mul_apply]
        abel
      rw [he]
      exact S.add_mem (hb (ρ c v)) (hc v)
    inv_mem' := by
      intro b hb v
      have he : ρ b (ρ b⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have hh := S.neg_mem (hb (ρ b⁻¹ v))
      simpa only [he, neg_sub] using hh }
  have haD : zpowers a ≤ D := by
    apply zpowers_le.mpr
    intro v
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (show ρ a v - v ∈ U from ⟨v, rfl⟩))
  have hgD : zpowers (g * a * g⁻¹) ≤ D := by
    apply zpowers_le.mpr
    intro v
    exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (show ρ (g * a * g⁻¹) v - v ∈ W from ⟨v, rfl⟩))
  have hhD : zpowers (h * a * h⁻¹) ≤ D := by
    apply zpowers_le.mpr
    intro v
    exact Submodule.mem_sup_right (show ρ (h * a * h⁻¹) v - v ∈ X from ⟨v, rfl⟩)
  have hLD := hgen.trans (sup_le (sup_le haD hgD) hhD)
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hV]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, v, _, rfl⟩
    exact hLD hl v
  have hUW := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hUWX := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ W) X
  have hdS : Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) V := by
    rw [hS]
    exact finrank_top (ZMod 2) V
  have hdU : Module.finrank (ZMod 2) U = fixedCodim ρ (zpowers a) :=
    (fixedCodim_zpowers_eq_displacement_rank ρ a).symm
  have hdW : Module.finrank (ZMod 2) W = fixedCodim ρ (zpowers a) := by
    rw [← fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_conj]
  have hdX : Module.finrank (ZMod 2) X = fixedCodim ρ (zpowers a) := by
    rw [← fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_conj]
  change Module.finrank (ZMod 2) (U ⊔ W ⊔ X : Submodule (ZMod 2) V) = _ at hdS
  omega

variable [Finite H]

/-- Replacement retains a nontrivial best offender disjoint from a commuting
factor whenever the original actor generates the whole L by commutators. -/
theorem exists_disjoint_bestOffender
    (hρ : Function.Injective ρ) (P L A : Subgroup H)
    (hPL : P ≤ centralizer (L : Set H)) (hLA : ⁅L, A⁆ = L)
    (hV : subspaceCommutator ρ ⊤ L = ⊤) (hA : IsBestOffender ρ A) :
    ∃ B ≤ A, IsBestOffender ρ B ∧ IsQuadratic ρ B ∧ B ⊓ P = ⊥ := by
  refine ⟨displacementCentralizer ρ A, displacementCentralizer_le ρ A,
    hA.displacementCentralizer_isBestOffender ρ,
    displacementCentralizer_isQuadratic ρ A, ?_⟩
  apply le_bot_iff.mp
  have hc := displacementCentralizer_inf_centralizer_eq_bot ρ hρ hLA
    ((span_component_displacements ρ L).trans hV)
  exact (inf_le_inf_left _ hPL).trans hc.le

/-- Reduce offender containment to group-theoretic rank and generation bounds
and a lower dimension bound. All three bounds must be supplied in an
application to a particular central product. -/
theorem bestOffender_le_of_rank_two_three_conjugates
    (hρ : Function.Injective ρ) (P L : Subgroup H)
    (hPL : P ≤ centralizer (L : Set H))
    (hLA : ∀ A : Subgroup H, IsElementaryTwo A → ¬ A ≤ P → ⁅L, A⁆ = L)
    (hrank : ∀ B : Subgroup H, IsElementaryTwo B → B ⊓ P = ⊥ → rank B ≤ 2)
    (hgen : ∀ a : H, a ^ 2 = 1 → a ∉ P →
      ∃ g h : H, L ≤ zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹))
    (hV : subspaceCommutator ρ ⊤ L = ⊤)
    (hdim : 7 ≤ Module.finrank (ZMod 2) V)
    (A : Subgroup H) (hA : IsBestOffender ρ A) : A ≤ P := by
  by_contra hn
  obtain ⟨B, _, hB, _, hBP⟩ := exists_disjoint_bestOffender ρ hρ P L A hPL
    (hLA A hA.1 hn) hV hA
  obtain ⟨⟨a, ha⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1.1
  have ha1 : a ≠ 1 := fun he => ha1' (Subtype.ext he)
  have haP : a ∉ P := by
    intro haP
    exact ha1 (Subgroup.mem_bot.mp (hBP.le ⟨ha, haP⟩))
  let _ := hB.1.2
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  obtain ⟨g, h, hgh⟩ := hgen a ha2 haP
  have hupper := finrank_le_three_mul_fixedCodim_of_three_conjugates ρ L hV a g h hgh
  have hfix : fixedSpace ρ B ≤ fixedSpace ρ (zpowers a) :=
    fixedSpace_antitone ρ (zpowers_le.mpr ha)
  have hdle := Submodule.finrank_mono hfix
  have hdB := fixedCodim_add_finrank ρ B
  have hda := fixedCodim_add_finrank ρ (zpowers a)
  have hcod := (hB.isOffender ρ).2
  have hr := hrank B hB.1 hBP
  omega

end Representation.BinaryOffender.SL2SevenCentralProduct

namespace Representation.BinaryOffender
open Subgroup SL2SevenCentralProduct
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- In a faithful full binary action of a central product of the two-core
with SL₂(7), every best offender lies in the two-core. This includes elementary
actors with nontrivial coordinates in both commuting factors. -/
theorem bestOffender_le_twoCore_of_SL2Seven
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (f : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) →* H)
    (hf : Function.Injective f)
    (hc : ⁅pCore 2 H, f.range⁆ = ⊥)
    (hs : pCore 2 H ⊔ f.range = ⊤)
    (hz : (pCore 2 H).comap f =
      center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)))
    (hV : subspaceCommutator ρ ⊤ f.range = ⊤)
    (A : Subgroup H) (hA : IsBestOffender ρ A) : A ≤ pCore 2 H := by
  have hfull : subspaceCommutator (ρ.comp f) ⊤ ⊤ = ⊤ := by
    apply top_unique
    calc
      ⊤ = subspaceCommutator ρ ⊤ f.range := hV.symm
      _ ≤ subspaceCommutator (ρ.comp f) ⊤ ⊤ := by
        apply Submodule.span_le.mpr
        rintro _ ⟨_, ⟨s, rfl⟩, v, hv, rfl⟩
        exact Submodule.subset_span ⟨s, Subgroup.mem_top s, v, hv, rfl⟩
  apply bestOffender_le_of_rank_two_three_conjugates ρ hρ (pCore 2 H) f.range
    (commutator_eq_bot_iff_le_centralizer.mp hc) ?_ ?_ ?_ hV
    (seven_le_finrank_of_faithful_full (ρ.comp f) (hρ.comp hf) hfull) A hA
  · intro B _ hB
    exact commutator_range_eq f hf hc hs hz B hB
  · intro B hB hBP
    let _ := hB.2
    exact elementary_rank_le_two f hs hz B hBP
  · exact three_conjugates_range_le f hc hs hz

end Representation.BinaryOffender
