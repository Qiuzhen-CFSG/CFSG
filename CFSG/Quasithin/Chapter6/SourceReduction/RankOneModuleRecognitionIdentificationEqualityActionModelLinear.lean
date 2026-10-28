module
public import Theory.SpecificGroups.BinaryLinear.LineRadical

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionModelNormalizers

/-!
# Excluding the larger binary-linear equality models

The source-line stabilizer fixes the unique nonidentity layer image.
In a full binary linear group, the stabilizer of a transvection center
conjugates that transvection to every nonidentity element of the line
radical. Hence the radical has order two and the dimension is two.

The proof transports the literal source action through both isomorphisms
in HasModelOn. Its consumer reduces the complete G.6.4 list to GL₂(2)
and the three symmetric-module alternatives. Those symmetric alternatives
still require the residual argument; no natural-action output is assumed.

Source: Aschbacher--Smith, 6.2.13, printed p.687 (PDF p.704).
-/

@[expose] public section
open Subgroup Module

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem binary_dimension_of_stabilizer_centralizes
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (t : BinaryLinear.GL V) (ht : t ≠ 1)
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1)
    (hc : ∀ c : BinaryLinear.GL V,
      (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        c w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) →
      c * t * c⁻¹ = t) : finrank (ZMod 2) V = 2 := by
  let W := LinearMap.range (t.toLinearMap - LinearMap.id)
  obtain ⟨w, hw, hgen⟩ := finrank_eq_one_iff'.mp hr
  have hw0 : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
  have hspan : Submodule.span (ZMod 2) {(w : V)} = W := by
    apply le_antisymm (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr w.property))
    intro v hv
    obtain ⟨c, he⟩ := hgen ⟨v, hv⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val he⟩
  have hWcard : Nat.card W = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hr]
    decide
  have htW (v : V) (hv : v ∈ W) : t v ∈ W := by
    obtain ⟨u, rfl⟩ := hv
    refine ⟨t u, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      LinearEquiv.coe_coe]
  have htR : t ∈ BinaryLinear.radical (Submodule.span (ZMod 2) {(w : V)}) := by
    rw [hspan]
    refine ⟨?_, fun v => ⟨v, rfl⟩⟩
    intro v hv
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact congrArg Subtype.val (((Nat.card_eq_two_iff' (0 : W)).mp hWcard).unique
        (show (⟨t v, htW v hv⟩ : W) ≠ 0 from fun he => hv0
          (t.injective ((congrArg Subtype.val he).trans (map_zero t).symm)))
        (show (⟨v, hv⟩ : W) ≠ 0 from fun he => hv0 (congrArg Subtype.val he)))
  obtain ⟨f, hf, hfw, htf⟩ := BinaryLinear.exists_transvection_of_mem_line_radical hw0 htR ht
  have hte : t = BinaryLinear.transvection (w : V) f hfw := LinearEquiv.ext htf
  have hRcard : Nat.card (BinaryLinear.radical (Submodule.span (ZMod 2) {(w : V)})) = 2 := by
    apply (Nat.card_eq_two_iff' 1).mpr
    refine ⟨⟨t, htR⟩, fun he => ht (congrArg Subtype.val he), ?_⟩
    intro s hs
    obtain ⟨c, hcw, hcs⟩ := BinaryLinear.LineRadical.conjugate_fixing_center
      (w : V) hw0 f hf hfw s.property (fun he => hs (Subtype.ext he))
    have hct : c * t * c⁻¹ = t := hc c (by
      intro v hv
      change v ∈ W at hv
      change c v ∈ W
      rw [← hspan] at hv ⊢
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, hcw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    apply Subtype.ext
    calc
      (s : BinaryLinear.GL V) = c * BinaryLinear.transvection (w : V) f hfw * c⁻¹ := hcs.symm
      _ = c * t * c⁻¹ := congrArg (fun s : BinaryLinear.GL V => c * s * c⁻¹) hte.symm
      _ = t := hct
  rw [BinaryLinear.LineRadical.card (w : V) hw0] at hRcard
  have he : finrank (ZMod 2) V - 1 = 1 :=
    Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hRcard)
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Module
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- A binary-linear model for the equality action has dimension two.
The stabilizer of its displacement line must fix its marked transvection. -/
theorem LocalAnalysis.equality_binaryLinearModel_dimension
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R)
    (m : ℕ)
    (hmodel : let := A.sourceEqualityVectorQuotient_elementary h611 hz
      ChapterG.Section06.HasModelOn (sourceEqualityRepresentation A h611 hz) ⊤ ⊤
      (ChapterG.Section06.binaryLinearAction m)) : m = 2 := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  let ρ := equalityRepresentation A
  obtain ⟨a, ha, ha1, _⟩ := A.exists_equalityCentralMark h611 hnatural hz hTH
  have hSH : ZS (T : Subgroup G) L R ≤ centralizer ({z} : Set G) :=
    inf_le_left.trans (layer_le_involution_centralizer h611 hz)
  have hcard := (h611.natural_ZS_geometry hnatural).2.1
  have hline := equalityDisplacement_eq_line A
    (A.layer_closure_commutator_eq_plane h611 hnatural hz hTH hbranch).le
    hSH hz horder hcard a ha ha1
  have hrank : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 := by
    rw [hline]
    exact equalityVectorSubspace_finrank hSH hz horder hcard
  obtain ⟨eK, eW, stable, equivariant⟩ := hmodel
  let e : EqualityActor z ≃* BinaryLinear.GL (Fin m → ZMod 2) :=
    Subgroup.topEquiv.symm.trans eK
  let f : Additive (EqualityVectorQuotient (T : Subgroup G) L R z) ≃ₗ[ZMod 2]
      (Fin m → ZMod 2) := Submodule.topEquiv.symm.trans eW
  have hact (b : EqualityActor z) (v : Additive (EqualityVectorQuotient (T : Subgroup G) L R z)) :
      f (ρ b v) = e b (f v) := equivariant ⟨b, mem_top b⟩ ⟨v, Submodule.mem_top⟩
  have hrange : (LinearMap.range (ρ a - LinearMap.id)).map f.toLinearMap =
      LinearMap.range ((e a).toLinearMap - LinearMap.id) := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      refine ⟨f u, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, hact]
    · rintro ⟨u, rfl⟩
      refine ⟨ρ a (f.symm u) - f.symm u, ⟨f.symm u, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub,
        hact, LinearEquiv.apply_symm_apply]
  have hrank' : finrank (ZMod 2) (LinearMap.range ((e a).toLinearMap - LinearMap.id)) = 1 := by
    rw [← hrange, f.finrank_map_eq, hrank]
  have he : finrank (ZMod 2) (Fin m → ZMod 2) = 2 :=
    binary_dimension_of_stabilizer_centralizes (e a)
      (fun he => ha1 (e.injective (he.trans (map_one e).symm))) hrank' (by
        intro c hc
        have hb : ∀ w ∈ equalityVectorSubspace
            (T := (T : Subgroup G)) (L := L) (R := R) (z := z),
            ρ (e.symm c) w ∈ equalityVectorSubspace := by
          intro w hw
          rw [← hline] at hw ⊢
          have hfw : f w ∈ LinearMap.range ((e a).toLinearMap - LinearMap.id) := by
            rw [← hrange]
            exact Submodule.mem_map_of_mem hw
          have hcwf := hc (f w) hfw
          rw [← hrange] at hcwf
          obtain ⟨u, hu, heu⟩ := hcwf
          have heq : u = ρ (e.symm c) w := by
            apply f.injective
            rw [hact, MulEquiv.apply_symm_apply]
            exact heu
          exact heq ▸ hu
        have heq := A.equality_line_stabilizer_fixes_mark h611 hnatural hz a ha ha1
          (e.symm c) hb
        have hh := congrArg e heq
        simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hh)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using he

/-- Apply G.6.4 to the literal equality action and eliminate every binary
linear model of dimension at least three. The symmetric alternatives still
require the residual argument of 6.2.13. -/
theorem LocalAnalysis.equality_action_reduced_classification
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R) :
    let := A.sourceEqualityVectorQuotient_elementary h611 hz
    let ρ := sourceEqualityRepresentation A h611 hz
    EqualityNaturalAction A h611 hz ∨
      ChapterG.Section06.HasModelOn ρ ⊤ ⊤
        (BinaryPermutation.naturalRepresentation (Fin 6)) ∨
      ChapterG.Section06.HasModelOn ρ ⊤ ⊤
        (BinaryPermutation.naturalRepresentation (Fin 7)) ∨
      ChapterG.Section06.HasModelOn ρ ⊤ ⊤
        (BinaryPermutation.coreRepresentation (Fin 6)) := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨_, _, _, _, _, _, hm⟩ :=
    A.equality_action_classification h611 hnatural hz horder hTH hbranch
  rcases hm with ⟨m, _, _, hm⟩ | hm
  · have he := A.equality_binaryLinearModel_dimension h611 hnatural hz horder hTH hbranch m hm
    subst m
    exact Or.inl hm
  · exact Or.inr hm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
