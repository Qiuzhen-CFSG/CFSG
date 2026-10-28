module
public import CFSG.Quasithin.ChapterE.Section04.Basic
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.SpecificGroups.Alternating.FiveElementaryActors

/-!
# Bounds for full alternating-five module normalizers

The five-point permutation module has parameter at most one: an index-two
subgroup separating a moved orbit has strictly more fixed vectors. The
augmentation correction transfers that vector to the deleted module.
For every faithful irreducible binary A₅ action, Schur's lemma embeds each
elementary subgroup of its full linear normalizer into Aut(A₅), giving
rank at most two. These bounds retain all outer and scalar actors.
Source: Aschbacher–Smith, E.3.8–9 and 10.2.12, printed pp.232 and 754.
-/

public noncomputable section
open Subgroup BinaryPermutation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {X V : Type*} [Group X] [Finite X]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The source fixed-space parameter is bounded by the full actor's two-rank. -/
theorem moduleA_le_primeRank (ρ : Representation (ZMod 2) X V)
    (hf : Function.Injective ρ) : moduleA ρ ≤ (primeRank 2 X : ℕ∞) := by
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A,hA⟩
  apply ENat.natCast_le_natCast.mpr
  have hc := (primeRank_le_iff_elementary_card_le X).mp le_rfl A hA.2.1.2
  have hr : rank A ≤ primeRank 2 X := by
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using
      Nat.log_mono_right (b := 2) hc
  exact (parameter_le_rank_of_mem_fixedSpaceFamily ρ hf hA).trans hr

private theorem separating_hyperplane (f : X →* Equiv.Perm (Fin 5))
    (hf : Function.Injective f) (A : Subgroup X)
    (hA : Representation.BinaryOffender.IsElementaryTwo A) :
    ∃ B : Subgroup X, B ≤ A ∧ B.relIndex A = 2 ∧
      ∃ w : core (Fin 5),
        (∀ b ∈ B, coreRepresentation (Fin 5) (f b) w = w) ∧
        ¬ (∀ a ∈ A, coreRepresentation (Fin 5) (f a) w = w) := by
  classical
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hft : f t ≠ 1 := fun h => ht1 (hf (h.trans (map_one f).symm))
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, f t i ≠ i := by
    by_contra! h
    exact hft (Equiv.ext h)
  let g : A →* Equiv.Perm (Fin 5) := f.comp A.subtype
  let K : Subgroup A := (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap g
  have hK : K ≠ ⊤ := by
    intro h
    have hm : (⟨t, ht⟩ : A) ∈ K := h ▸ Subgroup.mem_top _
    exact hi hm
  obtain ⟨C, hC, hKC⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
  have hidx : C.index = 2 := (IsElementaryAbelian.isPGroup 2 A).index_of_isCoatom C hC
  obtain ⟨a, _, ha⟩ := SetLike.exists_of_lt hC.lt_top
  let R : Fin 5 → Prop := fun j => ∃ b : C, g b i = j
  have hRi : R i := ⟨1, by simp⟩
  have hRa : ¬ R (g a i) := by
    rintro ⟨b, hb⟩
    have hk : a⁻¹ * b.val ∈ K := by
      change g (a⁻¹ * b.val) i = i
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, hb,
        Equiv.symm_apply_apply]
    have hc := C.mul_mem b.property (C.inv_mem (hKC hk))
    apply ha
    simpa using hc
  have hR (b : C) (j : Fin 5) : R (g b j) ↔ R j := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨b⁻¹ * c, ?_⟩
      change g (b.val⁻¹ * c.val) i = j
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, hc,
        Equiv.symm_apply_apply]
    · rintro ⟨c, rfl⟩
      exact ⟨b * c, by simp⟩
  let v : Full (Fin 5) := fun j => if R j then 1 else 0
  have hv (b : C) : representation (Fin 5) (g b) v = v := by
    ext j
    change (if R ((g b).symm j) then (1 : ZMod 2) else 0) = _
    have hr : R ((g b).symm j) ↔ R j := by
      simpa only [Subgroup.coe_inv, map_inv, Equiv.Perm.inv_def] using hR b⁻¹ j
    simp only [hr]
    rfl
  have hva : representation (Fin 5) (g a) v ≠ v := by
    intro h
    have hh := congrFun h (g a i)
    simp only [representation_apply, Equiv.symm_apply_apply] at hh
    have hi1 : v i = 1 := if_pos hRi
    have ha0 : v (g a i) = 0 := if_neg hRa
    rw [hi1, ha0] at hh
    exact one_ne_zero hh
  have hsum : augmentation (Fin 5) (allOne (Fin 5)) = 1 := by
    rw [augmentation_allOne]
    change (5 : ZMod 2) = 1
    decide
  let w : core (Fin 5) := ⟨v - augmentation (Fin 5) v • allOne (Fin 5), by
    change augmentation (Fin 5) _ = 0
    rw [map_sub, map_smul, hsum, smul_eq_mul, mul_one, sub_self]⟩
  refine ⟨C.map A.subtype, ?_, ?_, w, ?_, ?_⟩
  · rintro _ ⟨b, _, rfl⟩
    exact b.property
  · have hh := C.relIndex_map_map_of_injective (⊤ : Subgroup A) A.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using
      hh.trans (by simpa using hidx)
  · rintro _ ⟨b, hb, rfl⟩
    apply Subtype.ext
    change representation (Fin 5) (g b) (v - augmentation (Fin 5) v • allOne (Fin 5)) = _
    rw [map_sub, map_smul, permute_allOne, hv ⟨b, hb⟩]
  · intro h
    have hh := congrArg Subtype.val (h a.val a.property)
    change representation (Fin 5) (g a) (v - augmentation (Fin 5) v • allOne (Fin 5)) = _ at hh
    rw [map_sub, map_smul, permute_allOne] at hh
    exact hva (sub_left_inj.mp hh)

/-- The full symmetric-five deleted module has parameter at most one. -/
theorem moduleA_fiveNatural_le_one :
    moduleA (naturalRepresentation (Fin 5)) ≤ 1 := by
  have hc : moduleA (coreRepresentation (Fin 5)) ≤ 1 := by
    apply (moduleA_le_iff_next_family_empty _ 1).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro A hA
    obtain ⟨B,hBA,hidx,w,hBw,hAw⟩ :=
      separating_hyperplane (MonoidHom.id _) Function.injective_id A hA.2.1
    have hw : (w : core (Fin 5)) ∈ fixedSpace (coreRepresentation (Fin 5)) B :=
      fun b => hBw b b.property
    rw [← hA.2.2 B hBA (by rw [hidx]; decide)] at hw
    exact hAw (fun a ha => hw ⟨a,ha⟩)
  rw [moduleA_eq_of_equivariant_equiv (coreRepresentation (Fin 5))
    (naturalRepresentation (Fin 5)) (MulEquiv.refl _)
    (coreEquivNatural (Fin 5) (by decide))
    (coreEquivNatural_equivariant (Fin 5) (by decide))] at hc
  exact hc

omit [Finite X] in
/-- Full five-point coordinates give the bound for the original actor. -/
theorem moduleA_le_one_of_fiveNatural (ρ : Representation (ZMod 2) X V)
    (f : X →* Equiv.Perm (Fin 5)) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] natural (Fin 5))
    (he : ∀ x v, E (ρ x v) = naturalRepresentation (Fin 5) (f x) (E v)) :
    moduleA ρ ≤ 1 :=
  (moduleA_le_of_equivariant_injective ρ _ f hf E he).trans moduleA_fiveNatural_le_one

/-- Every faithful irreducible binary A₅ action has full-normalizer two-rank at most two. -/
theorem primeRank_alternatingFive_linearNormalizer_le_two
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible) :
    primeRank 2 (linearNormalizer σ) ≤ 2 := by
  have hj : Function.Injective σ.asGroupHom := by
    intro x y h
    exact hf (congrArg Units.val h)
  let e : alternatingGroup (Fin 5) ≃* actionImage σ := MonoidHom.ofInjective hj
  apply (primeRank_linearNormalizer_le σ hi).trans
  rw [← primeRank_equiv 2 (MulAut.congr e)]
  exact Theory.SpecificGroups.Alternating.FiveExtensionAction.automorphism_primeRank_two_le

/-- A faithful action embedding into that full normalizer has parameter at most two,
even when its module is a central cover of the irreducible module. -/
theorem moduleA_le_two_of_alternatingFive_normalizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X V) (hρ : Function.Injective ρ)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (hσ : Function.Injective σ) (hi : σ.IsIrreducible)
    (f : X →* linearNormalizer σ) (hf : Function.Injective f) : moduleA ρ ≤ 2 := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) W) := Finite.of_injective
    (fun g : Module.End (ZMod 2) W => (g : W → W)) DFunLike.coe_injective
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans
    (primeRank_alternatingFive_linearNormalizer_le_two σ hσ hi)
  exact (moduleA_le_primeRank ρ hρ).trans (by exact_mod_cast hr)

end CFSG.Quasithin.ChapterE
