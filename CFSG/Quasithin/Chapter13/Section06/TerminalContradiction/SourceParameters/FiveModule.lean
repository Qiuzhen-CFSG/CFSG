module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Coordinates
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# The actual five-point automizer has module parameter one

The normalizer action factors through its genuine automizer: both kernels
are the centralizer of V. The resulting faithful permutation action has
exactly the given coordinate image and intertwines the actual binary action.

For a nontrivial elementary two-subgroup, choose a moved point and a maximal
subgroup containing its stabilizer. This subgroup has index two. The indicator
of its orbit fixes the subgroup but not the full actor. Subtracting its
augmentation times the constant vector puts this witness in the five-point
core without changing its stabilizer. Thus the second fixed-space family is
empty, including for cyclic actors. Containment of A₅ supplies even order and
makes the first family nonempty. No distinctness claim for arbitrary
nonidentity elements is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the direct module calculation in the proof of
13.6.25, printed p.934, with the literal families of E.3.8–9.
-/

public section

open Subgroup BinaryPermutation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveModule

variable {X : Type*} [Group X] [Finite X]

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
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveModule

open Subgroup BinaryPermutation
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveCoordinates
variable {G : Type*} [Group G] {V : Subgroup G}

private theorem automizer_kernel_le (d : FiveCoordinates V) :
    V.normalizerMonoidHom.rangeRestrict.ker ≤ d.actor.ker := by
  intro n hn
  apply (d.actor_eq_one_iff n).mpr
  change n ∈ (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G))
  rw [← normalizerMonoidHom_ker]
  exact congrArg Subtype.val hn

/-- The actual automizer acting on the five coordinates. -/
noncomputable def coordinateActor (d : FiveCoordinates V) :
    ChapterE.Automizer V →* Equiv.Perm (Fin 5) :=
  V.normalizerMonoidHom.rangeRestrict.liftOfSurjective
    V.normalizerMonoidHom.rangeRestrict_surjective ⟨d.actor, automizer_kernel_le d⟩

theorem coordinateActor_normalizer (d : FiveCoordinates V)
    (n : normalizer (V : Set G)) :
    d.coordinateActor (V.normalizerMonoidHom.rangeRestrict n) = d.actor n := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ n

theorem coordinateActor_injective (d : FiveCoordinates V) :
    Function.Injective d.coordinateActor := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨n, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
  rw [coordinateActor_normalizer] at ha
  apply Subtype.ext
  have hc := (d.actor_eq_one_iff n).mp ha
  change n ∈ (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) at hc
  rwa [← normalizerMonoidHom_ker] at hc

theorem coordinateActor_range (d : FiveCoordinates V) :
    d.coordinateActor.range = d.actor.range := by
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨n, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
    exact ⟨n, (d.coordinateActor_normalizer n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨V.normalizerMonoidHom.rangeRestrict n, d.coordinateActor_normalizer n⟩

/-- The automizer is isomorphic to the specified coordinate image. -/
noncomputable def coordinateImageEquiv (d : FiveCoordinates V) :
    ChapterE.Automizer V ≃* d.actor.range :=
  (MonoidHom.ofInjective d.coordinateActor_injective).trans
    (MulEquiv.subgroupCongr d.coordinateActor_range)

theorem coordinateActor_equivariant [IsElementaryAbelian 2 V]
    (d : FiveCoordinates V) (a : ChapterE.Automizer V) (v : Additive V) :
    (d.equiv ((ChapterE.automizerRepresentation V a v).toMul)).toAdd =
      coreRepresentation (Fin 5) (d.coordinateActor a) (d.equiv v.toMul).toAdd := by
  obtain ⟨n, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
  rw [coordinateActor_normalizer]
  exact d.equivariant n v.toMul

/-- Fixed vectors correspond under the given genuine group coordinates. -/
theorem fixedSpace_coordinates [IsElementaryAbelian 2 V]
    (d : FiveCoordinates V) (A : Subgroup (ChapterE.Automizer V)) (v : Additive V) :
    v ∈ Representation.BinaryOffender.fixedSpace (ChapterE.automizerRepresentation V) A ↔
      (d.equiv v.toMul).toAdd ∈ Representation.BinaryOffender.fixedSpace
        (coreRepresentation (Fin 5)) (A.map d.coordinateActor) := by
  constructor
  · intro hv
    rintro ⟨_, a, ha, rfl⟩
    change coreRepresentation (Fin 5) (d.coordinateActor a) (d.equiv v.toMul).toAdd = _
    rw [← d.coordinateActor_equivariant]
    exact congrArg (fun w : Additive V => (d.equiv w.toMul).toAdd) (hv ⟨a, ha⟩)
  · intro hv a
    apply d.equiv.injective
    change (d.equiv ((ChapterE.automizerRepresentation V a v).toMul)).toAdd = _
    rw [d.coordinateActor_equivariant]
    exact hv ⟨d.coordinateActor a, mem_map_of_mem _ a.property⟩

/-- The actual A₅ image forces the automizer to have even order. -/
theorem automizer_even [Finite G] (d : FiveCoordinates V)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range) :
    Even (Nat.card (ChapterE.Automizer V)) := by
  rw [Nat.card_congr d.coordinateImageEquiv.toEquiv]
  apply even_iff_two_dvd.mpr
  apply dvd_trans (show 2 ∣ Nat.card (alternatingGroup (Fin 5)) by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide)
  exact Subgroup.card_dvd_of_le hAlt
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveCoordinates

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveCoordinates
open Subgroup BinaryPermutation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every elementary actor has an index-two subgroup with more fixed vectors. -/
theorem fixedSpaceFamily_two_eq_empty (d : FiveCoordinates V) :
    ChapterE.fixedSpaceFamily (ChapterE.automizerRepresentation V) 2 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨B, hBA, hidx, w, hBw, hAw⟩ :=
    CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveModule.separating_hyperplane d.coordinateActor d.coordinateActor_injective A hA.2.1
  let v : Additive V := Additive.ofMul (d.equiv.symm (Multiplicative.ofAdd w))
  have he : (d.equiv v.toMul).toAdd = w := d.equiv.apply_symm_apply _
  have hvB : v ∈ fixedSpace (ChapterE.automizerRepresentation V) B := by
    apply (d.fixedSpace_coordinates B v).mpr
    rw [he]
    rintro ⟨_, b, hb, rfl⟩
    exact hBw b hb
  have hfix := hA.2.2 B hBA (by rw [hidx]; decide)
  rw [← hfix] at hvB
  have hvA := (d.fixedSpace_coordinates A v).mp hvB
  rw [he] at hvA
  apply hAw
  intro a ha
  exact hvA ⟨d.coordinateActor a, mem_map_of_mem _ ha⟩

/-- The module calculation used in the proof of source Lemma 13.6.25. -/
theorem localA_eq_one (d : FiveCoordinates V)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range) : ChapterE.localA V = 1 := by
  apply le_antisymm
  · change ChapterE.moduleA (ChapterE.automizerRepresentation V) ≤ 1
    apply iSup_le
    intro k
    apply iSup_le
    rintro ⟨A, hA⟩
    by_cases hk : k ≤ 1
    · exact_mod_cast hk
    have hm := ChapterE.fixedSpaceFamily_mono (ChapterE.automizerRepresentation V)
      (show 0 < 2 by decide) (show 2 ≤ k by omega) hA
    rw [d.fixedSpaceFamily_two_eq_empty] at hm
    exact hm.elim
  · obtain ⟨A, hA⟩ := ChapterE.fixedSpaceFamily_one_nonempty_of_even
      (ChapterE.automizerRepresentation V) (d.automizer_even hAlt)
    exact ChapterE.le_moduleA_of_mem (ChapterE.automizerRepresentation V) hA

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.FiveCoordinates
