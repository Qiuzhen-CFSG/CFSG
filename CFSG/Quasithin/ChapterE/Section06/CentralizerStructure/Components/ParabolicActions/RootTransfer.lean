module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Root realization in the parabolic branch of E.6.11

Put W = [V,L ∩ M]. The E.6.8 decomposition V = W C_V(L) says that W induces
the same automorphisms of L as V. Since V normalizes L, W lies in L. For n > 1
the supplied derived symplectic model is the full matrix group, by its actual
inclusion isomorphism. Its trivial center then turns the equality of induced
actions into equality with an actual matrix root subgroup.

Maximality inside L identifies L ∩ M with the root normalizer as soon as that
normalizer is known to be proper. The centralizer and solvable residual are
transported through the same embedding. The final residual theorem deliberately
retains the intrinsic root-normalizer residual identity as an explicit premise;
this module does not assert the missing matrix calculation or torus existence.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3c),
printed p.250 (PDF p.261), using the decomposition in E.6.8(2).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Components.ParabolicActions
variable {G : Type*} [Group G] {L V W : Subgroup G}

private theorem automizer_map (L A : Subgroup G) :
    (inducedAutomizer L A).map (Automizer L).subtype =
      (A.subgroupOf (normalizer (L : Set G))).map L.normalizerMonoidHom := by
  rw [inducedAutomizer, map_map]
  rfl

private theorem image_from_decomposition (hVN : V ≤ normalizer (L : Set G))
    (hWL : W ≤ L) (hdecomp : W ⊔ (V ⊓ centralizer (L : Set G)) = V) :
    (inducedAutomizer L V).map (Automizer L).subtype =
      (W.subgroupOf L).map (MulAut.conj : L →* MulAut L) := by
  have hWV : W ≤ V := hdecomp ▸ le_sup_left
  rw [automizer_map, ← hdecomp, subgroupOf_sup (hWV.trans hVN)
    ((inf_le_right : V ⊓ centralizer (L : Set G) ≤ _).trans
      (centralizer_le_normalizer _)), Subgroup.map_sup]
  have hc : ((V ⊓ centralizer (L : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, normalizerMonoidHom_ker]
    exact comap_mono inf_le_right
  rw [hc, sup_bot_eq]
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w.val, hWL hw⟩, hw, ?_⟩
    ext l
    rfl
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w.val, L.le_normalizer w.property⟩, hw, ?_⟩
    ext l
    rfl

private theorem congr_conj {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (MulAut.congr e).toMonoidHom.comp MulAut.conj =
      MulAut.conj.comp e.toMonoidHom := by
  ext a b
  simp [MulAut.congr, MulAut.conj_apply]

private theorem transported_image_from_decomposition
    {A : Type*} [Group A] (e : L ≃* A)
    (hVN : V ≤ normalizer (L : Set G))
    (hWL : W ≤ L) (hdecomp : W ⊔ (V ⊓ centralizer (L : Set G)) = V) :
    ((inducedAutomizer L V).map (Automizer L).subtype).map
        (MulAut.congr e).toMonoidHom =
      ((W.subgroupOf L).map e.toMonoidHom).map MulAut.conj := by
  rw [image_from_decomposition hVN hWL hdecomp, map_map, congr_conj, map_map]

private theorem conj_injective_of_center_eq_bot {A : Type*} [Group A]
    (hc : center A = ⊥) : Function.Injective (MulAut.conj : A →* MulAut A) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  rw [← hc]
  apply mem_center_iff.mpr
  intro b
  have he := DFunLike.congr_fun (show MulAut.conj a = 1 from ha) b
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

open Theory.SpecificGroups.SymplecticFour

private theorem derived_conj {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) :
    (MulAut.congr (derivedEquivFull_of_card_gt_two hF)).toMonoidHom.comp
      (MulAut.conjNormal (H := commutator (Sp F))) = MulAut.conj := by
  ext a : 1
  ext b : 1
  change derivedEquivFull_of_card_gt_two hF
      (MulAut.conjNormal a ((derivedEquivFull_of_card_gt_two hF).symm b)) =
    a * b * a⁻¹
  rw [derivedEquivFull_of_card_gt_two_apply, MulAut.conjNormal_apply]
  have he : ((derivedEquivFull_of_card_gt_two hF).symm b).val = b := by
    rw [← derivedEquivFull_of_card_gt_two_apply hF]
    exact (derivedEquivFull_of_card_gt_two hF).apply_symm_apply b
  rw [he]

private theorem congr_trans {A B C : Type*} [Group A] [Group B] [Group C]
    (e : A ≃* B) (f : B ≃* C) :
    (MulAut.congr f).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      (MulAut.congr (e.trans f)).toMonoidHom := by
  ext a c
  rfl

/-- An inner root action and the fixed-space decomposition identify an embedded root. -/
theorem root_of_decomposition {n : ℕ} (hn : 1 < n)
    (hroot : SymplecticRootAction L V n) (hWL : W ≤ L)
    (hdecomp : W ⊔ (V ⊓ centralizer (L : Set G)) = V) : SymplecticRoot L W n := by
  obtain ⟨hVN, F, hfield, hfinite, hcard, e, r, he⟩ := hroot
  let := hfield
  let := hfinite
  let := EvenProjective.charTwo_of_card hcard
  have hF : 2 < Nat.card F := by
    rw [hcard]
    exact (Nat.pow_lt_pow_right (by decide : 1 < 2) hn)
  let f := derivedEquivFull_of_card_gt_two hF
  refine ⟨hWL, F, hfield, hfinite, hcard, e.trans f, r, ?_⟩
  apply map_injective (conj_injective_of_center_eq_bot
    (EvenProjective.center_eq_bot (F := F)))
  rw [← transported_image_from_decomposition (e.trans f) hVN hWL hdecomp]
  have hh := congrArg (Subgroup.map (MulAut.congr f).toMonoidHom) he
  rw [map_map, congr_trans] at hh
  simp only [map_map] at hh ⊢
  rw [show (MulAut.congr f).toMonoidHom.comp MulAut.conjNormal =
    MulAut.conj from derived_conj hF] at hh
  exact hh

/-- Normalization, rather than ambient normality, puts the displacement inside L. -/
theorem displacement_le_component {M : Subgroup G}
    (hVN : V ≤ normalizer (L : Set G)) : ⁅V, L ⊓ M⁆ ≤ L :=
  (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp hVN)

/-- The displacement in the genuine symplectic alternative is an actual matrix root. -/
theorem displacement_is_root {M U : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hs : SymplecticAlternative M V U L n) (hroot : SymplecticRootAction L V n) :
    SymplecticRoot L ⁅V, L ⊓ M⁆ n :=
  root_of_decomposition hn hroot (displacement_le_component hroot.1)
    (hs.decomposition hn).1

/-- The fixed factor contributes no further centralizer restriction inside L. -/
theorem centralizer_eq_of_decomposition
    (hdecomp : W ⊔ (V ⊓ centralizer (L : Set G)) = V) :
    L ⊓ centralizer (V : Set G) = L ⊓ centralizer (W : Set G) := by
  have hWV : W ≤ V := hdecomp ▸ le_sup_left
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hWV))
  intro l hl
  refine ⟨hl.1, ?_⟩
  have hc : V ≤ centralizer ({l} : Set G) := by
    rw [← hdecomp]
    apply sup_le
    · intro w hw
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hl.2) w hw)
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hv.2) l hl.1).symm
  exact mem_centralizer_iff.mpr (fun v hv =>
    (mem_centralizer_singleton_iff.mp (hc hv)))

/-- The centralizers of V and its displacement agree inside L. -/
theorem displacement_centralizer {M U : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hs : SymplecticAlternative M V U L n) :
    L ⊓ centralizer (V : Set G) = L ⊓ centralizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) :=
  centralizer_eq_of_decomposition (hs.decomposition hn).1

/-- A maximal parabolic normalizing the displacement is its proper root normalizer. -/
theorem parabolic_map_eq_root_normalizer {M : Subgroup G}
    {A : Type*} [Group A] (e : L ≃* A) (R : Subgroup A)
    (hVN : V ≤ normalizer (L : Set G))
    (hP : MaximalParabolic L (L ⊓ M))
    (hR : ((⁅V, L ⊓ M⁆ : Subgroup G).subgroupOf L).map e.toMonoidHom = R)
    (hN : normalizer (R : Set A) ≠ ⊤) :
    ((L ⊓ M).subgroupOf L).map e.toMonoidHom = normalizer (R : Set A) := by
  have hc : IsCoatom (((L ⊓ M).subgroupOf L).map e.toMonoidHom) :=
    (e.mapSubgroup.isCoatom_iff _).mpr hP.2.1
  apply ((hc.le_iff_eq hN).mp ?_).symm
  rw [← hR, ← map_equiv_normalizer_eq]
  apply map_mono
  rw [← subgroupOf_normalizer_eq (displacement_le_component hVN)]
  exact comap_mono (normalizer_commutator_ge_right V (L ⊓ M))

private theorem relative_centralizer (hWL : W ≤ L) :
    (L ⊓ centralizer (W : Set G)).subgroupOf L =
      centralizer (W.subgroupOf L : Set L) := by
  ext l
  constructor
  · intro hl
    exact mem_centralizer_iff.mpr (fun w hw =>
      Subtype.ext (mem_centralizer_iff.mp hl.2 w.val hw))
  · intro hl
    refine ⟨l.property, mem_centralizer_iff.mpr ?_⟩
    intro w hw
    exact congrArg Subtype.val (mem_centralizer_iff.mp hl ⟨w, hWL hw⟩ hw)

private theorem centralizer_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (R : Subgroup A) :
    (centralizer (R : Set A)).map e.toMonoidHom =
      centralizer (R.map e.toMonoidHom : Set B) := by
  ext b
  simp only [mem_map_equiv, mem_centralizer_iff]
  constructor
  · intro h a ha
    apply e.symm.injective
    simpa only [map_mul] using h (e.symm a) (mem_map_equiv.mp ha)
  · intro h a ha
    have he := h (e a) (by simpa)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm he

/-- Transport the centralizer of V to the centralizer of the same matrix root. -/
theorem displacement_centralizer_map {M U : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hs : SymplecticAlternative M V U L n) (hVN : V ≤ normalizer (L : Set G))
    {A : Type*} [Group A] (e : L ≃* A) (R : Subgroup A)
    (hR : ((⁅V, L ⊓ M⁆ : Subgroup G).subgroupOf L).map e.toMonoidHom = R) :
    ((L ⊓ centralizer (V : Set G)).subgroupOf L).map e.toMonoidHom =
      centralizer (R : Set A) := by
  rw [displacement_centralizer hn hs,
    relative_centralizer (displacement_le_component hVN), centralizer_map, hR]

private theorem residual_map_equiv {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) (P : Subgroup A) :
    ((solvableResidual P).map P.subtype).map (e : A →* B) =
      (solvableResidual (P.map (e : A →* B))).map (P.map (e : A →* B)).subtype := by
  have he : (P.map (e : A →* B)).subtype.comp (e.subgroupMap P).toMonoidHom =
      (e : A →* B).comp P.subtype := by
    ext x
    rfl
  rw [map_map, ← he, ← map_map,
    map_solvableResidual_eq _ (e.subgroupMap P).surjective]

private theorem residual_relative [Finite G] {P : Subgroup G} (hPL : P ≤ L) :
    ((solvableResidual (P.subgroupOf L)).map (P.subgroupOf L).subtype).map L.subtype =
      (solvableResidual P).map P.subtype := by
  have he : P.subtype.comp (subgroupOfEquivOfLe hPL).toMonoidHom =
      L.subtype.comp (P.subgroupOf L).subtype := by
    ext x
    rfl
  rw [map_map, ← he, ← map_map,
    map_solvableResidual_eq _ (subgroupOfEquivOfLe hPL).surjective]

/-- The intrinsic root-normalizer residual identity implies the required embedded residual identity. -/
theorem parabolic_residual_of_root_normalizer_residual [Finite G]
    {M U : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hs : SymplecticAlternative M V U L n) (hVN : V ≤ normalizer (L : Set G))
    (hP : MaximalParabolic L (L ⊓ M))
    {A : Type*} [Group A] (e : L ≃* A) (R : Subgroup A)
    (hR : ((⁅V, L ⊓ M⁆ : Subgroup G).subgroupOf L).map e.toMonoidHom = R)
    (hN : normalizer (R : Set A) ≠ ⊤)
    (hres : (solvableResidual (normalizer (R : Set A))).map
      (normalizer (R : Set A)).subtype = centralizer (R : Set A)) :
    (solvableResidual ↥(L ⊓ M)).map (L ⊓ M).subtype =
      L ⊓ centralizer (V : Set G) := by
  have hPN := parabolic_map_eq_root_normalizer e R hVN hP hR hN
  have he : (solvableResidual ((L ⊓ M).subgroupOf L)).map
      ((L ⊓ M).subgroupOf L).subtype = (L ⊓ centralizer (V : Set G)).subgroupOf L := by
    apply map_injective (f := e.toMonoidHom) e.injective
    have ht : ((solvableResidual ((L ⊓ M).subgroupOf L)).map
        ((L ⊓ M).subgroupOf L).subtype).map e.toMonoidHom =
        (solvableResidual (((L ⊓ M).subgroupOf L).map e.toMonoidHom)).map
          (((L ⊓ M).subgroupOf L).map e.toMonoidHom).subtype :=
      residual_map_equiv e ((L ⊓ M).subgroupOf L)
    rw [ht, hPN, hres, displacement_centralizer_map hn hs hVN e R hR]
  have hh := congrArg (Subgroup.map L.subtype) he
  rw [residual_relative inf_le_left, map_subgroupOf_eq_of_le inf_le_left] at hh
  exact hh

end CFSG.Quasithin.ChapterE.Section06.Components.ParabolicActions
