module

public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterInvolutions.LinearConjugacy
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections

/-!
# The three sections of any outer Hermitian involution

An F-linear conjugator carries the actual fixed kernel and commutator range
to the marked field-involution spaces. Its restrictions and induced quotient
maps intertwine the inherited centralizer actions. This proves faithfulness
and dimension three on all three sections, identifies the full image
centralizer with SL₃(F), and transports the pointwise-centralizer calculation.
The binary fixed kernel has dimension 6n. Finally every outer involution is
shown to have this F-linear description with equality of its actual action.

Source: Aschbacher–Smith, H.4.4(6), printed p.381; the standing faithful
binary action and residual convention are on printed p.377.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterInvolutions
variable (n : ℕ) [NeZero n] (i : Space n ≃ₗ[F n] Space n)

/-- The centralizer inside the literal binary image. -/
def centralizer : Subgroup (Space n ≃ₗ[ZMod 2] Space n) :=
  binaryImage n ⊓ Subgroup.centralizer ({binaryEquiv n i} : Set _)

/-- Restriction of the original image action to that centralizer. -/
def action : Representation (F n) (centralizer n i) (Space n) :=
  (imageAction n).comp ((binaryImageEquiv n).symm.toMonoidHom.comp
    (Subgroup.inclusion (show centralizer n i ≤ binaryImage n from inf_le_left)))

theorem action_apply (g : centralizer n i) (X : Space n) : action n i g X = g.val X := by
  have h := (binaryImageEquiv n).apply_symm_apply (⟨g.val, g.property.1⟩ : binaryImage n)
  exact congrArg (fun a : binaryImage n => a.val X) h

theorem action_commutes (g : centralizer n i) (X : Space n) :
    action n i g (i X) = i (action n i g X) := by
  rw [action_apply, action_apply]
  exact congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e X)
    (Subgroup.mem_centralizer_singleton_iff.mp g.property.2)

/-- The actual fixed space C_V(i). -/
def fixed : Submodule (F n) (Space n) := LinearMap.ker (i.toLinearMap - LinearMap.id)
/-- The actual commutator space [V,i]. -/
def moved : Submodule (F n) (Space n) := LinearMap.range (i.toLinearMap - LinearMap.id)

theorem mem_fixed (X : Space n) : X ∈ fixed n i ↔ i X = X := by
  change i X - X = 0 ↔ _
  exact sub_eq_zero

def fixedSubrepresentation : Subrepresentation (action n i) where
  toSubmodule := fixed n i
  apply_mem_toSubmodule g X hX := by
    rw [mem_fixed] at hX ⊢
    rw [← action_commutes, hX]

def movedSubrepresentation : Subrepresentation (action n i) where
  toSubmodule := moved n i
  apply_mem_toSubmodule g X hX := by
    obtain ⟨Y, rfl⟩ := hX
    refine ⟨action n i g Y, ?_⟩
    change i (action n i g Y) - action n i g Y = action n i g (i Y - Y)
    rw [map_sub, action_commutes]

def movedAction : Representation (F n) (centralizer n i) (moved n i) :=
  (movedSubrepresentation n i).toRepresentation

def fixedAction : Representation (F n) (centralizer n i) (fixed n i) :=
  (fixedSubrepresentation n i).toRepresentation

/-- The inverse image of [V,i] under the inclusion C_V(i) → V. -/
def movedInFixed : Submodule (F n) (fixed n i) := (moved n i).comap (fixed n i).subtype

def middleAction : Representation (F n) (centralizer n i)
    ((fixed n i) ⧸ movedInFixed n i) :=
  (fixedAction n i).quotient (movedInFixed n i)
    (fun g _ hX => (movedSubrepresentation n i).apply_mem_toSubmodule g hX)

def topAction : Representation (F n) (centralizer n i) ((Space n) ⧸ fixed n i) :=
  (action n i).quotient (fixed n i) (fixedSubrepresentation n i).apply_mem_toSubmodule

theorem movedAction_apply (g : centralizer n i) (X : moved n i) :
    (movedAction n i g X).val = g.val X.val := action_apply n i g X.val

theorem fixedAction_apply (g : centralizer n i) (X : fixed n i) :
    (fixedAction n i g X).val = g.val X.val := action_apply n i g X.val

theorem middleAction_mk (g : centralizer n i) (X : fixed n i) :
    middleAction n i g ((movedInFixed n i).mkQ X) =
      (movedInFixed n i).mkQ (fixedAction n i g X) := rfl

theorem topAction_mk (g : centralizer n i) (X : Space n) :
    topAction n i g ((fixed n i).mkQ X) = (fixed n i).mkQ (action n i g X) := rfl

variable (c : Space n ≃ₗ[F n] Space n)
  (hc : binaryEquiv n c ∈ binaryNormalizer n)
  (hi : MulAut.conj (binaryEquiv n c) (binaryEquiv n i) = fieldSwapBinary n)

include hi in
theorem intertwines (X : Space n) : c (i X) = fieldSwap n (c X) := by
  have h := congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e (c X)) hi
  change c (i (c.symm (c X))) = fieldSwap n (c X) at h
  simpa only [c.symm_apply_apply] using h

include hi in
theorem fixed_iff (X : Space n) : X ∈ fixed n i ↔ c X ∈ fieldFixed n := by
  rw [mem_fixed, mem_fieldFixed, ← intertwines n i c hi]
  exact c.injective.eq_iff.symm

include hi in
theorem moved_iff (X : Space n) : X ∈ moved n i ↔ c X ∈ FieldSections.moved n := by
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨c Y, ?_⟩
    change fieldSwap n (c Y) - c Y = c (i Y - Y)
    rw [map_sub, intertwines n i c hi]
  · rintro ⟨Y, hY⟩
    refine ⟨c.symm Y, c.injective ?_⟩
    change c (i (c.symm Y) - c.symm Y) = c X
    rw [map_sub, intertwines n i c hi, c.apply_symm_apply]
    exact hY

include hi in
theorem fixed_map : (fixed n i).map c.toLinearMap = fieldFixed n := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩; exact (fixed_iff n i c hi Y).mp hY
  · intro hX
    exact ⟨c.symm X, (fixed_iff n i c hi _).mpr (by simpa using hX), c.apply_symm_apply X⟩

include hi in
theorem moved_map : (moved n i).map c.toLinearMap = FieldSections.moved n := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩; exact (moved_iff n i c hi Y).mp hY
  · intro hX
    exact ⟨c.symm X, (moved_iff n i c hi _).mpr (by simpa using hX), c.apply_symm_apply X⟩

def fixedEquiv : fixed n i ≃ₗ[F n] fieldFixed n :=
  c.ofSubmodules _ _ (fixed_map n i c hi)

def movedEquiv : moved n i ≃ₗ[F n] FieldSections.moved n :=
  c.ofSubmodules _ _ (moved_map n i c hi)

include hi in
theorem moved_le_fixed : moved n i ≤ fixed n i := by
  intro X hX
  exact (fixed_iff n i c hi X).mpr
    (FieldSections.moved_le_fixed n ((moved_iff n i c hi X).mp hX))

include hi in
theorem movedInFixed_map :
    (movedInFixed n i).map (fixedEquiv n i c hi).toLinearMap = FieldSections.movedInFixed n := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact (moved_iff n i c hi Y.val).mp hY
  · intro hX
    refine ⟨(fixedEquiv n i c hi).symm X, ?_, (fixedEquiv n i c hi).apply_symm_apply X⟩
    apply (moved_iff n i c hi _).mpr
    change c (c.symm X.val) ∈ FieldSections.moved n
    change X.val ∈ FieldSections.moved n at hX
    simpa only [c.apply_symm_apply] using hX

def middleEquiv : ((fixed n i) ⧸ movedInFixed n i) ≃ₗ[F n]
    ((fieldFixed n) ⧸ FieldSections.movedInFixed n) :=
  Submodule.Quotient.equiv _ _ (fixedEquiv n i c hi) (movedInFixed_map n i c hi)

def topEquiv : ((Space n) ⧸ fixed n i) ≃ₗ[F n] ((Space n) ⧸ fieldFixed n) :=
  Submodule.Quotient.equiv _ _ c (fixed_map n i c hi)

/-- Conjugation on the literal image centralizer, retaining its action on V. -/
def centralizerToMarked : centralizer n i ≃* FieldSections.centralizer n :=
  OuterRank.imageCentralizerEquivOfConj n (binaryEquiv n i) (binaryEquiv n c) hc hi

def centralizerEquiv : centralizer n i ≃* Matrix.SpecialLinearGroup (Fin 3) (F n) :=
  (centralizerToMarked n i c hc hi).trans (FieldSections.centralizerEquiv n)

theorem action_intertwines (g : centralizer n i) (X : Space n) :
    c (action n i g X) =
      FieldSections.centralizerAction n (centralizerToMarked n i c hc hi g) (c X) := by
  rw [action_apply, FieldSections.centralizerAction_apply]
  change c (g.val X) = (binaryEquiv n c * g.val * (binaryEquiv n c)⁻¹) (c X)
  change c (g.val X) = c (g.val (c.symm (c X)))
  rw [c.symm_apply_apply]

theorem moved_intertwines (g : centralizer n i) (X : moved n i) :
    movedEquiv n i c hi (movedAction n i g X) =
      FieldSections.movedAction n (centralizerToMarked n i c hc hi g) (movedEquiv n i c hi X) := by
  apply Subtype.ext
  exact action_intertwines n i c hc hi g X.val

theorem fixed_intertwines (g : centralizer n i) (X : fixed n i) :
    fixedEquiv n i c hi (fixedAction n i g X) =
      FieldSections.fixedAction n (centralizerToMarked n i c hc hi g) (fixedEquiv n i c hi X) := by
  apply Subtype.ext
  exact action_intertwines n i c hc hi g X.val

theorem middle_intertwines (g : centralizer n i) (X : (fixed n i) ⧸ movedInFixed n i) :
    middleEquiv n i c hi (middleAction n i g X) =
      FieldSections.middleAction n (centralizerToMarked n i c hc hi g) (middleEquiv n i c hi X) := by
  induction X using Submodule.Quotient.induction_on with
  | _ X =>
    change (FieldSections.movedInFixed n).mkQ (fixedEquiv n i c hi (fixedAction n i g X)) =
      (FieldSections.movedInFixed n).mkQ (FieldSections.fixedAction n
        (centralizerToMarked n i c hc hi g) (fixedEquiv n i c hi X))
    rw [fixed_intertwines]

theorem top_intertwines (g : centralizer n i) (X : (Space n) ⧸ fixed n i) :
    topEquiv n i c hi (topAction n i g X) =
      FieldSections.topAction n (centralizerToMarked n i c hc hi g) (topEquiv n i c hi X) := by
  induction X using Submodule.Quotient.induction_on with
  | _ X =>
    change (fieldFixed n).mkQ (c (action n i g X)) =
      (fieldFixed n).mkQ (FieldSections.centralizerAction n (centralizerToMarked n i c hc hi g) (c X))
    rw [action_intertwines]

private theorem faithful_of_intertwines {k G H U V : Type*} [Field k] [Group G] [Group H]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (ρ : Representation k G U) (σ : Representation k H V) (e : G ≃* H) (f : U ≃ₗ[k] V)
    (hf : ∀ g x, f (ρ g x) = σ (e g) (f x)) (hσ : Function.Injective σ) :
    Function.Injective ρ := by
  intro g h he
  apply e.injective
  apply hσ
  ext x
  obtain ⟨y, rfl⟩ := f.surjective x
  rw [← hf, ← hf, he]

include hc hi in
theorem movedAction_faithful : Function.Injective (movedAction n i) :=
  faithful_of_intertwines _ _ (centralizerToMarked n i c hc hi) (movedEquiv n i c hi)
    (moved_intertwines n i c hc hi) (FieldSections.movedAction_faithful n)

include hc hi in
theorem middleAction_faithful : Function.Injective (middleAction n i) :=
  faithful_of_intertwines _ _ (centralizerToMarked n i c hc hi) (middleEquiv n i c hi)
    (middle_intertwines n i c hc hi) (FieldSections.middleAction_faithful n)

include hc hi in
theorem topAction_faithful : Function.Injective (topAction n i) :=
  faithful_of_intertwines _ _ (centralizerToMarked n i c hc hi) (topEquiv n i c hi)
    (top_intertwines n i c hc hi) (FieldSections.topAction_faithful n)

include hi in
theorem finrank_fixed : Module.finrank (F n) (fixed n i) = 6 :=
  (fixedEquiv n i c hi).finrank_eq.trans (finrank_fieldFixed n)

include hi in
theorem finrank_moved : Module.finrank (F n) (moved n i) = 3 :=
  (movedEquiv n i c hi).finrank_eq.trans (FieldSections.finrank_moved n)

include hi in
theorem finrank_middle : Module.finrank (F n) ((fixed n i) ⧸ movedInFixed n i) = 3 :=
  (middleEquiv n i c hi).finrank_eq.trans (FieldSections.finrank_middle n)

include hi in
theorem finrank_top : Module.finrank (F n) ((Space n) ⧸ fixed n i) = 3 :=
  (topEquiv n i c hi).finrank_eq.trans (FieldSections.finrank_top n)

/-- The pointwise stabilizer of the literal fixed space. -/
def pointwiseFixed : Subgroup (Space n ≃ₗ[ZMod 2] Space n) where
  carrier := {e | ∀ X : fixed n i, e X.val = X.val}
  one_mem' := by intro X; rfl
  mul_mem' := by
    intro e f he hf X
    change e (f X.val) = X.val
    rw [hf, he]
  inv_mem' := by
    intro e he X
    apply e.injective
    change e (e.symm X.val) = e X.val
    rw [LinearEquiv.apply_symm_apply, he]

theorem self_mem_pointwiseFixed : binaryEquiv n i ∈ pointwiseFixed n i := by
  intro X
  exact (mem_fixed n i X.val).mp X.property

include hc hi in
theorem eq_one_or_self_of_fixes
    (e : Space n ≃ₗ[ZMod 2] Space n) (heN : e ∈ binaryNormalizer n)
    (he : e ∈ pointwiseFixed n i) : e = 1 ∨ e = binaryEquiv n i := by
  let b := binaryEquiv n c
  have hb : MulAut.conj b e ∈ binaryNormalizer n :=
    (binaryNormalizer n).mul_mem ((binaryNormalizer n).mul_mem hc heN)
      ((binaryNormalizer n).inv_mem hc)
  have hfix : ∀ X : fieldFixed n, MulAut.conj b e X.val = X.val := by
    intro X
    obtain ⟨Y, rfl⟩ := (fixedEquiv n i c hi).surjective X
    change c (e (c.symm (c Y.val))) = c Y.val
    rw [c.symm_apply_apply, he]
  rcases FieldSections.eq_one_or_fieldSwapBinary_of_fixes n (normalizerCoverage n)
    (MulAut.conj b e) hb hfix with h | h
  · exact Or.inl ((MulAut.conj b).injective (h.trans (map_one (MulAut.conj b)).symm))
  · exact Or.inr ((MulAut.conj b).injective (h.trans hi.symm))

include hc hi in
theorem fixes_iff_mem_zpowers
    (e : Space n ≃ₗ[ZMod 2] Space n) (heN : e ∈ binaryNormalizer n) :
    e ∈ pointwiseFixed n i ↔ e ∈ Subgroup.zpowers (binaryEquiv n i) := by
  constructor
  · intro he
    rcases eq_one_or_self_of_fixes n i c hc hi e heN he with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · intro he
    exact (Subgroup.zpowers_le.mpr (self_mem_pointwiseFixed n i)) he

include hc hi in
/-- The pointwise centralizer inside the source group itself. -/
theorem source_relative_pointwiseFixed_eq
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (hiM : binaryEquiv n i ∈ M) :
    (pointwiseFixed n i).comap M.subtype = Subgroup.zpowers (⟨binaryEquiv n i, hiM⟩ : M) := by
  apply le_antisymm
  · intro e he
    rcases eq_one_or_self_of_fixes n i c hc hi e.val
      (sourceOvergroup_le_normalizer n M hM e.property) he with h | h
    · have he1 : e = 1 := Subtype.ext h
      rw [he1]
      exact Subgroup.one_mem _
    · have hei : e = ⟨binaryEquiv n i, hiM⟩ := Subtype.ext h
      rw [hei]
      exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (self_mem_pointwiseFixed n i)

include hi in
/-- Binary dimension of the actual fixed kernel. -/
theorem finrank_binaryFixed :
    Module.finrank (ZMod 2) (LinearMap.ker ((binaryEquiv n i).toLinearMap - LinearMap.id)) = 6 * n := by
  let e : (LinearMap.ker ((binaryEquiv n i).toLinearMap - LinearMap.id)) ≃ fixed n i := {
    toFun X := ⟨X.val, X.property⟩
    invFun X := ⟨X.val, X.property⟩ }
  have hF := Module.natCard_eq_pow_finrank (K := F n) (V := fixed n i)
  rw [card_F, finrank_fixed n i c hi, ← pow_mul] at hF
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.ker ((binaryEquiv n i).toLinearMap - LinearMap.id))
  have hcard : Nat.card (ZMod 2) = 2 := by simp
  rw [hcard, Nat.card_congr e, hF] at h2
  have hh : n * 6 = Module.finrank (ZMod 2)
      (LinearMap.ker ((binaryEquiv n i).toLinearMap - LinearMap.id)) :=
    (pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2
  omega

/-- An outer binary involution is itself F-linear, with an F-linear conjugator.
Both comparisons concern the given binary action. -/
theorem exists_linear_lift_and_conjugator
    (a : Space n ≃ₗ[ZMod 2] Space n) (haN : a ∈ binaryNormalizer n)
    (ha2 : orderOf a = 2) (haL : a ∉ binaryImage n) :
    ∃ (j c : Space n ≃ₗ[F n] Space n), binaryEquiv n j = a ∧
      binaryEquiv n c ∈ binaryNormalizer n ∧
      MulAut.conj (binaryEquiv n c) (binaryEquiv n j) = fieldSwapBinary n := by
  obtain ⟨c, hc, hca⟩ := exists_linear_conjugator n a haN ha2 haL
  let j := c⁻¹ * fieldSwap n * c
  have hj : binaryEquiv n j = a := by
    change binaryEquivHom n (c⁻¹ * fieldSwap n * c) = a
    rw [map_mul, map_mul, map_inv]
    change (binaryEquiv n c)⁻¹ * fieldSwapBinary n * binaryEquiv n c = a
    rw [← hca, MulAut.conj_apply]
    group
  exact ⟨j, c, hj, hc, by rw [hj]; exact hca⟩

end Representation.HermitianTensorThree.ImageOuter.OuterInvolutions
