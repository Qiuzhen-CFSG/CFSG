module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.NativeMatrices
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Centralizer

/-!
# A faithful representation of the full automorphism group on the M₁₂ heart

The checked matrices implement the two generators of the actual degree-24
carrier. Implementability is a subgroup condition, so every automorphism has
an implementing linear equivalence. The native scalar-centralizer theorem
makes that equivalence unique; uniqueness supplies the identity, multiplication
and inner-action laws. Faithfulness follows from the native faithful action.
The latter uses the already proved simplicity of M₁₂ and a moved heart vector.

Source: Aschbacher–Smith H.11.1, printed pp.392–393 (1 March 2004 manuscript),
with the existing ATLAS M12d2G1-p24B0 full automorphism identification.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
open Sporadic.Mathieu M12ExceptionalExtension
open LinearMap.GeneralLinearGroup

private theorem intertwines_of_original (a : MulAut M12)
    (e : M12Heart ≃ₗ[ZMod 2] M12Heart)
    (he : ∀ (j : Fin 2) (v : M12Heart),
      e (m12HeartRepresentation (NativeMatrices.original j) v) =
        m12HeartRepresentation (a (NativeMatrices.original j)) (e v))
    (g : M12) (v : M12Heart) :
    e (m12HeartRepresentation g v) = m12HeartRepresentation (a g) (e v) := by
  let f := e.conjRingEquiv.toMonoidHom.comp m12HeartRepresentation
  let q := m12HeartRepresentation.comp a.toMonoidHom
  have hj (j : Fin 2) : NativeMatrices.original j ∈ f.eqLocus q := by
    change f (NativeMatrices.original j) = q (NativeMatrices.original j)
    apply LinearMap.ext
    intro v
    change e (m12HeartRepresentation (NativeMatrices.original j) (e.symm v)) =
      m12HeartRepresentation (a (NativeMatrices.original j)) v
    rw [he, LinearEquiv.apply_symm_apply]
  have ht : f.eqLocus q = ⊤ := original_pair_generates _ (hj 0) (hj 1)
  have hx : g ∈ f.eqLocus q := ht ▸ Subgroup.mem_top g
  have hv := congrArg (fun l : Module.End (ZMod 2) M12Heart => l (e v)) hx
  change e (m12HeartRepresentation g (e.symm (e v))) =
    m12HeartRepresentation (a g) (e v) at hv
  simpa only [LinearEquiv.symm_apply_apply] using hv

private def Implemented (g : Carrier) : Prop :=
  ∃ e : M12Heart ≃ₗ[ZMod 2] M12Heart, ∀ (x : M12) (v : M12Heart),
    e (m12HeartRepresentation x v) =
      m12HeartRepresentation (automorphismEquiv g x) (e v)

private noncomputable def implemented : Subgroup Carrier where
  carrier := Implemented
  one_mem' := ⟨LinearEquiv.refl _ _, by intro x v; simp⟩
  mul_mem' := by
    rintro g h ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨f.trans e, ?_⟩
    intro x v
    simp only [LinearEquiv.trans_apply, hf, he, map_mul, MulAut.mul_apply]
  inv_mem' := by
    rintro g ⟨e, he⟩
    refine ⟨e.symm, ?_⟩
    intro x v
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    simp

private theorem all_implemented (g : Carrier) : Implemented g := by
  have hg (i : Fin 2) : NativeMatrices.generator i ∈ implemented :=
    ⟨NativeMatrices.heartEquiv i,
      intertwines_of_original _ _ (NativeMatrices.heart_intertwines i)⟩
  have htop : group ≤ implemented.map group.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨NativeMatrices.generator 0, hg 0, rfl⟩
    · have : x = generatorB := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨NativeMatrices.generator 1, hg 1, rfl⟩
  obtain ⟨k, hk, hkg⟩ := htop g.property
  have : k = g := Subtype.ext hkg
  exact this ▸ hk

private theorem exists_implementer (a : MulAut M12) :
    ∃ e : M12Heart ≃ₗ[ZMod 2] M12Heart, ∀ (x : M12) (v : M12Heart),
      e (m12HeartRepresentation x v) = m12HeartRepresentation (a x) (e v) := by
  obtain ⟨e, he⟩ := all_implemented (automorphismEquiv.symm a)
  refine ⟨e, ?_⟩
  simpa only [MulEquiv.apply_symm_apply] using he

private noncomputable def implementer (a : MulAut M12) :
    M12Heart ≃ₗ[ZMod 2] M12Heart := (exists_implementer a).choose

private theorem implementer_spec (a : MulAut M12) (x : M12) (v : M12Heart) :
    implementer a (m12HeartRepresentation x v) =
      m12HeartRepresentation (a x) (implementer a v) :=
  (exists_implementer a).choose_spec x v

/-- The unique linear implementation of each actual automorphism of native M₁₂. -/
noncomputable def automorphismRepresentation :
    Representation (ZMod 2) (MulAut M12) M12Heart where
  toFun a := (implementer a).toLinearMap
  map_one' := by
    have he := heart_intertwiner_unique 1 (implementer 1) (LinearEquiv.refl _ _)
      (implementer_spec 1) (by intro x v; rfl)
    exact congrArg LinearEquiv.toLinearMap he
  map_mul' a b := by
    have he := heart_intertwiner_unique (a*b) (implementer (a*b))
      ((implementer b).trans (implementer a)) (implementer_spec (a*b)) (by
        intro x v
        simp only [LinearEquiv.trans_apply, implementer_spec, MulAut.mul_apply])
    exact congrArg LinearEquiv.toLinearMap he

/-- Restriction to the original inner automorphisms is exactly the native heart action. -/
theorem automorphismRepresentation_inner :
    automorphismRepresentation.comp MulAut.conj = m12HeartRepresentation := by
  apply MonoidHom.ext
  intro x
  have hx (y : M12) (v : M12Heart) :
      m12HeartRepresentation x (m12HeartRepresentation y v) =
        m12HeartRepresentation (MulAut.conj x y) (m12HeartRepresentation x v) := by
    have hg : x * y = MulAut.conj x y * x := by simp [MulAut.conj_apply, mul_assoc]
    have hm := congrArg m12HeartRepresentation hg
    rw [map_mul, map_mul] at hm
    exact congrArg (fun l : Module.End (ZMod 2) M12Heart => l v) hm
  have he := heart_intertwiner_unique (MulAut.conj x) (implementer (MulAut.conj x))
    (toLinearEquiv (m12HeartRepresentation.asGroupHom x))
    (implementer_spec (MulAut.conj x)) hx
  exact congrArg LinearEquiv.toLinearMap he

/-- The ten-dimensional native heart action is faithful. -/
theorem heartRepresentation_faithful : Function.Injective m12HeartRepresentation := by
  let : IsSimpleGroup M12 := m12_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal m12HeartRepresentation.ker inferInstance with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff _).mp hbot
  · have ha : originalA ∈ m12HeartRepresentation.ker := htop ▸ Subgroup.mem_top originalA
    change m12HeartRepresentation originalA = 1 at ha
    have hv := congrArg (fun f : Module.End (ZMod 2) M12Heart =>
      coordinates (f (M12Calculations.heartEquiv (Pi.single 0 1)))) ha
    change coordinates (m12HeartRepresentation originalA
      (M12Calculations.heartEquiv (Pi.single 0 1))) =
        coordinates (M12Calculations.heartEquiv (Pi.single 0 1)) at hv
    rw [M12Calculations.heartEquiv_apply, coordinates_toHeart] at hv
    change action m12GeneratorA (Pi.single 0 1) = Pi.single 0 1 at hv
    have hn : action m12GeneratorA (Pi.single 0 1) ≠ Pi.single 0 1 := by decide +kernel
    exact (hn hv).elim

/-- The full automorphism action is faithful. -/
theorem automorphismRepresentation_faithful :
    Function.Injective automorphismRepresentation := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have he : implementer a = LinearEquiv.refl _ _ := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) M12Heart => f v) ha
  apply MulEquiv.ext
  intro x
  apply heartRepresentation_faithful
  apply LinearMap.ext
  intro v
  have hx := implementer_spec a x v
  rw [he] at hx
  exact hx.symm

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
