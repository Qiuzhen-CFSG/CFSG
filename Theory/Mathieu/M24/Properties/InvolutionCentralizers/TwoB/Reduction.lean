module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoB.Marker
public import Theory.GroupTheory.SemidirectProductTranslationCentralizer
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The marked M₂₄ centralizer from its sextet placement and vector stabilizer

The native affine embedding identifies a full-weight translation centralizer
inside the sextet stabilizer. If its entire ambient centralizer preserves
that sextet, the identification is onto. The literal projection to the
hexacode vector stabilizer then has a normal elementary kernel of order 64,
with explicit binary coordinates and a self-centralizing action.

An isomorphism of that actual vector stabilizer with S₅ finishes the exact
sequence requested by Aschbacher–Smith 16.1.5(7), printed p.1171. Ambient
placement and the S₅ identification are explicit independent obligations;
this conditional reduction does not assert the unconditional source table.
The same literal kernel discharges its component-exclusion input.
-/

@[expose] public section
open Atlas.Codes Subgroup SemidirectProduct
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoB
open Theory.GroupTheory
noncomputable section

abbrev affineCentralizer := TranslationCentralizer.centralizer hexAffineAction vector
abbrev actors := TranslationCentralizer.actors hexAffineAction vector

def toNativeCentralizer : affineCentralizer →* nativeCentralizer :=
  (nativeEmbedding.comp affineCentralizer.subtype).codRestrict _ (by
    intro x
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change nativeEmbedding x.val * nativeEmbedding (inl vector) =
      nativeEmbedding (inl vector) * nativeEmbedding x.val
    rw [← map_mul, ← map_mul]
    exact congrArg nativeEmbedding (Subgroup.mem_centralizer_singleton_iff.mp x.property))

theorem toNativeCentralizer_bijective
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    Function.Bijective toNativeCentralizer := by
  constructor
  · intro x y h
    have he : nativeEmbedding x.val = nativeEmbedding y.val :=
      congrArg (fun z : nativeCentralizer => z.val) h
    exact Subtype.ext (nativeEmbedding_injective he)
  · intro g
    let x := nativeAffineEquiv.symm ⟨g.val, hplace g.property⟩
    have hx : nativeEmbedding x = g.val :=
      congrArg Subtype.val (nativeAffineEquiv.apply_symm_apply _)
    have hxc : x ∈ affineCentralizer := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply nativeEmbedding_injective
      rw [map_mul, map_mul, hx]
      exact Subgroup.mem_centralizer_singleton_iff.mp g.property
    exact ⟨⟨x,hxc⟩, Subtype.ext hx⟩

def markedAffineEquiv
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    centralizer2B ≃* affineCentralizer :=
  markedCentralizerEquiv.trans
    (MulEquiv.ofBijective toNativeCentralizer (toNativeCentralizer_bijective hplace)).symm

def elementaryEquiv : (Fin 6 → Multiplicative (ZMod 2)) ≃* Multiplicative hexacode :=
  (MulEquiv.funMultiplicative (Fin 6) (ZMod 2)).symm.trans
    (hexFlatParameters.trans hexEquiv).toAddEquiv.toMultiplicative

theorem affineAction_injective : Function.Injective hexAffineAction := by
  intro g h he
  apply hexAction_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun he (Multiplicative.ofAdd v))

/-- The literal projection of the marked centralizer to the vector stabilizer. -/
def projection (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    centralizer2B →* actors :=
  (TranslationCentralizer.projection hexAffineAction vector).comp
    (markedAffineEquiv hplace).toMonoidHom

theorem projection_surjective (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    Function.Surjective (projection hplace) :=
  (TranslationCentralizer.projection_surjective hexAffineAction vector).comp
    (markedAffineEquiv hplace).surjective

def kernelEquiv (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    (Fin 6 → Multiplicative (ZMod 2)) ≃* (projection hplace).ker :=
  (elementaryEquiv.trans (TranslationCentralizer.kernelEquiv hexAffineAction vector)).trans
    { toFun := fun u => ⟨(markedAffineEquiv hplace).symm u.val, by
        change TranslationCentralizer.projection hexAffineAction vector
          ((markedAffineEquiv hplace) ((markedAffineEquiv hplace).symm u.val)) = 1
        rw [MulEquiv.apply_symm_apply]
        exact u.property⟩
      invFun := fun u => ⟨markedAffineEquiv hplace u.val, u.property⟩
      left_inv := fun u => Subtype.ext ((markedAffineEquiv hplace).apply_symm_apply _)
      right_inv := fun u => Subtype.ext ((markedAffineEquiv hplace).symm_apply_apply _)
      map_mul' := fun u v => Subtype.ext (map_mul (markedAffineEquiv hplace).symm _ _) }

theorem kernel_card (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    Nat.card (projection hplace).ker = 64 := by
  rw [← Nat.card_congr (kernelEquiv hplace).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem kernel_elementary (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    IsElementaryAbelian 2 (projection hplace).ker := by
  have hp (u : (projection hplace).ker) : u ^ 2 = 1 := by
    obtain ⟨v,rfl⟩ := (kernelEquiv hplace).surjective u
    have hs : ∀ t : Multiplicative (ZMod 2), t ^ 2 = 1 := by decide +kernel
    rw [← map_pow, show v ^ 2 = 1 from funext (fun i => hs (v i)), map_one]
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
  intro x y
  obtain ⟨u,rfl⟩ := (kernelEquiv hplace).surjective x
  obtain ⟨v,rfl⟩ := (kernelEquiv hplace).surjective y
  rw [← map_mul, ← map_mul, mul_comm]

theorem kernel_selfCentralizing
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    Subgroup.centralizer ((projection hplace).ker : Set centralizer2B) ≤
      (projection hplace).ker := by
  intro x hx
  apply TranslationCentralizer.kernel_selfCentralizing hexAffineAction vector
    affineAction_injective
  intro u hu
  have hh := hx ((markedAffineEquiv hplace).symm u) (by
    change TranslationCentralizer.projection hexAffineAction vector
      ((markedAffineEquiv hplace) ((markedAffineEquiv hplace).symm u)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact hu)
  change u * markedAffineEquiv hplace x = markedAffineEquiv hplace x * u
  simpa only [map_mul, MulEquiv.apply_symm_apply] using
    congrArg (markedAffineEquiv hplace) hh

/-- The exact requested extension follows from the two concrete geometric inputs. -/
def extensionOfGeometry
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet)
    (q : actors ≃* Equiv.Perm (Fin 5)) :
    GroupExtension (Fin 6 → Multiplicative (ZMod 2)) centralizer2B (Equiv.Perm (Fin 5)) where
  inl := (projection hplace).ker.subtype.comp (kernelEquiv hplace).toMonoidHom
  rightHom := q.toMonoidHom.comp (projection hplace)
  inl_injective := (projection hplace).ker.subtype_injective.comp (kernelEquiv hplace).injective
  rightHom_surjective := q.surjective.comp (projection_surjective hplace)
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      change q (projection hplace ((kernelEquiv hplace v).val)) = 1
      rw [show projection hplace ((kernelEquiv hplace v).val) = 1 from
        (kernelEquiv hplace v).property, map_one]
    · intro hx
      have hk : x ∈ (projection hplace).ker := by
        apply q.injective
        exact hx.trans (map_one q).symm
      obtain ⟨v,hv⟩ := (kernelEquiv hplace).surjective ⟨x,hk⟩
      exact ⟨v,congrArg Subtype.val hv⟩

/-- The extension uses the same literal kernel whose action was calculated above. -/
theorem extensionOfGeometry_range
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet)
    (q : actors ≃* Equiv.Perm (Fin 5)) :
    (extensionOfGeometry hplace q).inl.range = (projection hplace).ker := by
  rw [(extensionOfGeometry hplace q).range_inl_eq_ker_rightHom]
  ext x
  change q (projection hplace x) = 1 ↔ projection hplace x = 1
  exact q.map_eq_one_iff

theorem extensionOfGeometry_selfCentralizing
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet)
    (q : actors ≃* Equiv.Perm (Fin 5)) :
    Subgroup.centralizer ((extensionOfGeometry hplace q).inl.range : Set centralizer2B) ≤
      (extensionOfGeometry hplace q).inl.range := by
  rw [extensionOfGeometry_range]
  exact kernel_selfCentralizing hplace

/-- The same actual kernel supplies the component-exclusion input to the table. -/
theorem exists_normal_selfCentralizing_two_subgroup
    (hplace : nativeCentralizer ≤ sextetStabilizer standardSextet) :
    ∃ Q : Subgroup centralizer2B,
      Q.Normal ∧ IsPGroup 2 Q ∧ Subgroup.centralizer (Q : Set centralizer2B) ≤ Q :=
  ⟨(projection hplace).ker, inferInstance,
    (kernel_elementary hplace).isPGroup 2 _, kernel_selfCentralizing hplace⟩

end
end Sporadic.Mathieu.M24InvolutionCentralizers.TwoB
