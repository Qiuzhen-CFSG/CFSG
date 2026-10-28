module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Assembly.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry

/-!
# Fixed dimensions and codimensions on the original tensor module

The canonical scalar-extension map and Noether–Deuring descent construct a
marked equivalence from the original component module to the Hermitian model.
For each outer involution, normalize this equivalence by an actual symplectic
conjugator. The involution then becomes transposition, and the literal native
intersection of an elementary actor embeds in the field centralizer.

Fixed vectors inject into the model common-fixed space. The model's bounds
therefore give codimension at least 8s, strictly greater at maximal rank,
including s = 1. All scalar-extension, transport and model-geometry premises
are discharged here. No natural-plus-graph representation is substituted.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
noncomputable section
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
  [Field F] [Algebra (SchurField (ρ.comp L.subtype)) F] [Finite F] [Algebra (ZMod 2) F]

def originalEquiv {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) :
    (Representation.endFieldRep (ρ.comp L.subtype)) ≃ₗ
      (Model.action h.sigma h.sigma_involutive).comp h.groupEquiv.toMonoidHom :=
  Classical.choice (Transport.original_equiv (ρ.comp L.subtype) h
    (Model.Geometry.eM h.sigma h.sigma_involutive h.extension_degree h.sigma_ne)
    (Model.Geometry.eM_intertwines h.sigma h.sigma_involutive h.extension_degree h.sigma_ne))

def normalizedEquiv {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) : V ≃ₗ[ZMod 2] Model.Space h.sigma h.sigma_involutive :=
  (Representation.asModuleEquiv (ρ.comp L.subtype)).symm.trans
    (((originalEquiv ρ L h).toLinearEquiv.trans
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((Model.action h.sigma h.sigma_involutive).asGroupHom c⁻¹))).restrictScalars (ZMod 2))

omit [Finite G] [L.Normal] in
lemma normalizedEquiv_component {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) (g : L) (v : V) :
    normalizedEquiv ρ L h c (ρ g.val v) =
      Model.action h.sigma h.sigma_involutive (c⁻¹ * h.groupEquiv g * c)
        (normalizedEquiv ρ L h c v) := by
  have hi := (originalEquiv ρ L h).isIntertwining g
    ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm v)
  change originalEquiv ρ L h ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm (ρ g.val v)) =
    Model.action h.sigma h.sigma_involutive (h.groupEquiv g)
      (originalEquiv ρ L h ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm v)) at hi
  change Model.action h.sigma h.sigma_involutive c⁻¹
    (originalEquiv ρ L h ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm (ρ g.val v))) =
    Model.action h.sigma h.sigma_involutive (c⁻¹ * h.groupEquiv g * c)
      (Model.action h.sigma h.sigma_involutive c⁻¹
        (originalEquiv ρ L h ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm v)))
  rw [hi]
  simp only [map_mul, Module.End.mul_apply, Representation.self_inv_apply]

lemma exists_normalized {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    ∃ c : Sp F, ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v) := by
  obtain ⟨c, hc⟩ := Transport.outer_operator_of_equiv ρ L hS hs h (originalEquiv ρ L h) t ht hout
  refine ⟨c, fun v => ?_⟩
  change Model.action h.sigma h.sigma_involutive c⁻¹
      (originalEquiv ρ L h ((Representation.asModuleEquiv (ρ.comp L.subtype)).symm (ρ t v))) = _
  rw [hc, Representation.inv_self_apply]
  rfl

variable {ρ L}

def fixedEquiv {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) :
    fixedSpace ρ (zpowers t) ≃ₗ[ZMod 2] Model.fieldFixed h.sigma h.sigma_involutive where
  toFun v := ⟨normalizedEquiv ρ L h c v.val, by
    change Model.fieldSwap h.sigma h.sigma_involutive _ - _ = 0
    rw [← hc, (mem_fixedSpace_zpowers_iff ρ t v.val).mp v.property, LinearMap.id_apply, sub_self]⟩
  invFun X := ⟨(normalizedEquiv ρ L h c).symm X.val, by
    rw [mem_fixedSpace_zpowers_iff]
    apply (normalizedEquiv ρ L h c).injective
    rw [hc, LinearEquiv.apply_symm_apply]
    exact sub_eq_zero.mp X.property⟩
  left_inv v := Subtype.ext ((normalizedEquiv ρ L h c).symm_apply_apply v.val)
  right_inv X := Subtype.ext ((normalizedEquiv ρ L h c).apply_symm_apply X.val)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

variable (ρ L)
theorem outer_fixed_finrank {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 10 * s := by
  obtain ⟨c, hc⟩ := exists_normalized ρ L hS hs h t ht hout
  rw [(fixedEquiv h t c hc).finrank_eq]
  exact Model.Geometry.finrank_fieldFixed_binary h.sigma h.sigma_involutive
    h.extension_degree h.sigma_ne h.schur_card
end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
open Model.Geometry
noncomputable section
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
  [Field F] [Algebra (SchurField (ρ.comp L.subtype)) F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite G] [L.Normal] in
theorem model_action_faithful {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) :
    Function.Injective (Model.action h.sigma h.sigma_involutive) := by
  intro a b hab
  apply h.groupEquiv.symm.injective
  apply Subtype.ext
  apply hS.faithful
  ext v
  apply (normalizedEquiv ρ L h 1).injective
  have hi (g : Sp F) := normalizedEquiv_component ρ L h 1 (h.groupEquiv.symm g) v
  simp only [MulEquiv.apply_symm_apply, inv_one, one_mul, mul_one] at hi
  rw [hi, hi, hab]

omit [Finite G] [L.Normal] in
theorem normalized_centralizer {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (g : L) (hg : g.val * t = t * g.val) :
    nativeMark ρ L h c g ∈ centralizer h.sigma := by
  rw [MulAut.mem_fixedSubgroup]
  apply model_action_faithful ρ L hS h
  apply LinearMap.ext
  intro X
  have hi (v : V) : normalizedEquiv ρ L h c (ρ g.val v) =
      Model.action h.sigma h.sigma_involutive (nativeMark ρ L h c g)
        (normalizedEquiv ρ L h c v) := by
    simpa only [nativeMark, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv] using
      normalizedEquiv_component ρ L h c g v
  have hswap (Y : Model.Space h.sigma h.sigma_involutive) :
      Model.fieldSwap h.sigma h.sigma_involutive
        (Model.action h.sigma h.sigma_involutive (nativeMark ρ L h c g) Y) =
      Model.action h.sigma h.sigma_involutive (nativeMark ρ L h c g)
        (Model.fieldSwap h.sigma h.sigma_involutive Y) := by
    obtain ⟨v, rfl⟩ := (normalizedEquiv ρ L h c).surjective Y
    rw [← hi, ← hc, ← hc, ← hi]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg]
  obtain ⟨Y, rfl⟩ := (Model.fieldSwap h.sigma h.sigma_involutive).surjective X
  simpa only [Model.fieldSwap_action] using hswap Y

omit [Finite G] [L.Normal] in
theorem nativeActor_le_of_normalized {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (A : Subgroup G) (hA : IsElementaryTwo A) (htA : t ∈ A) :
    nativeActor ρ L h c A ≤ centralizer h.sigma := by
  let : IsElementaryAbelian 2 A := hA.2
  rintro x ⟨g, hg, rfl⟩
  apply normalized_centralizer ρ L hS h t c hc g
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm
    (⟨g.val, hg⟩ : A) ⟨t, htA⟩)

def commonFixedMap {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (A : Subgroup G) (htA : t ∈ A) :
    fixedSpace ρ A →ₗ[ZMod 2]
      Model.commonFixed h.sigma h.sigma_involutive (nativeActor ρ L h c A) where
  toFun v := ⟨normalizedEquiv ρ L h c v.val, by
    constructor
    · change Model.fieldSwap h.sigma h.sigma_involutive _ - _ = 0
      rw [← hc, show ρ t v.val = v.val from v.property ⟨t, htA⟩,
        LinearMap.id_apply, sub_self]
    · rintro ⟨b, g, hg, rfl⟩
      change Model.action h.sigma h.sigma_involutive (nativeMark ρ L h c g)
        (normalizedEquiv ρ L h c v.val) = _
      have hi := normalizedEquiv_component ρ L h c g v.val
      rw [show ρ g.val v.val = v.val from v.property ⟨g.val, hg⟩] at hi
      simpa only [nativeMark, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv] using hi.symm⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

omit [Finite G] [L.Normal] in
lemma commonFixedMap_injective {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (A : Subgroup G) (htA : t ∈ A) :
    Function.Injective (commonFixedMap ρ L h t c hc A htA) := by
  intro v w hvw
  exact Subtype.ext ((normalizedEquiv ρ L h c).injective (congrArg Subtype.val hvw))

theorem proper_outer_codimension {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) (hproper : zpowers t < A) :
    8 * s ≤ fixedCodim ρ A ∧ (rank A = 3 * s + 1 → 8 * s < fixedCodim ρ A) := by
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  obtain ⟨c, hc⟩ := exists_normalized ρ L hS hs h t ht hout
  have htA := hproper.le (mem_zpowers t)
  have hB := nativeActor_le_of_normalized ρ L hS h t c hc A hA htA
  have hBne := nativeActor_ne_bot ρ L hS hs h c A hA t ht hout hproper
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (commonFixedMap_injective ρ L h t c hc A htA)
  have hsum := fixedCodim_add_finrank ρ A
  rw [h.binary_finrank] at hsum
  have hfix := Model.Geometry.finrank_commonFixed_binary_le h.sigma h.sigma_involutive
    h.extension_degree h.sigma_ne h.schur_card _ hB hBne
  constructor
  · omega
  · intro hr
    have hstrict := Model.Geometry.finrank_commonFixed_binary_lt_of_card_cube
      h.sigma h.sigma_involutive h.extension_degree h.sigma_ne h.schur_card _ hB hBne
      (nativeActor_card_cube ρ L hS hs h c A hA t htA hout hr)
    omega
end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
