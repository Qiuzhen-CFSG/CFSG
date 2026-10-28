module
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point

/-!
# The fixed-field centralizer in Baumeister's point parabolic

The selected involution is fourth-power Frobenius on the field of sixteen
elements. Its affine centralizer consists of the affine transformations of
its fixed field F₄ and that same involution. The even permutations of F₄
are exactly its affine transformations, giving the actual A₄ × C₂ map.

Small field checks identify the coefficients and the two possible linear
parts; group multiplication and transport to a faithful ambient image are
proved structurally. The resulting map supplies the first/third overlap
in Baumeister, *A geometry for groups of J₃-type* (2007), p.496.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.BaumeisterParabolics.PointCentralizer
open Subgroup
open SingerField hiding normalizer frobenius
abbrev AF := alternatingGroup F

def slope (p : AF) : Fˣ := Units.mk0 (p.val 1 - p.val 0) (by
  exact sub_ne_zero.mpr (fun h => one_ne_zero (p.val.injective h)))

private theorem affine_formula (p : AF) (x : F) :
    p.val x = p.val 0 + (slope p : F) * x := by
  revert p x
  decide +kernel

private theorem slope_mul (p q : AF) : slope (p*q) = slope p * slope q := by
  apply Units.ext
  change p.val (q.val 1) - p.val (q.val 0) = _
  rw [affine_formula p (q.val 1), affine_formula p (q.val 0)]
  change _ = (slope p : F) * (q.val 1 - q.val 0)
  ring

def affineWord (p : AF) : Model :=
  ⟨.ofAdd (algebraMap F K (p.val 0)),
    ⟨multiplication (Units.map (algebraMap F K).toMonoidHom (slope p)),
      (show torus ≤ SingerField.normalizer from le_sup_left) ⟨_,rfl⟩⟩⟩

private theorem affine_left (p q : AF) :
    (affineWord (p*q)).left = (affineWord p * affineWord q).left := by
  change Multiplicative.ofAdd (algebraMap F K (p.val (q.val 0))) =
    Multiplicative.ofAdd (algebraMap F K (p.val 0) +
      algebraMap F K (slope p : F) * algebraMap F K (q.val 0))
  rw [affine_formula p (q.val 0), map_add, map_mul]

private theorem affine_right (p q : AF) :
    (affineWord (p*q)).right = (affineWord p * affineWord q).right := by
  apply Subtype.ext
  change multiplication (Units.map _ (slope (p*q))) =
    multiplication (Units.map _ (slope p)) * multiplication (Units.map _ (slope q))
  rw [slope_mul, map_mul, map_mul]

def affineHom : AF →* Model where
  toFun := affineWord
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (algebraMap F K (0 : F)) = 1
      rw [map_zero]; rfl
    · apply Subtype.ext
      change multiplication (Units.map _ (slope 1)) = 1
      have hs : slope 1 = 1 := by apply Units.ext; simp [slope]
      rw [hs,map_one,map_one]
  map_mul' p q := by exact SemidirectProduct.ext (affine_left p q) (affine_right p q)

def flipHom : Multiplicative (ZMod 2) →* Model where
  toFun i := fieldElement ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change fieldElement ^ (i.toAdd + j.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    simpa only [fieldElement_order] using
      pow_mod_orderOf fieldElement (i.toAdd.val + j.toAdd.val)

private theorem linear_ext {a b : K ≃ₗ[F] K}
    (h1 : a 1 = b 1) (ht : a (⟨0,1⟩ : K) = b ⟨0,1⟩) : a=b := by
  apply LinearEquiv.ext
  intro x
  have hx : x = x.re • (1 : K) + x.im • (⟨0,1⟩ : K) := by
    revert x; decide +kernel
  rw [hx,map_add,map_add,map_smul,map_smul,map_smul,map_smul,h1,ht]

private theorem affine_commutes (p : AF) : Commute (affineHom p) fieldElement := by
  apply SemidirectProduct.ext
  · revert p; decide +kernel
  · apply Subtype.ext
    apply linear_ext
    · revert p; decide +kernel
    · revert p; decide +kernel

def centralizerHom : AF × Multiplicative (ZMod 2) →* Model :=
  affineHom.noncommCoprod flipHom (by
    intro p i
    exact (affine_commutes p).pow_right i.toAdd.val)

private theorem centralizer_kernel : ∀ x : AF × Multiplicative (ZMod 2),
    (centralizerHom x).left = 1 → (centralizerHom x).right.val 1 = 1 →
    (centralizerHom x).right.val (⟨0,1⟩ : K) = ⟨0,1⟩ → x = 1 := by
  decide +kernel

theorem centralizerHom_injective : Function.Injective centralizerHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  exact centralizer_kernel x (congrArg SemidirectProduct.left hx)
    (congrArg (fun x : Model => x.right.val 1) hx)
    (congrArg (fun x : Model => x.right.val (⟨0,1⟩ : K)) hx)

private def linearWord (u : Fˣ) (i : Multiplicative (ZMod 2)) : K ≃ₗ[F] K :=
  multiplication (Units.map (algebraMap F K).toMonoidHom u) *
    SingerField.frobenius ^ i.toAdd.val

private theorem fixed_field : ∀ t : K, star t = t → algebraMap F K t.re = t := by
  decide +kernel

private theorem affine_parameters : ∀ b : F, ∀ u : Fˣ,
    ∃ p : AF, p.val 0 = b ∧ slope p = u := by decide +kernel

private theorem right_parameters : ∀ c : Seventeen.Complement,
    complementHom c (star (1 : K)) = star (complementHom c 1) →
    complementHom c (star (⟨0,1⟩ : K)) = star (complementHom c (⟨0,1⟩ : K)) →
    ∃ (u : Fˣ) (i : Multiplicative (ZMod 2)),
      linearWord u i 1 = complementHom c 1 ∧
      linearWord u i (⟨0,1⟩ : K) = complementHom c (⟨0,1⟩ : K) := by
  decide +kernel

theorem centralizerHom_range : centralizerHom.range =
    centralizer ({fieldElement} : Set Model) := by
  apply le_antisymm
  · rintro _ ⟨⟨p,i⟩,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact ((affine_commutes p).mul_left (Commute.self_pow fieldElement i.toAdd.val).symm).eq
  · intro x hx
    have he := mem_centralizer_singleton_iff.mp hx
    have hL : star x.left.toAdd = x.left.toAdd := by
      have hh := congrArg SemidirectProduct.left he.symm
      change Multiplicative.ofAdd (0 + star x.left.toAdd) =
        Multiplicative.ofAdd (x.left.toAdd + x.right.val 0) at hh
      simpa only [zero_add, map_zero, add_zero, toAdd_ofAdd] using
        congrArg Multiplicative.toAdd hh
    obtain ⟨c,hc⟩ := complementEquiv.surjective x.right
    have hcV : complementHom c = x.right.val := congrArg Subtype.val hc
    have hR : complementHom c * SingerField.frobenius =
        SingerField.frobenius * complementHom c := by
      rw [hcV]
      exact congrArg (fun x : Model => x.right.val) he
    obtain ⟨u,i,hu,hi⟩ := right_parameters c
      (LinearEquiv.congr_fun hR 1) (LinearEquiv.congr_fun hR (⟨0,1⟩ : K))
    obtain ⟨p,hp,hs⟩ := affine_parameters x.left.toAdd.re u
    refine ⟨(p,i), SemidirectProduct.ext ?_ ?_⟩
    · have hi0 : ∀ i : Multiplicative (ZMod 2), (flipHom i).left = 1 := by
        decide +kernel
      change (affineHom p).left * action (affineHom p).right (flipHom i).left = _
      rw [hi0,map_one,mul_one]
      change Multiplicative.ofAdd (algebraMap F K (p.val 0)) = _
      rw [hp, fixed_field _ hL]
      rfl
    · apply Subtype.ext
      have hiR : (flipHom i).right.val = SingerField.frobenius ^ i.toAdd.val := by
        change ((SemidirectProduct.rightHom : Model →* SingerField.normalizer)
          (fieldElement ^ i.toAdd.val)).val = _
        rw [map_pow, Subgroup.coe_pow]
        rfl
      change multiplication (Units.map _ (slope p)) * (flipHom i).right.val = _
      rw [hs,hiR]
      exact (linear_ext hu hi).trans hcV

/-- The centralizer of the actual selected field involution in the point group. -/
def pointCentralizerEquiv : centralizer ({fieldElement} : Set Model) ≃*
    (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) := by
  let e : F ≃ Fin 4 := Fintype.equivFinOfCardEq Representation.SL2FourNatural.card_field
  exact (MulEquiv.subgroupCongr centralizerHom_range.symm).trans
    ((MonoidHom.ofInjective centralizerHom_injective).symm.trans
      ((Equiv.altCongrHom e).prodCongr (MulEquiv.refl _)))

variable {G H : Type*} [Group G] [Group H]

/-- Restrict a faithful map to the literal intersection with its image centralizer. -/
def imageCentralizerEquiv (j : H →* G) (hj : Function.Injective j) (f : H) :
    (j.range ⊓ centralizer ({j f} : Set G) : Subgroup G) ≃*
      centralizer ({f} : Set H) := by
  have he : (centralizer ({f} : Set H)).map j =
      j.range ⊓ centralizer ({j f} : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,rfl⟩, mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg j (mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨⟨y,rfl⟩,hy⟩
      refine ⟨y,mem_centralizer_singleton_iff.mpr (hj ?_),rfl⟩
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hy
  exact (MulEquiv.subgroupCongr he.symm).trans
    ((centralizer ({f} : Set H)).equivMapOfInjective j hj).symm

/-- The original point-image centralizer, with the chosen field involution. -/
def imagePointCentralizerEquiv (j : Model →* G) (hj : Function.Injective j) :
    (j.range ⊓ centralizer ({j fieldElement} : Set G) : Subgroup G) ≃*
      (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) :=
  (imageCentralizerEquiv j hj fieldElement).trans pointCentralizerEquiv

end Sporadic.Janko3.SourceRecognition.BaumeisterParabolics.PointCentralizer
