module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ShortCentralizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.Fusion

/-!
# Model involution fusion in the original prepared Ree pair

The inverse full-normalizer markings agree on their literal entire
intersection. The connected native fixed-graph argument therefore
transports every involution conjugacy between extension endpoints to the
original ambient group. In particular it applies to the whole common
normalizer map carrying the original Sylow. Conversely every ambient
involution has a Sylow representative whose extension image is an actual
native Ree involution, since the extension outer quotient is odd.

These statements hold for every constructed marking, so the same marking
retains all previous Sylow, endpoint, overlap and centralizer comparisons.
The source-input constructor retains both comparison orientations and the
original equation 2m+1=n. No ambient generation or recognition is assumed.
Two-root-class exhaustion, the reverse fusion implication and the full
ambient short-root centralizer remain for F.4.35,42–43.
Source: Aschbacher–Smith 5.3.1–3 and F.4.30,35,40–43,
printed pp.658–659,290–296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
variable {G : Type*} [Group G]

/-- The inverse of the actual full endpoint marking, followed by its original ambient inclusion. -/
@[expose] def FullNormalizerMarking.endpointInverse {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β)
    (i : Bool) : D.extension.family i →* G :=
  match i with
  | false => (normalizer (L : Set G)).subtype.comp
      (D.full.left.symm.toMonoidHom.comp
        (subgroupOfEquivOfLe D.extension.left_le).toMonoidHom)
  | true => (normalizer (K : Set G)).subtype.comp
      (D.full.right.symm.toMonoidHom.comp
        (subgroupOfEquivOfLe D.extension.right_le).toMonoidHom)

/-- These are compatible on the entire extension overlap. -/
theorem FullNormalizerMarking.endpointInverse_compatible {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β)
    (x : D.extension.carrier) (h₀ : x ∈ D.extension.family false)
    (h₁ : x ∈ D.extension.family true) :
    D.endpointInverse false ⟨x,h₀⟩ = D.endpointInverse true ⟨x,h₁⟩ := by
  let b : D.extension.middle := ⟨x.val,⟨h₀,h₁⟩⟩
  have hl := congrArg Subtype.val (D.full.symm.left_commutes b)
  have hr := congrArg Subtype.val (D.full.symm.right_commutes b)
  exact hl.trans hr.symm

/-- The inverse endpoint maps recover the original left-normalizer elements literally. -/
theorem FullNormalizerMarking.endpointInverse_left {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β)
    (x : normalizer (L : Set G)) :
    D.endpointInverse false ⟨D.leftToCarrier x,(D.full.left x).property⟩ = x.val := by
  change (D.full.left.symm (D.full.left x)).val = x.val
  rw [D.full.left.symm_apply_apply]

/-- The inverse right endpoint likewise recovers its original ambient element. -/
theorem FullNormalizerMarking.endpointInverse_right {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β)
    (x : normalizer (K : Set G)) :
    D.endpointInverse true ⟨D.rightToCarrier x,(D.full.right x).property⟩ = x.val := by
  change (D.full.right.symm (D.full.right x)).val = x.val
  rw [D.full.right.symm_apply_apply]

/-- The whole-overlap map agrees with the left endpoint map. -/
theorem FullNormalizerMarking.middleToCarrier_left {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β)
    (x : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    D.middleToCarrier x = D.leftToCarrier (inclusion inf_le_left x) := by
  apply Subtype.ext
  exact (congrArg Subtype.val (D.full.left_commutes x)).symm

private theorem involution_sylow_representative [Finite G] (T : Sylow 2 G)
    (x : G) (hx : orderOf x = 2) :
    ∃ y : T, orderOf y.val = 2 ∧ IsConj x y.val := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  have hy : (MulAut.conj g) x ∈ T := by
    rw [←hg]
    exact ⟨x,hS (mem_zpowers x),rfl⟩
  exact ⟨⟨(MulAut.conj g) x,hy⟩,(MulEquiv.orderOf_eq _ x).trans hx,
    isConj_iff.mpr ⟨g,rfl⟩⟩

variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))

include d h hp
/-- Every involution fusion between the full extension endpoints holds in the original ambient group under the literal inverse normalizer maps. -/
theorem Preparation.ree_extension_involution_fusion
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    {i j : Bool} (x : D.extension.family i) (y : D.extension.family j)
    (hx : orderOf x.val = 2) (hxy : IsConj x.val y.val) :
    IsConj (D.endpointInverse i x) (D.endpointInverse j y) := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  exact GeneralReeFour.extension_involution_fusion D.extension hm D.endpointInverse
    D.endpointInverse_compatible x y hx hxy

/-- The involution specialization of F.4.30 on the literal full common-normalizer marking, hence on the original Sylow. -/
theorem Preparation.ree_middle_involution_fusion
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (hx : orderOf x.val = 2)
    (hxy : IsConj (D.middleToCarrier x) (D.middleToCarrier y)) :
    IsConj x.val y.val := by
  rw [D.middleToCarrier_left,D.middleToCarrier_left] at hxy
  let xL := inclusion (show normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
    normalizer (L : Set G) from inf_le_left) x
  let yL := inclusion (show normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
    normalizer (L : Set G) from inf_le_left) y
  have hx' : orderOf (D.leftToCarrier xL) = 2 := by
    rw [orderOf_injective D.leftToCarrier D.leftToCarrier_injective,←Subgroup.orderOf_coe]
    exact hx
  have hh := d.ree_extension_involution_fusion h hp m D
    (i := false) (j := false)
    ⟨D.leftToCarrier xL,(D.full.left xL).property⟩
    ⟨D.leftToCarrier yL,(D.full.left yL).property⟩ hx' hxy
  rw [D.endpointInverse_left,D.endpointInverse_left] at hh
  exact hh

include hH he
/-- Every ambient involution has a representative in the original common normalizer marked by an actual native Ree involution. -/
theorem Preparation.ree_involution_native_representative
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x : G) (hx : orderOf x = 2) :
    ∃ (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G)) (t : ReeF4.Model m),
      y.val ∈ (T : Subgroup G) ∧ orderOf t = 2 ∧ IsConj x y.val ∧
      D.middleToCarrier y = D.extension.baseHom t := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  obtain ⟨_,hTL,hTK,_⟩ := d.ree_full_sylow h hH hp m he
  obtain ⟨u,hu,huconj⟩ := involution_sylow_representative T x hx
  let y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) :=
    ⟨u.val,⟨L.le_normalizer (hTL u.property),(residual H).le_normalizer (hTK u.property)⟩⟩
  have hi : Function.Injective D.middleToCarrier :=
    (inclusion_injective (inf_le_left.trans D.extension.left_le)).comp D.full.middle.injective
  have hy : orderOf (D.middleToCarrier y) = 2 :=
    (orderOf_injective _ hi y).trans ((Subgroup.orderOf_coe y).symm.trans hu)
  obtain ⟨t,ht,hyt⟩ := GeneralReeFour.extension_involution_native D.extension hm _ hy
  exact ⟨y,t,u.property,ht,huconj,hyt.symm⟩

/-- Both original orientations supply the actual full marking and its model-to-ambient involution fusion. -/
theorem Preparation.ree_full_extension_fusion :
    2*m+1 = n ∧ 0 < m ∧
    ∃ D : ReeNormalizerMarking L (residual H) (sourceS L H) m,
      (∀ (i j : Bool) (x : D.extension.family i) (y : D.extension.family j),
        orderOf x.val = 2 → IsConj x.val y.val →
          IsConj (D.endpointInverse i x) (D.endpointInverse j y)) ∧
      ∀ x : G, orderOf x = 2 →
        ∃ (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
          (t : ReeF4.Model m),
          y.val ∈ (T : Subgroup G) ∧ orderOf t = 2 ∧ IsConj x y.val ∧
          D.middleToCarrier y = D.extension.baseHom t := by
  obtain ⟨hn,hm,⟨D⟩⟩ := d.ree_full_normalizer_marking h hH hp m he
  exact ⟨hn,hm,D,
    fun _ _ x y hx hxy => d.ree_extension_involution_fusion h hp m D x y hx hxy,
    fun x hx => d.ree_involution_native_representative h hH hp m he D x hx⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
