module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.CriticalImage
public import Theory.Representation.SymplecticFourOrthogonalCover.EmbeddedProjectionAction
/-!
# Coordinates for reciprocal critical actions

The marked ambient quotient is semilinear because it normalizes the natural
symplectic component. Restricting its original quotient map preserves the
literal opposite-seed centralizer kernel. Once a critical image is inner,
the component marking gives its natural action and retains this same kernel.

These interfaces assemble the two endpoints in MS93 (3.3), printed p.867.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource
open Representation.SymplecticFourOrthogonalCover
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer

theorem ambient_marking_semilinear
    {J V F : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (hF : Nat.card F=4) (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F))) :
    ∀ g : J, ∃ σ : F ≃+* F, ∀ c v,
      MovedSection.ambientAction s e g (c • v) = σ c • MovedSection.ambientAction s e g v := by
  have hcard : 2 < Nat.card F := by omega
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
      Subgroup.topEquiv
  intro g
  exact SymplecticNaturalNormalizer.exists_field_twist
    ⟨linearAction (MovedSection.ambientAction s e) g,
      SymplecticNaturalNormalizer.operator_mem_naturalNormalizer B hcard (e.groupEquiv.trans d)
        (MovedSection.ambientAction s e)
        (fun b v => MovedSection.ambientAction_component s e b v) g⟩

theorem restricted_kernel_of_mapped_centralizer
    {G D : Type*} [Group G] [Group D]
    (A B S : Subgroup G) (hAB : A ≤ B) (κ : B →* D)
    (hk : κ.ker.map B.subtype = B ⊓ centralizer (S : Set G)) :
    (κ.comp (inclusion hAB)).ker = (centralizer (S : Set G)).subgroupOf A := by
  ext x
  change κ (inclusion hAB x)=1 ↔ x.val ∈ centralizer (S : Set G)
  constructor
  · intro hx
    have hm : x.val ∈ κ.ker.map B.subtype := ⟨inclusion hAB x,hx,rfl⟩
    rw [hk] at hm
    exact hm.2
  · intro hx
    have hm : x.val ∈ κ.ker.map B.subtype := by rw [hk]; exact ⟨hAB x.property,hx⟩
    obtain ⟨y,hy,he⟩ := hm
    have hxy : y=inclusion hAB x := Subtype.ext he
    rwa [hxy] at hy

theorem ambient_marking_inner_apply
    {J V F A : Type*} [Group J] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J}
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (δ : A →* J) (β : A →* L (K := F))
    (he : ∀ x, (e.groupEquiv.symm (β x) : J)=δ x) (x : A) (v : Vector F) :
    MovedSection.ambientAction s e (δ x) v = (β x).val • v := by
  rw [←he x,MovedSection.ambientAction_component,e.groupEquiv.apply_symm_apply]
  rfl

theorem inner_model_kernel_eq
    {J V F A : Type*} [Group J] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J}
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (δ : A →* J) (β : A →* L (K := F))
    (he : ∀ x, (e.groupEquiv.symm (β x) : J)=δ x) :
    ((commutator (Sp F)).subtype.comp β).ker=δ.ker := by
  ext x
  change (β x).val=1 ↔ δ x=1
  constructor
  · intro hx
    have hb : β x=1 := Subtype.ext hx
    rw [←he x,hb,map_one]
    rfl
  · intro hx
    have hh : (e.groupEquiv.symm (β x) : J)=(e.groupEquiv.symm 1 : J) := by
      rw [map_one,he x,hx]
      rfl
    exact congrArg Subtype.val (e.groupEquiv.symm.injective (Subtype.ext hh))

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
