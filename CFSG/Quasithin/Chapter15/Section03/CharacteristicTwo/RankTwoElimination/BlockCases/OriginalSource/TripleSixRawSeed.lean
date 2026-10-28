module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.TripleSixRawFixed
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction

/-!
# Embedding the first-choice seed in the literal moved section

Commutator generation places the original seed in [starV,L*]. If the
central projection is injective, its restriction embeds the seed in the
actual moved quotient and intertwines every component element normalizing
that seed. This retains the original inclusion and quotient maps.

Source: Aschbacher–Smith 15.3.21, printed p.1127, with B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]

theorem tripleSix_firstChoice_seed_moved
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L)
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hcomm : d.V = ⁅d.V,d.Yplus⁆) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      ∀ v : starV c.L d.R, ((v : (c.L ⊔ d.R : Subgroup G)) : G) ∈ d.V →
        Additive.ofMul v ∈ s.space.toSubmodule := by
  intro C J hCJ s v hv
  let A := c.L ⊔ d.R
  let K := c.L.subgroupOf A
  let H := d.Yplus.subgroupOf A
  let V := d.V.subgroupOf A
  have hLJ : c.L ≤ A := le_sup_left
  have hYJ : d.Yplus ≤ A := hYL.trans hLJ
  have hVJ : d.V ≤ A := hVW.trans (map_subtype_le _)
  have hVS : V ≤ starV c.L d.R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hVW hx
    exact (show y=x from Subtype.ext he) ▸ hy
  have heq : V=⁅V,H⁆ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVJ,map_subgroupOf_eq_of_le hYJ]
    exact hcomm
  have hVC : V ≤ ⁅starV c.L d.R,K⁆ := by
    rw [heq]
    exact commutator_mono hVS (comap_mono hYL)
  rw [s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hCJ]
  change Additive.ofMul v ∈ subspaceCommutator (starRepresentation c.L d.R) ⊤ C
  change Additive.ofMul v ∈ subspaceCommutator
    (NormalElementaryQuotient.representation (starV c.L d.R)
      (QuotientGroup.mk' (starKernel c.L d.R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) ⊤ (K.map (QuotientGroup.mk' (starKernel c.L d.R)))
  rw [←NormalElementaryQuotient.commutatorSpace_eq (starV c.L d.R)
    (QuotientGroup.mk' (starKernel c.L d.R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) K]
  exact hVC hv



/-- The actual seed injects equivariantly into the canonical moved quotient. -/
theorem tripleSix_seed_embedding
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L)
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hcomm : d.V = ⁅d.V,d.Yplus⁆) :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J)),
      Function.Injective s.central.toSubmodule.mkQ →
      ∃ j : d.V → (s.space.toSubmodule ⧸ s.central.toSubmodule),
        Function.Injective j ∧ j 1 = 0 ∧
        ∀ (l : c.L) (hl : (l : G) ∈ normalizer (d.V : Set G)) (v : d.V),
          j (d.V.normalizerMonoidHom ⟨l,hl⟩ v) =
            s.central.quotientRepresentation (((subgroupOfEquivOfLe hCJ).symm (toStarImage c.L d.R l)) : J) (j v) := by
  intro C J hCJ s hp
  have hVJ : d.V ≤ c.L ⊔ d.R := hVW.trans (map_subtype_le _)
  have hvW (v : d.V) : (⟨v,hVJ v.property⟩ : (c.L ⊔ d.R : Subgroup G)) ∈ starV c.L d.R := by
    obtain ⟨w,hw,he⟩ := hVW v.property
    exact (show w = ⟨v,hVJ v.property⟩ from Subtype.ext he) ▸ hw
  let f : d.V → s.space.toSubmodule := fun v => ⟨Additive.ofMul ⟨⟨v,hVJ v.property⟩,hvW v⟩,
    tripleSix_firstChoice_seed_moved d c hYL hVW hcomm hCJ s _ v.property⟩
  let j : d.V → (s.space.toSubmodule ⧸ s.central.toSubmodule) := fun v => s.central.toSubmodule.mkQ (f v)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun w : s.space.toSubmodule => ((w.val.toMul : (c.L ⊔ d.R : Subgroup G)) : G)) he
  refine ⟨j,hp.comp hf,?_,?_⟩
  · change s.central.toSubmodule.mkQ (f 1)=0
    have he : f 1=(0 : s.space.toSubmodule) := by
      change (⟨Additive.ofMul ⟨(1 : (c.L ⊔ d.R : Subgroup G)), _⟩, _⟩ : s.space.toSubmodule) = 0
      apply Subtype.ext
      apply Additive.toMul.injective
      simp
    rw [he,map_zero]
  · intro l hl v
    change s.central.toSubmodule.mkQ (f (d.V.normalizerMonoidHom ⟨l,hl⟩ v)) =
      s.central.toSubmodule.mkQ
        (s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm (toStarImage c.L d.R l)) : J) (f v))
    apply congrArg s.central.toSubmodule.mkQ
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change _ = (starRepresentation c.L d.R
      (QuotientGroup.mk' (starKernel c.L d.R) ⟨l,mem_sup_left l.property⟩) (f v).val).toMul.val
    rw [starRepresentation_apply]
    rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
