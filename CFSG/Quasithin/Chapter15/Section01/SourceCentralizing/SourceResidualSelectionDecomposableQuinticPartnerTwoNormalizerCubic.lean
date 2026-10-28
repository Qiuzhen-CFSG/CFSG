module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSeedNormalizer
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The original seed normalizer has no moving cubic section action

The residual of the literal ambient normalizer of E centralizes E. Its
restricted action on the image of E therefore has two-group image. If an
actual normalizing element has cube acting trivially on F/D, that same
restricted action is trivial. This controls an actual lift and does not
identify an arbitrary quotient stabilizer with the seed normalizer.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v
variable {G : Type u} [Group G] [Finite G]

private theorem normalizer_cubic_fixed
    {H F D E : Subgroup G} {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (dF : BinaryConjugationSection H F D ρ)
    (hNH : normalizer (E : Set G) ≤ H)
    (hres : (pResidual 2 (normalizer (E : Set G))).map
      (normalizer (E : Set G)).subtype ≤ centralizer (E : Set G))
    (g : H) (hg : (g : G) ∈ normalizer (E : Set G)) (hc : ρ (g^3) = 1) :
    ∀ w ∈ dF.imageSpace E, ρ g w = w := by
  let N := normalizer (E : Set G)
  let f : N →* H := inclusion hNH
  let I : Subrepresentation (ρ.comp f) := {
    toSubmodule := dF.imageSpace E
    apply_mem_toSubmodule n w hw := dF.imageSpace_apply_mem E (f n) n.property w hw }
  let α := I.toRepresentation
  let q := α.asGroupHom.rangeRestrict
  have hkernel : pResidual 2 N ≤ q.ker := by
    intro n hn
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    obtain ⟨x,hx,he⟩ := (dF.mem_imageSpace_iff E w.val).mp w.property
    change ρ (f n) w.val = w.val
    rw [←he,←dF.equivariant]
    congr 2
    apply Subtype.ext
    have hcomm := hres (mem_map_of_mem N.subtype hn) x hx
    change (x : G) * (n : G) = (n : G) * (x : G) at hcomm
    change (n : G) * x * (n : G)⁻¹ = x
    rw [←hcomm,mul_inv_cancel_right]
  have hP : IsPGroup 2 α.asGroupHom.range :=
    ((pResidual_le_iff_isPGroup_quotient 2 q.ker).mp hkernel).of_equiv
      (QuotientGroup.quotientKerEquivOfSurjective q α.asGroupHom.rangeRestrict_surjective)
  let n : N := ⟨g,hg⟩
  have hcq : q n ^ 3 = 1 := by
    rw [←map_pow]
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ρ (g^3) w.val = w.val
    rw [hc]
    rfl
  have hq : q n = 1 := (hP.powEquiv (by decide : Nat.Coprime 2 3)).injective (by
    change q n ^ 3 = (1 : α.asGroupHom.range)^3
    simpa only [one_pow] using hcq)
  intro w hw
  have he := congrArg (fun a : α.asGroupHom.range => (a.val.val : I → I) ⟨w,hw⟩) hq
  exact congrArg Subtype.val he

/-- A literal normalizer lift with cubic canonical action fixes the original
seed image. The global residual control is derived from the original source. -/
theorem PreparedChosenModule.decomposable_five_partner_two_normalizer_cubic_fixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ)
        (g : Mc), (g : G) ∈ normalizer (E : Set G) → ρ (g^3) = 1 →
        ∀ w ∈ dF.imageSpace E, ρ g w = w := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  dsimp only
  intro W _ _ ρ dF g hg hc
  have hn := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).1
  have hr := (h.decomposable_five_partner_two_seed_normalizer
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).2
  exact normalizer_cubic_fixed ρ dF hn hr g hg hc

end CFSG.Quasithin.Chapter15.Section01
