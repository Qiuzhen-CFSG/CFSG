module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionSeedNormalizer
import Theory.GroupTheory.PerfectSmallTwoAction
import Theory.GroupTheory.SolvableResidual
import Theory.Representation.BinaryConjugationSection.InvariantImages
import Theory.Representation.BinaryConjugationSection.QuadraticPair
import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Perfect seed stabilizers in the original quintic section

Every perfect subgroup of the actual section image lifts through the solvable
residual of Mc. That residual centralizes the normal order-four Uc. A lift
stabilizing the image of E normalizes E because Uc is contained in E. The
ambient seed-normalizer displacement theorem therefore makes the lift fix
E/Uc pointwise. The original section coordinates and chosen perfect subgroup
are retained throughout.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_image_lifts_centralizing_four
    {H U : Subgroup G} (hUH : U≤H) (hnU : H≤normalizer (U:Set G))
    (hcU : Nat.card U≤4) {D : Type*} [Group D]
    (f : H→*D) (hf : Function.Surjective f) (K : Subgroup D) [Group.IsPerfect K] :
    K≤((centralizer (U:Set G)).subgroupOf H).map f := by
  let : (U.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hnU
  have hc : Nat.card (U.subgroupOf H)≤4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv]
    exact hcU
  have hb := le_centralizer_of_isPerfect_of_card_le_four
    (solvableResidual H) (U.subgroupOf H) hc
  have hb' : solvableResidual H≤(centralizer (U:Set G)).subgroupOf H := by
    intro b hbmem u hu
    exact congrArg Subtype.val (hb hbmem ⟨u,hUH hu⟩ hu)
  have hm := map_mono (f:=f) hb'
  rw [map_solvableResidual_eq f hf] at hm
  exact (le_solvableResidual_of_isPerfect K).trans hm

private theorem perfect_section_seed_stabilizer_fixes
    {H F U E : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (dF : BinaryConjugationSection H F U ρ)
    (hUE : U≤E) (hEF : E≤F) (hnU : H≤normalizer (U:Set G))
    (hcU : Nat.card U≤4)
    (hcomm : ⁅normalizer (E:Set G)⊓centralizer (U:Set G),E⁆≤U)
    (K : Subgroup (Representation.BinaryOffender.actionImage ρ)) [Group.IsPerfect K] :
    dF.imageSpace E≤fixedSpace (Representation.BinaryOffender.imageRepresentation ρ)
      (K⊓subspaceStabilizer (Representation.BinaryOffender.imageRepresentation ρ)
        (dF.imageSpace E)) := by
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let f := Representation.BinaryOffender.actionHom ρ
  have hK := perfect_image_lifts_centralizing_four
    (dF.kernel_le.trans dF.section_le) hnU hcU f
    ρ.asGroupHom.rangeRestrict_surjective K
  intro v hv k
  obtain ⟨c,hc,hck⟩ := hK k.property.1
  have hstab : ∀ w, ρ c w∈dF.imageSpace E ↔ w∈dF.imageSpace E := by
    intro w
    have hh := k.property.2 w
    rw [←hck] at hh
    exact hh
  have hm (x:F) : (c:G)*(x:G)*(c:G)⁻¹∈E ↔
      ρ c (dF.coordinates x).toAdd∈dF.imageSpace E := by
    let y : F := ⟨(c:G)*(x:G)*(c:G)⁻¹,
      (mem_normalizer_iff.mp (dF.normalized c.property) x).mp x.property⟩
    have he := dF.coordinates_mem_imageSpace_iff_of_kernel_le E hUE y
    rw [dF.equivariant] at he
    exact he.symm
  have hcE : (c:G)∈normalizer (E:Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact (hm ⟨x,hEF hx⟩).mpr ((hstab _).mpr
        ((dF.coordinates_mem_imageSpace_iff_of_kernel_le E hUE _).mpr hx))
    · intro hx
      have hxF : x∈F := (mem_normalizer_iff.mp (dF.normalized c.property) x).mpr (hEF hx)
      exact (dF.coordinates_mem_imageSpace_iff_of_kernel_le E hUE ⟨x,hxF⟩).mp
        ((hstab _).mp ((hm ⟨x,hxF⟩).mp hx))
  have hvfix := dF.fixed_on_imageSpace_of_commutator_le
    (normalizer (E:Set G)⊓centralizer (U:Set G)) E hcomm c ⟨hcE,hc⟩ v hv
  change σ (k : Representation.BinaryOffender.actionImage ρ) v=v
  rw [←hck]
  exact hvfix

/-- In the same actual partner section, every perfect subgroup's setwise
stabilizer of the original marked plane fixes that plane pointwise. -/
theorem PreparedChosenModule.decomposable_five_partner_four_perfect_seed_stabilizer
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
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let F := conjugateSpanBy E (centralizer (Uc:Set G))
      ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F Uc ρ)
        (K : Subgroup (Representation.BinaryOffender.actionImage ρ)), Group.IsPerfect K →
        dF.imageSpace E≤fixedSpace (Representation.BinaryOffender.imageRepresentation ρ)
          (K⊓subspaceStabilizer (Representation.BinaryOffender.imageRepresentation ρ)
            (dF.imageSpace E)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  dsimp only
  intro W _ _ ρ dF K hK
  let := hK
  have hUE := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hc := h.decomposable_five_partner_four_seed_normalizer_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  exact perfect_section_seed_stabilizer_fixes ρ dF hUE (le_conjugateSpanBy _ _)
    (le_normalizer_conjugateSpanBy _ _) hcU.le hc K

end CFSG.Quasithin.Chapter15.Section01
