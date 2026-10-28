module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryKernel
public import Theory.Representation.ElementaryPerfectSplit

/-!
# The actual six-letter action on the original secondary module

Descend conjugation on the unchanged V_Y through the original coordinate
map KT to S6. Its full kernel remains X O₂(KT), and the chosen six-space
marking is kept. This constructs the secondary representation without
assuming its faithfulness, irreducibility, or natural-module type.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The scalar-trivial secondary representation is constructed on the
literal additive group of V_Y, through the same original six-space chart. -/
theorem original_tripleSix_central_closure_secondary_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    ∃ hr : IsPReduced 2 (V.subgroupOf M),
      letI := hr.elementary
      ∃ (hMU : M ≤ normalizer (U : Set G)) (f : Automizer U →* HexAutomorphisms),
        Function.Bijective f ∧
        (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property⟩) =
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
        (∀ (b : Automizer U) (u : U),
          (tripleSixPointCoordinates D a (b.val u)).toAdd =
            Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
        (let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
         let q := hexCoordinateSixHom.comp π
         Function.Surjective π ∧ π.ker = pCore 2 M ∧ Function.Surjective q ∧
         q.ker = (X.subgroupOf M) ⊔ pCore 2 M ∧
         ∃ σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (V.subgroupOf M)),
           ∀ (m : M) (v : Additive (V.subgroupOf M)),
             ((σ (q m) v).toMul : M) = m * (v.toMul : M) * m⁻¹) := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  have hr : IsPReduced 2 (V.subgroupOf M) :=
    (original_tripleSix_central_closure_scalar_fixed_module
      h structural D a z hz hzT hnot houter).2.2.2.2.1
  let := hr.elementary
  let := hr.normal
  obtain ⟨hMU,f,hf,hfk,hchart,hπ,hker,hqker,hcentral⟩ :=
    original_tripleSix_central_closure_secondary_kernel h structural D a z hz hzT hnot houter
  let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
  let q := hexCoordinateSixHom.comp π
  have hq : Function.Surjective q := hexCoordinateSix_surjective.comp hπ
  have hk : q.ker ≤ (MulAut.conjNormal : M →* MulAut (V.subgroupOf M)).ker := by
    intro m hm
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change m * (v : M) * m⁻¹ = v
    rw [←hcentral hm v v.property,mul_inv_cancel_right]
  let β : Equiv.Perm (Fin 6) →* MulAut (V.subgroupOf M) :=
    q.liftOfSurjective hq ⟨MulAut.conjNormal,hk⟩
  let σ := elementaryRepresentation (p := 2) β
  refine ⟨hr,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,?_⟩
  intro m v
  change ((β (q m)) v.toMul : M) = _
  dsimp only [β]
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

end CFSG.Quasithin.Chapter12.Section07
