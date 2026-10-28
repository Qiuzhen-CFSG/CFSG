module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels

/-!
# Assemble the centralizing branch of 15.3.31

The inputs are the surviving C.1.32/C.1.34 module configurations, with
actual quotient and coefficient isomorphisms, and the marked parabolic
P = M ∩ L = N_L(V₂). Its O^{3′} residual is Y₊. These earlier classification
and marking inputs belong to the parent source assembly. They contain no
condition on D = C_I(Y₊), cocycle detection or centralizer recognition.

The block and linear model constructors prove faithful coefficient actions,
elementary Z(Q), and detection of every cocycle on the marked residual.
The three-subgroup argument puts [D,L] in Z(Q); the checked square argument
gives elementary D⁺ and trivial Frattini subgroup. Commutator cocycles then
kill D⁺, including its inner central automorphisms. Both natural summands
in C.1.34(2) use the same actor marking. The concrete calculations bypass
I.2.3, whose list does not include L₃(2), and retain the universal-dual-cover
orientation established in `Cocycles` and `Embedding`.

The final application combines C_I(Y₊) = C_I(L) with the actual V₁ and
normalizer conclusions of 15.3.29 to exclude this centralizing branch.
It does not assert the earlier classifications or the noncentral branch.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.31, printed p.1132 (PDF p.1149); C.1.13, C.1.31--34, B.4.8,
I.1.5--6 and I.2.3.
-/

@[expose] public section

open Subgroup Representation

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover

variable {G : Type*} [Group G]

/-- Exactly the coefficient and parabolic data consumed from the surviving
MS alternatives. The block images use the original quotient marking; the
linear cases mark E inside a genuine natural constituent of the full center.
Unneeded layers of C.1.34(3) may be retained by the caller. -/
inductive MarkedConfiguration (L E P : Subgroup G) : Prop
  | alternating
      (short : ChapterC.IsShort L)
      (model : ChapterC.BlockModuleModel L
        (BlockModels.multiplicativeAction BlockModels.Alternating.action))
      (plane : Submodule (ZMod 2) BlockModels.Alternating.Coefficients)
      (dimension : Module.finrank (ZMod 2) plane = 2)
      (invariant : ∀ g ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.T0,
        plane.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = plane)
      (parabolic : (P.subgroupOf L).map
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
          BlockModels.planeStabilizer BlockModels.Alternating.action plane)
  | g2
      (short : ChapterC.IsShort L)
      (model : ChapterC.BlockModuleModel L
        (BlockModels.multiplicativeAction BlockModels.G2.action))
      (parabolic : (P.subgroupOf L).map
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
          BlockModels.planeStabilizer BlockModels.G2.action BlockModels.G2.markedPlane)
  | linearOne
      (core : LinearModels.AbelianCore L LinearThree.natural)
      (plane : LinearModels.MarkedPlane core.fullCenter E)
  | linearTwo
      (core : LinearModels.AbelianCore L (LinearThree.natural.prod LinearThree.natural))
      (plane : LinearModels.MarkedPlane core.fullCenter E)
  | linearThree
      (center : LinearModels.FullCenter L LinearThree.natural)
      (plane : LinearModels.MarkedPlane center E)

variable [Finite G]

private theorem residual_subgroupOf {L P Y : Subgroup G} (hPL : P ≤ L)
    (hY : Y = (primeToResidual 3 P).map P.subtype) :
    Y.subgroupOf L = (primeToResidual 3 (P.subgroupOf L)).map (P.subgroupOf L).subtype := by
  rw [hY]
  apply Subgroup.map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hPL),
    map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le hPL]

private theorem centralizing_branch_of_model {A V : Type*}
    [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) A V}
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (m : CenterModel c.L ρ) (hfaith : Function.Injective ρ)
    (hZ : IsElementaryAbelian 2 (coreCenter c.L))
    (hdet : DetectedOn ρ ((d.Yplus.subgroupOf c.L).map m.actorMap))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    c.L ⊓ centralizer (extensionCore c.L : Set G) ≤ c.L.pCoreIn 2 ∧
      IsElementaryAbelian 2 (coreCenter c.L) ∧
      ⁅yplusCentralizer d I, c.L⁆ ≤ coreCenter c.L ∧
      IsElementaryAbelian 2 (plusImage I c.L (yplusCentralizer d I)) ∧
      frattini (plusImage I c.L (yplusCentralizer d I)) = ⊥ ∧
      plusImage I c.L (yplusCentralizer d I) = ⊥ := by
  obtain ⟨hcomm, helem, hfrattini⟩ :=
    centralizing_structure_of_model d c hYL hnormal m hfaith hDQ hZ
  exact ⟨m.centralizer_core_le hfaith, hZ, hcomm, helem, hfrattini,
    centralizerImage_eq_bot_of_detected_model d c hYL hnormal m hfaith hDQ hdet⟩

/-- The complete centralizing-branch deduction on the literal source subgroups.
The residual is O^{3′}, the normality is relative to I, and every coefficient
model, faithful action and cocycle-detection premise is discharged here.
The earlier classification and marked V₂-parabolic remain explicit inputs. -/
theorem centralizing_branch (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (hP : d.M ⊓ c.L = c.L ⊓ normalizer (d.V₂ : Set G))
    (hY : d.Yplus = (primeToResidual 3 (d.M ⊓ c.L : Subgroup G)).map (d.M ⊓ c.L).subtype)
    (configuration : MarkedConfiguration c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    c.L ⊓ centralizer (extensionCore c.L : Set G) ≤ c.L.pCoreIn 2 ∧
      IsElementaryAbelian 2 (coreCenter c.L) ∧
      ⁅yplusCentralizer d I, c.L⁆ ≤ coreCenter c.L ∧
      IsElementaryAbelian 2 (plusImage I c.L (yplusCentralizer d I)) ∧
      frattini (plusImage I c.L (yplusCentralizer d I)) = ⊥ ∧
      plusImage I c.L (yplusCentralizer d I) = ⊥ := by
  have hY' := residual_subgroupOf (L := c.L) inf_le_right hY
  cases configuration with
  | alternating hs m W hdim hW hpar =>
    obtain ⟨model, _, _, _, hfaith, hdet⟩ :=
      BlockModels.alternating_model_and_marking hs m ((d.M ⊓ c.L).subgroupOf c.L)
        d.Yplus hY' W hdim hW hpar
    exact centralizing_branch_of_model d c hYL hnormal model hfaith
      (coreCenter_elementary_of_short hs) hdet hDQ
  | g2 hs m hpar =>
    obtain ⟨model, _, _, _, hfaith, hdet⟩ :=
      BlockModels.g2_model_and_marking hs m ((d.M ⊓ c.L).subgroupOf c.L)
        d.Yplus hY' hpar
    exact centralizing_branch_of_model d c hYL hnormal model hfaith
      (coreCenter_elementary_of_short hs) hdet hDQ
  | linearOne core plane =>
    obtain ⟨m⟩ := LinearModels.caseOne core plane hP hY
    exact centralizing_branch_of_model d c hYL hnormal m.model
      (specialLinearNatural_injective 3) m.elementary
      (LinearThree.detectedOn_of_marked_matrices _ m.transvection_mem m.rotation_mem) hDQ
  | linearTwo core plane =>
    obtain ⟨m⟩ := LinearModels.caseTwo core plane hP hY
    exact centralizing_branch_of_model d c hYL hnormal m.model
      LinearThree.two_natural_injective m.elementary
      (LinearThree.detectedOn_two_natural _ m.transvection_mem m.rotation_mem) hDQ
  | linearThree center plane =>
    obtain ⟨m⟩ := LinearModels.caseThree center plane hP hY
    exact centralizing_branch_of_model d c hYL hnormal m.model
      (specialLinearNatural_injective 3) m.elementary
      (LinearThree.detectedOn_of_marked_matrices _ m.transvection_mem m.rotation_mem) hDQ

/-- D⁺ = 1 in the actual quotient I/C_I(L), for all five surviving marked
configurations. No model-specific cover or extension premise remains. -/
theorem centralizerImage_eq_bot_of_marked_configuration (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (hP : d.M ⊓ c.L = c.L ⊓ normalizer (d.V₂ : Set G))
    (hY : d.Yplus = (primeToResidual 3 (d.M ⊓ c.L : Subgroup G)).map (d.M ⊓ c.L).subtype)
    (configuration : MarkedConfiguration c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    plusImage I c.L (yplusCentralizer d I) = ⊥ :=
  (centralizing_branch d c hYL hnormal hP hY configuration hDQ).2.2.2.2.2

/-- The ambient centralizer equality needed by the parent 15.3.31 proof.
Normality of the quotient denominator follows from relative L-normality. -/
theorem centralizers_eq_of_marked_configuration (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (hP : d.M ⊓ c.L = c.L ⊓ normalizer (d.V₂ : Set G))
    (hY : d.Yplus = (primeToResidual 3 (d.M ⊓ c.L : Subgroup G)).map (d.M ⊓ c.L).subtype)
    (configuration : MarkedConfiguration c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    I ⊓ centralizer (d.Yplus : Set G) = I ⊓ centralizer (c.L : Set G) := by
  let : (actionKernel I c.L).Normal := actionKernel_normal
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal)
  have hzero := centralizerImage_eq_bot_of_marked_configuration
    d c hYL hnormal hP hY configuration hDQ
  exact le_antisymm
    (le_inf inf_le_left ((plusImage_eq_bot_iff inf_le_left).mp hzero))
    (inf_le_inf_left I (centralizer_le hYL))

/-- Actual consumer application: 15.3.29 supplies V₁ ≤ C_I(Y₊) and
N_G(V₁) ≤ M, while the component lies outside M. Thus the centralizing
branch is impossible after the earlier marked configurations are supplied. -/
theorem centralizing_branch_false (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (hP : d.M ⊓ c.L = c.L ⊓ normalizer (d.V₂ : Set G))
    (hY : d.Yplus = (primeToResidual 3 (d.M ⊓ c.L : Subgroup G)).map (d.M ⊓ c.L).subtype)
    (configuration : MarkedConfiguration c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G))
    (hVI : d.V₁ ≤ I) (hVY : d.V₁ ≤ centralizer (d.Yplus : Set G))
    (hnorm : normalizer (d.V₁ : Set G) ≤ d.M) : False :=
  excluded_of_equal_centralizers d c hVI hVY hnorm
    (centralizers_eq_of_marked_configuration d c hYL hnormal hP hY configuration hDQ)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
