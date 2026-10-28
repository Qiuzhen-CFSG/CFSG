module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.LocalGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Literal parabolics and component action in original 15.1.22

The family retains the quotient of P N_S(L) by its own two-core and
excludes a central product of genuine A₃ blocks in O²(P). Neither the
two-core nor a group-family label replaces this two-residual condition.
The plus map is the quotient of N_{G₁}(L) by C_{G₁}(L); in particular S
is never silently assumed to normalize L. All images first restrict to
this actual normalizer.

Source: Aschbacher--Smith, original 15.1.22 (*), (**), printed pp.1098--1099.
These definitions contain no placement or centralizer conclusion.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The source N_S(L), rather than all of S. -/
def sylowNormalizer (d : CaseIComponentData T M Mc V) : Subgroup G :=
  d.S ⊓ normalizer (d.L : Set G)

/-- The source G_L=N_{G₁}(L). -/
def componentNormalizer (d : CaseIComponentData T M Mc V) : Subgroup G :=
  d.G1 ⊓ normalizer (d.L : Set G)

/-- The literal C_{G₁}(L), expressed inside G_L. -/
def componentKernel (d : CaseIComponentData T M Mc V) : Subgroup d.componentNormalizer :=
  (centralizer (d.L : Set G)).subgroupOf d.componentNormalizer

instance componentKernel_normal (d : CaseIComponentData T M Mc V) :
    d.componentKernel.Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact inf_le_right.trans (normalizer_le_normalizer_centralizer d.L)

abbrev ComponentPlus (d : CaseIComponentData T M Mc V) :=
  d.componentNormalizer ⧸ d.componentKernel

def plusMap (d : CaseIComponentData T M Mc V) :
    d.componentNormalizer →* d.ComponentPlus := QuotientGroup.mk' d.componentKernel

/-- Images use the restriction to G_L. Containment is proved at use sites. -/
def plus (d : CaseIComponentData T M Mc V) (A : Subgroup G) : Subgroup d.ComponentPlus :=
  (A.subgroupOf d.componentNormalizer).map d.plusMap

noncomputable def plusOmega (d : CaseIComponentData T M Mc V) : Subgroup d.ComponentPlus :=
  omegaOneCenterAmbient (d.plus d.sylowNormalizer)

/-- The embedded O^{3′}(M ∩ L). -/
def localThreeResidual (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype

/-- Central products of actual A₃ blocks in P, with their ambient subnormality. -/
def IsAThreeProduct (P : Subgroup G) : Prop :=
  ∃ F : Set (Subgroup P),
    (∀ A ∈ F, ChapterC.IsBlock A ∧ ChapterC.IsAlternatingBlock A 3) ∧
    F.Pairwise (fun A B => ⁅A,B⁆ = ⊥) ∧ sSup F = pResidual 2 P

/-- Exactly the parabolic family used before any row exclusion. -/
structure IsSourceParabolic (d : CaseIComponentData T M Mc V) (P : Subgroup G) : Prop where
  le_component : P ≤ d.L
  normalized : d.sylowNormalizer ≤ normalizer (P : Set G)
  fitting : generalizedFitting P = pCore 2 P
  quotient :
    Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∨
    Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))
  not_aThree_product : ¬ IsAThreeProduct P

def sourceParabolics (d : CaseIComponentData T M Mc V) : Set (Subgroup G) :=
  {P | d.IsSourceParabolic P}

theorem component_le_normalizer (d : CaseIComponentData T M Mc V) :
    d.L ≤ d.componentNormalizer := le_inf d.L_component.1 d.L.le_normalizer

theorem sylowNormalizer_le_componentNormalizer (d : CaseIComponentData T M Mc V) :
    d.sylowNormalizer ≤ d.componentNormalizer :=
  inf_le_inf_right _ d.S_le_G1

theorem componentKernel_map (d : CaseIComponentData T M Mc V) :
    d.componentKernel.map d.componentNormalizer.subtype =
      d.G1 ⊓ centralizer (d.L : Set G) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property.1,hy⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx,Subgroup.centralizer_le_normalizer _ hc⟩,hc,rfl⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
