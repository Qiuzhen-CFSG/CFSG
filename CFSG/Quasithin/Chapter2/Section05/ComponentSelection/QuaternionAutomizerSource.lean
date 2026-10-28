module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.QuaternionShadowSource
public import Theory.GroupTheory.TwoGroupSquareChoice
/-! # Consuming the original automizer in the quaternion contradiction
The actual quotient by O₂(H) supplies the M₁₀ epimorphism with its exact
centralizer kernel. The finite two-group normalizer condition chooses the
outside crossing element, and the proved terminal quaternion argument applies.
The A₆ source dispatcher therefore removes its M₁₀ alternative whenever the
original two-core is quaternion. No action or crossing witness is retained.
Source: Aschbacher--Smith 2.5.21, printed p.567.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {M H L:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.quaternion_m10_core_quotient_impossible
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (eK:L≃*AlternatingSix.ShadowLocal.A6)
    (eQ:(H⧸pCore 2 H)≃*AlternatingSix.M10.extension)
    (eC:twoCore H≃*QuaternionGroup 2) : False := by
  obtain ⟨f,hf,hk⟩:=MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) (c.T:Subgroup G) c.T.isPGroup' c.sylow_lt
  exact MathieuSourceSetup.quaternion_m10_impossible c hgen eK f hf hk
    ((MulEquiv.subgroupCongr (MathieuSourceSetup.core_eq_sylow_centralizer c hgen).symm).trans eC)
    x hxT hxS hxN hx2

/-- The original A₆ source automizer supplies all action premises and eliminates
its M₁₀ branch for a quaternion two-core. -/
theorem MathieuSourceSetup.quaternion_alternating_six_core_quotient
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (eK:L≃*AlternatingSix.ShadowLocal.A6)
    (eC:twoCore H≃*QuaternionGroup 2) :
    Nonempty ((H⧸pCore 2 H)≃*GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∨
      Nonempty ((H⧸pCore 2 H)≃*AlternatingSix.ShadowLocal.AutA6) := by
  rcases MathieuSourceSetup.normal_alternating_six_core_quotient c hG hempty hgen eK with h|h|h
  · obtain ⟨eQ⟩:=h
    exact (MathieuSourceSetup.quaternion_m10_core_quotient_impossible c hgen eK eQ eC).elim
  · exact Or.inl h
  · exact Or.inr h
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
