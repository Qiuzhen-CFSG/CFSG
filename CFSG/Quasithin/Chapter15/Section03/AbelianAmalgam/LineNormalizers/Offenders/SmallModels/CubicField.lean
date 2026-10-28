module

public import Theory.Representation.SpecialLinearNatural.CubicFixedSpace
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Marked

public section
open Subgroup Representation Representation.BinaryOffender

/-!
The following companion belongs beside the actual 15.3.67 marked line-normalizer
consumer. Its U and q are the literal B.5.1/B.4.8 section data inside the source
action. Classification, kernel lifting and geometric normalization remain with
the source assembly owner; the cubic fixes the entire specified Sylow fixed
space and therefore the original marker.
-/
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
open BestReduction Representation.SL3BinaryCubic
variable {F D V : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]

/-- The natural section supplies the cubic needed for the source marker. -/
theorem sl3Field_natural_marked_cubic
    {ρ : Representation (ZMod 2) D V} {J : Subgroup D}
    (d : MarkedNormalizer ρ J) (f : Actor F →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] Space F)
    (hq : ∀ g u, q (U.toRepresentation g u) = natural g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ d.marker, ρ c v = v := by
  obtain ⟨c,hc,hfix⟩ := natural_centralSection_cubic ρ f hf U q hq hker hquot d.sylow
  exact ⟨c,hc,fun v hv => hfix v (d.sylow_fixes hv)⟩

/-- Both natural factors use the same embedded SL₃(F) and the same source q. -/
theorem sl3Field_double_marked_cubic
    {ρ : Representation (ZMod 2) D V} {J : Subgroup D}
    (d : MarkedNormalizer ρ J) (f : Actor F →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] (Space F × Space F))
    (hq : ∀ g u, q (U.toRepresentation g u) = (natural.prod natural) g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ d.marker, ρ c v = v := by
  obtain ⟨c,hc,hfix⟩ := double_centralSection_cubic ρ f hf U q hq hker hquot d.sylow
  exact ⟨c,hc,fun v hv => hfix v (d.sylow_fixes hv)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels

