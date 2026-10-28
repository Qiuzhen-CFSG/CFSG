module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Centralizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.LongCentralizer

/-!
# The marked Ree inverter in the original J.4 centralizer

A first-endpoint equivalence retaining the central involution and the chosen
five-subgroup sends the actual binary root s₁ to an element of the original
H inverting its original B₅. The proof transports centrality and inversion
through the literal endpoint map. Once short-path transport supplies ambient
fusion to z, the completed original J.3 calculations give both fixed fives
and the self-centralizing elementary subgroup of order25.

The endpoint marking and ambient fusion are separate earlier inputs: the
former comes from F.1.12 and Sylow conjugacy, the latter from F.4.6 short-path
transport. No isomorphism of the generated completion is used. Source:
Aschbacher--Smith, paragraph preceding J.4.8, printed pp.442--443.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Subgroup
open Centralizers Centralizers.Choices
namespace MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths

/-- The actual s₁ lifted into the first model endpoint. -/
def modelU : first := ⟨u, borel_le_first u_mem_borel⟩

/-- The actual central involution lifted into that endpoint. -/
def modelZ : first := ⟨z, first_eq_centralizer_z.symm ▸
  mem_centralizer_singleton_iff.mpr rfl⟩

/-- The specified order-five rotation lifted into the same endpoint. -/
def modelRotation : first := ⟨rotation, rotation_mem_first⟩

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Centralizers.Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- The image under the original endpoint equivalence, as an element of G. -/
def sourceU : G := e modelU

private theorem modelU_centralizes_modelZ : modelU * modelZ = modelZ * modelU := by
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (sylow_centralizes_z (borel_eq_sylow ▸ u_mem_borel))

private theorem modelU_inverts_rotation :
    modelU * modelRotation * modelU⁻¹ = modelRotation⁻¹ :=
  Subtype.ext u_inverts_rotation

/-- A marked first-endpoint equivalence gives a literal inverter in the
original H. Both marking hypotheses concern the original quotient maps. -/
theorem source_inverter
    (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    sourceU e ∈ d.toTypeRuSetup.H ∧
      ∀ x ∈ B5Image B5, sourceU e * x * (sourceU e)⁻¹ = x⁻¹ := by
  have huH : sourceU e ∈ d.toTypeRuSetup.H := by
    rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff, ← hz]
    exact congrArg (fun a : F => (a : G)) (by
      simpa only [map_mul] using congrArg e modelU_centralizes_modelZ)
  refine ⟨huH, ?_⟩
  intro x hx
  rw [← hfive] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
  have h : modelU * modelRotation^n * modelU⁻¹ = (modelRotation^n)⁻¹ := by
    change MulAut.conj modelU (modelRotation^n) = _
    rw [map_zpow, MulAut.conj_apply, modelU_inverts_rotation, inv_zpow]
  exact (by
    simpa only [sourceU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv, Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] using
      congrArg (fun a : F => (a : G)) (congrArg e h))

/-- The same literal source inverter feeds the existing extraspecial and
self-centralizer calculations once original short-path fusion is supplied. -/
theorem source_fixed_pair
    (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    Nat.card (fixedFive B5 (sourceU e)) = 5 ∧
      Nat.card (fixedFive B5 (c.z * sourceU e)) = 5 ∧
      IsElementaryAbelian 5 (B5Image B5 ⊔ fixedFive B5 (sourceU e) : Subgroup G) ∧
      centralizer ((B5Image B5 ⊔ fixedFive B5 (sourceU e) : Subgroup G) : Set G) =
        B5Image B5 ⊔ fixedFive B5 (sourceU e) := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  obtain ⟨h2,hprod⟩ := product_class c B5 (sourceU e) hu hfusion hi
  obtain ⟨h5,h5'⟩ := fixed_cards c B5 (sourceU e) hu h2 hi hfusion hprod
  exact ⟨h5,h5',base_fixed_elementary c B5 (sourceU e) hu hfusion hi,
    centralizer_base_fixed c B5 (sourceU e) hu hfusion hi⟩

end MarkedInverter
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
