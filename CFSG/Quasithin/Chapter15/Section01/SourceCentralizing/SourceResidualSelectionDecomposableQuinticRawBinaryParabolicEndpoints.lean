module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicNodes
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FiveInteriorExtension
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicNodes
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryGraphFour
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinarySourceParabolics

/-! The actual graph endpoints retain the no-A3-product obstruction through
the entire two-core. Degree four uses strict growth of the residual in a
characteristic-two cover; degree five uses the native sixth-power witness.
The degree-five interior retains its literal GL3(2) core quotient.
Private imports intentionally reuse only record-free intrinsic helpers and
this raw lane's full-preimage cover. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.RawBinaryParabolic
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- Characteristic two rules out an A3-product residual in the exact
four-dimensional graph endpoint, including its entire original kernel. -/
theorem four_endpoint_not_aThree (L : Subgroup G)
    (hf : generalizedFitting L = pCore 2 L)
    (e : (L ⧸ pCore 2 L) ≃* SL(3+1,ZMod 2)) (b : Basis 3) :
    ¬CaseIComponentData.IsAThreeProduct (EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ)) := by
  let q := coreFlagMap L e
  let D := EquivariantLift.lift L q (cutStabilizer b {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ)
  let P := D.subgroupOf L
  let E := BinaryLinear.parabolic (cutSpace b (1 : Fin 3))
  have hflag : cutStabilizer b {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ = E := by
    ext g
    rw [mem_cutStabilizer]
    constructor
    · exact fun hh => hh 1 (by decide)
    · intro hh i hi
      have he : i=1 := by fin_cases i <;> simp_all
      subst i
      exact hh
  have him : P.map q = E := (coreFlagMap_lift_image L e _).trans hflag
  let f : P →* E := (MulEquiv.subgroupCongr him).toMonoidHom.comp (q.subgroupMap P)
  have hsurj : Function.Surjective f :=
    (MulEquiv.subgroupCongr him).surjective.comp (q.subgroupMap_surjective P)
  have hk : f.ker = (pCore 2 L).subgroupOf P := by
    ext x
    change (⟨q x,_⟩ : E) = 1 ↔ (x : L) ∈ pCore 2 L
    rw [←coreFlagMap_ker L e]
    exact Subtype.ext_iff
  have hcore : pCore 2 L ≤ P := by
    change pCore 2 L ≤ (EquivariantLift.lift L q _).subgroupOf L
    rw [lift_eq]
    change pCore 2 L ≤ (((cutStabilizer b {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ).comap
      (coreFlagMap L e)).map L.subtype).comap L.subtype
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    rw [←coreFlagMap_ker L e]
    exact ker_le_comap _ _
  obtain ⟨h576,h144⟩ := four_endpoint_residual_data b
  change Nat.card E = 576 at h576
  change 144 ≤ Nat.card (pResidual 2 E) at h144
  have hne : pResidual 2 E ≠ ⊥ := by intro he; rw [he,card_bot] at h144; omega
  have hlt := CaseIComponentData.residual_card_lt_of_characteristic_core P
    (hf ▸ centralizer_generalizedFitting_le L) hcore f hsurj hk hne
  have hker : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.comap_subtype
  have h27 : ¬27 ∣ Nat.card P := by
    have hc := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective hsurj,card_top,h576] at hc
    obtain ⟨r,hr⟩ := hker.exists_card_eq
    rw [hr] at hc
    intro hd
    rw [←hc] at hd
    exact (by decide : ¬27 ∣ 576)
      (((by decide : Nat.Coprime 27 2).pow_right r).dvd_of_dvd_mul_left hd)
  let t : P ≃* D := subgroupOfEquivOfLe (EquivariantLift.lift_le L q _)
  have hcard : Nat.card (pResidual 2 P) = Nat.card (pResidual 2 D) := by
    have hh := congrArg (fun X : Subgroup D => Nat.card X)
      (map_pResidual_of_surjective 2 t.toMonoidHom t.surjective)
    rw [card_map_of_injective t.injective] at hh
    exact hh
  rintro ⟨F,hF,hcomm,hgen⟩
  have hbound := ChapterC.alternatingThree_product_card_le_of_not_dvd F
    (fun A hA => (hF A hA).2) hcomm (by rwa [←Nat.card_congr t.toEquiv])
  rw [hgen] at hbound
  have hbig : 144 < Nat.card (pResidual 2 D) := h144.trans_lt (hlt.trans_eq hcard)
  exact (Nat.not_lt_of_ge hbound hbig)

/-- The native residual element whose sixth power is nonidentity lifts to
the original five-dimensional endpoint. -/
theorem five_endpoint_not_aThree (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL(4+1,ZMod 2)) (b : Basis 4) :
    ¬CaseIComponentData.IsAThreeProduct (EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ)) := by
  obtain ⟨f,hf,_⟩ := lift_cover L e (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ)
  exact CaseIComponentData.not_aThreeProduct_of_residual_image _ f hf
    (five_endpoint_residual_not_exponent_six b)

/-- The full preimage of the marked five-dimensional interior retains its
actual three-dimensional Levi quotient. -/
theorem five_interior_core (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL(4+1,ZMod 2)) (b : Basis 4) :
    Nonempty (((EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3})) ⧸ pCore 2
      (EquivariantLift.lift L (coreFlagMap L e)
        (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}))) ≃* LinearGroup 3) := by
  obtain ⟨f,hf,hk⟩ := lift_cover L e (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3})
  obtain ⟨u⟩ := BinaryLinear.InvariantNodeActions.five_interior_quotient b
  exact ⟨(f.pCoreQuotientEquiv hf hk).trans u⟩

end CFSG.Quasithin.Chapter15.Section01.RawBinaryParabolic
