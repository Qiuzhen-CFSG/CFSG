module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.ModelCocycles
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry

/-!
# Applying the corrected quotient calculation to the original point center

The constructed cocycles close the SL₃ equality branch Q=VC_T(L). The source
Cartan and point-core geometry then feed the proved center decomposition on
the original flag. Only the two literal local-core calculations remain here;
the point-cohomology owner retains their discharge in the final assembly.
No splitting of V or deletion of C_T(L) is used.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766, with C.1.13 corrected.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem sylow_card_congr {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (P : Sylow 2 A) (Q : Sylow 2 B) :
    Nat.card P = Nat.card Q := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (Sylow.equiv R Q).toEquiv)

/-- The actual Sp₄ block alternative forces the marked coefficient field to have order four. -/
theorem sp4_field_four_of_block
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) :
    Nat.card S.field.Carrier = 4 := by
  let P := Theory.SpecificGroups.SymplecticFour.unipotentSylow S.field.card_eq S.field.degree_pos
  rcases hb with hb | hb
  · obtain ⟨_,_,F,inst,fin,hF,hmodel⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := S.field.degree)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hc := sylow_card_congr (m.groupEquiv.symm.trans hmodel.quotient_iso.some) P
      (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F S.field.degree_pos hF)
    change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := S.field.Carrier)) =
      Nat.card (Matrix.PSL3.LinearThree.unipotentSL F) at hc
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
      Matrix.PSL3.LinearThree.card_unipotentSL,S.field.card_eq,hF,← pow_mul,← pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    have hn := S.field.degree_pos
    omega
  · obtain ⟨_,F,inst,fin,hF,ρ,⟨model⟩,_⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : Fintype F := Fintype.ofFinite F
    have hF' : Nat.card F = 2^2 := by omega
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by simpa only [Nat.card_eq_fintype_card] using hF')
    have hc := sylow_card_congr (m.groupEquiv.symm.trans model.quotientIso) P
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF' (by decide))
    change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := S.field.Carrier)) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) at hc
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
      Theory.SpecificGroups.SymplecticFour.card_unipotent,S.field.card_eq,hF',← pow_mul,← pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    have hn : S.field.degree = 2 := by omega
    rw [S.field.card_eq,hn]
    rfl

/-- A nontrivial corrected quotient forces the actual q=4 symplectic marking. -/
theorem strict_quotient_symplectic_four
    (c : Coordinates D S.field)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hstrict : Nontrivial (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      ((cohomologyDenominator T L V).subgroupOf ((L ⊔ (T : Subgroup G)).pCoreIn 2)))) :
    Nat.card S.field.Carrier = 4 ∧
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) := by
  cases c with
  | sl3 m =>
    have hs : ChapterC.IsShort L := hb.elim (fun h => h.2.1) (fun h => h.1)
    have he := sl3_core_eq_denominator D S m hs
    have hn := QuotientGroup.nontrivial_iff.mp hstrict
    exact (hn (by rw [←he,subgroupOf_self])).elim
  | sp4 m => exact ⟨sp4_field_four_of_block D S m hb,⟨m⟩⟩
  | g2 m => exact (PointGeometry.no_g2_block_marking D S m hb).elim


/-- The original SL₃ point-center calculation, with the local-core geometry still explicit. -/
theorem sl3_center_of_core_calculations
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hlocal : V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L := by
  have hs : ChapterC.IsShort L := hb.elim (fun h => h.2.1) (fun h => h.1)
  obtain ⟨X,hXL,hXR,ho,hf,hp⟩ :=
    PointGeometry.center_geometry_of_core_calculations D S f hb hprod hlocal
  exact center_eq_of_core_eq_denominator D S hs f X hXL hXR ho hf hp
    (sl3_core_eq_denominator D S m hs)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
