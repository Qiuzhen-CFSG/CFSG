module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Candidates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Excluding the symmetric-linear quotient

The group S₅ × L₃(2) has order 20160 and a nontrivial sign quotient. A
perfect subgroup whose two-core quotient is L₄(2) would have order at least
20160, fill the entire group, and force the sign quotient to be perfect.
This is impossible. The intrinsic section survives passage through a
normal two-core, so the same obstruction applies to a local C-component
in any group whose actual two-core quotient is S₅ × L₃(2).

For the specified ATLAS max4 subgroup, the remaining input is precisely the
concrete quotient isomorphism owned by `SymmetricLinear.Quotient`. No global
J₄ order, simplicity, or Sylow coverage is assumed by this conditional result.

Source: the Sylow-overgroup proof of Aschbacher–Smith A.3.12(17), printed
pp.47–48, used in 1.3.9, p.514. The literal subgroup program and the matrix
model of L₃(2) are documented in `SymmetricLinear.Model`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels
open Janko4.LocalStructure.SymmetricLinear

private theorem section_card {G : Type*} [Group G]
    (h : ClassicalGroup.IsPSL G 4 2) : Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem quotientModel_card : Nat.card QuotientModel = 20160 := by
  rw [Nat.card_prod, Atlas.Comparisons.Exceptional.sl3Two_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

private theorem quotientModel_not_perfect : ¬ Group.IsPerfect QuotientModel := by
  intro h
  let := h
  let f : QuotientModel →* ℤˣ := (Equiv.Perm.sign).comp (MonoidHom.fst _ _)
  have hs : Function.Surjective f := (Equiv.Perm.sign_surjective (Fin 5)).comp
    (fun x => ⟨(x, 1), rfl⟩)
  let := Group.IsPerfect.ofSurjective hs
  have he : (1 : ℤˣ) = -1 := Subsingleton.elim _ _
  norm_num at he

private theorem no_perfect_four (B : Subgroup QuotientModel) [Group.IsPerfect B]
    (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2) : False := by
  have hdiv : 20160 ∣ Nat.card B := by
    rw [← section_card hB]
    exact card_quotient_dvd_card (pCore 2 B)
  have hle : 20160 ≤ Nat.card B := Nat.le_of_dvd (Nat.card_pos) hdiv
  have hcard : Nat.card B = Nat.card QuotientModel := by
    apply le_antisymm B.card_le_card_group
    rwa [quotientModel_card]
  have htop : B = ⊤ := B.eq_top_of_card_eq hcard
  have hp : Group.IsPerfect (⊤ : Subgroup QuotientModel) := htop ▸ inferInstance
  exact quotientModel_not_perfect (Group.IsPerfect.top_iff.mp hp)

/-- The actual quotient comparison excludes a local L₄(2) section. -/
theorem no_local_four_of_symmetricLinear_quotient {G : Type*} [Group G] [Finite G]
    (e : (G ⧸ pCore 2 G) ≃* QuotientModel)
    (A : Subgroup G) (S : Subgroup G)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S) : False := by
  let C := A.subgroupOf (A ⊔ S)
  let : Group.IsPerfect C := hlocal.perfect
  let eC : C ≃* A := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := eC.toMonoidHom) eC.surjective
  let etop : XiQuotient (⊤ : Subgroup G) ≃* (G ⧸ pCore 2 G) :=
    QuotientGroup.congr _ _ topEquiv (pCore_map_iso 2 topEquiv)
  let eq := etop.trans e
  let B := (twoQuotientImage A ⊤).map eq.toMonoidHom
  let f := eq.subgroupMap (twoQuotientImage A ⊤)
  let : Group.IsPerfect (twoQuotientImage A ⊤) :=
    Group.IsPerfect.ofSurjective (twoQuotientProjection_surjective (show A ≤ ⊤ from le_top))
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  let ef : XiQuotient (twoQuotientImage A ⊤) ≃* XiQuotient B :=
    QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  apply no_perfect_four B
  exact hA.of_mulEquiv ((imageSectionEquiv (show A ≤ ⊤ from le_top)).trans ef).symm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
