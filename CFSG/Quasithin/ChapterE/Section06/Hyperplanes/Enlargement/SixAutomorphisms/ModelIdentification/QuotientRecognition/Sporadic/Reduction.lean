module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Branches
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.FixedComponent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Source

/-!+# Intrinsic and ambient inputs for the sporadic quotient inspection

An involution fixed subgroup whose order is not divisible by 360 cannot
contain A₆. More generally, absence of an A₆ component transports through
an actual group isomorphism and contradicts the component constructed on
Y/Z(Y). These reductions do not apply to HS, whose inner involution table
has a genuine A₆ component. The separate source exclusion retains the
entire ambient configuration for that case.

Source: Aschbacher–Smith, Theorem C, printed p.33, E.6.8, pp.247–248,
and the further enlargement in E.6.23, p.254 (PDF p.265).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic

variable {D E : Type*} [Group D] [Group E]

/-- An intrinsic exclusion for an actual group, without any family tag.
This is not asserted for HS. -/
def FixedSixExclusion (D : Type*) [Group D] : Prop :=
  ∀ a : MulAut D, orderOf a = 2 → ∀ K : Subgroup a.fixedSubgroup,
    IsComponent a.fixedSubgroup K → ¬ Nonempty (K ≃* alternatingGroup (Fin 6))

namespace FixedSixExclusion

/-- Transport the actual fixed subgroup and its component together. -/
theorem of_equiv (e : D ≃* E) (h : FixedSixExclusion E) : FixedSixExclusion D := by
  intro a ha K hK hmodel
  let f := MulAut.fixedSubgroupCongr e a
  obtain ⟨c⟩ := hmodel
  exact h (MulAut.congr e a) (((MulAut.congr e).orderOf_eq a).trans ha)
    (K.map f.toMonoidHom) (hK.map_equiv f) ⟨(f.subgroupMap K).symm.trans c⟩

/-- A fixed-subgroup order obstruction is stronger than the component exclusion. -/
theorem of_fixed_card [Finite D]
    (h : ∀ a : MulAut D, orderOf a = 2 → ¬ 360 ∣ Nat.card a.fixedSubgroup) :
    FixedSixExclusion D := by
  intro a ha K _ hmodel
  obtain ⟨e⟩ := hmodel
  apply h a ha
  have hd := K.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd ⊢
  exact hd

/-- An ambient order obstruction excludes every involution-fixed A₆ component. -/
theorem of_card [Finite D] (h : ¬ 360 ∣ Nat.card D) : FixedSixExclusion D := by
  apply of_fixed_card
  intro a _ hd
  exact h (hd.trans a.fixedSubgroup.card_subgroup_dvd_card)

end FixedSixExclusion

variable {G : Type*} [Group G] [Finite G]

/-- One actual quotient model, with the full source configuration retained.
In particular the HS branch is not reduced to an unrestricted centralizer claim. -/
def SourceExclusion (D : Type*) [Group D] (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  HypothesisE61 KnownSimple.IsKnownSimple T M V → HypothesisE615 V →
    EarlierResults T M V →
    ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
      intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
        Nonempty ((Y ⧸ center Y) ≃* D) → False

/-- The actual quotient component discharges all the inputs of an intrinsic exclusion. -/
theorem not_quotient_of_fixed_exclusion {M V U A L X Y : Subgroup G} {g : G}
    [IsElementaryAbelian 2 V] (hD : FixedSixExclusion D)
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) (e : (Y ⧸ center Y) ≃* D) : False := by
  obtain ⟨a, ha, hS, ⟨s⟩⟩ := quotient_fixed_six_component d hY
  exact hD.of_equiv e a ha _ hS.2 ⟨(subgroupOfEquivOfLe hS.1).trans s⟩

/-- The model's simplicity and perfectness are inherited from the source component;
they need not be certified separately for the concrete carrier. -/
theorem sourceExclusion_of_fixed_exclusion
    (hD : IsSimpleGroup D → Group.IsPerfect D → FixedSixExclusion D)
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion D T M V := by
  intro _ _ _ U A L X g d _ Y hY he
  obtain ⟨e⟩ := he
  let _ := extension_quasisimple hY
  let _ : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  let _ : Group.IsPerfect (Y ⧸ center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective _)
  have hs : IsSimpleGroup D := (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  have hp : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact not_quotient_of_fixed_exclusion (hD hs hp) d hY e

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
