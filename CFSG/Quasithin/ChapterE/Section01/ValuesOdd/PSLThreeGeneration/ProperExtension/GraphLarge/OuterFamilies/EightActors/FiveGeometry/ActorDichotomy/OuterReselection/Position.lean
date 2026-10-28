module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Position.Action

/-!
# The fixed full actor in the literal radical quotient

The marked GL₂ block identifies the radical quotient with PGL₂(5), using
only the allowed unmarked S₅ premise. The central sign vanishes, while the
other two generators become the classes of diag(4,1) and [[0,3],[4,0]].
These commuting involutions generate a four-group. The latter matrix has
nonsquare determinant, so this whole actor is outside the derived subgroup.

The actor restriction and quotient map are the literal ones. The proved
equality between the residual supplement and the full centralizer transfers
the calculation back to exactly OuterReselection.StandardPosition. Its
consumer is modelReselection_of_standard_calculations; the independent
StandardFusion calculation remains with that assembly's other input.

Source: Aschbacher--Smith E.1.1--5, E.1.8, E.1.10 and the odd linear
branch of E.1.14(7), printed pp.209--214. Imported concrete carriers retain
their ATLAS attribution and the license in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory Matrix GorensteinWalter
open scoped MatrixGroups Matrix

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection

namespace Position
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

@[expose] def sign : GL (Fin 2) (ZMod 5) :=
  ⟨!![4,0;0,1], !![4,0;0,1], by decide +kernel, by decide +kernel⟩

@[expose] def twist : GL (Fin 2) (ZMod 5) :=
  ⟨!![3,0;0,1], !![2,0;0,1], by decide +kernel, by decide +kernel⟩

@[expose] def outer : GL (Fin 2) (ZMod 5) := twist * skew

abbrev d : PGL2 (ZMod 5) := ProjGenLinGroup.mk sign

abbrev t : PGL2 (ZMod 5) := ProjGenLinGroup.mk outer

@[expose] def actor : Subgroup (PGL2 (ZMod 5)) := zpowers d ⊔ zpowers t

theorem sign_block : block sign = SL3.standardInvolution (ZMod 5) := by
  apply Subtype.ext
  rw [block_formula]
  decide +kernel

theorem twist_block : block twist = twistDiagonal := by
  apply Subtype.ext
  rw [block_formula]
  decide +kernel

theorem central_block :
    block (GeneralLinearGroup.scalar (Fin 2) (-1 : (ZMod 5)ˣ)) = secondDiagonal := by
  apply Subtype.ext
  rw [block_formula]
  decide +kernel

theorem d_sq : d ^ 2 = 1 := by
  change ProjGenLinGroup.mk sign ^ 2 = 1
  rw [← map_pow, show sign ^ 2 = 1 by decide +kernel, map_one]

theorem t_sq : t ^ 2 = 1 := by
  have h : outer ^ 2 = GeneralLinearGroup.scalar (Fin 2)
      (⟨2,3,by decide,by decide⟩ : (ZMod 5)ˣ) := by decide +kernel
  change ProjGenLinGroup.mk outer ^ 2 = 1
  rw [← map_pow, h, ProjGenLinGroup.mk_scalar]

theorem d_ne : d ≠ 1 := by
  intro h
  have hmem := ProjGenLinGroup.mk_eq_one.mp h
  rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
  have hn : ∀ u : (ZMod 5)ˣ, GeneralLinearGroup.scalar (Fin 2) u ≠ sign := by decide +kernel
  obtain ⟨u,hu⟩ := hmem
  exact hn u hu

theorem t_outside_psl : t ∉
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod 5)).range := by
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
  decide +kernel

theorem d_inside_psl : d ∈
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod 5)).range := by
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
  decide +kernel

theorem dt_commute : Commute t d := by
  have h : outer * sign = sign * outer * GeneralLinearGroup.scalar (Fin 2) (-1 : (ZMod 5)ˣ) := by
    decide +kernel
  change ProjGenLinGroup.mk outer * ProjGenLinGroup.mk sign =
    ProjGenLinGroup.mk sign * ProjGenLinGroup.mk outer
  rw [← map_mul, h, map_mul, ProjGenLinGroup.mk_scalar, mul_one, map_mul]

theorem card_actor : Nat.card actor = 4 := by
  have hout : t ∉ zpowers d := fun h =>
    t_outside_psl ((zpowers_le.mpr d_inside_psl) h)
  have hn : t ∈ normalizer (zpowers d : Set (PGL2 (ZMod 5))) := by
    apply Subgroup.centralizer_le_normalizer
    intro x hx
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
    exact (dt_commute.zpow_right n).symm.eq
  rw [actor, card_sup_zpowers_of_normalizing_involution _ _ t_sq hout hn,
    Nat.card_zpowers, orderOf_eq_prime d_sq d_ne]

theorem actor_outside : ¬ actor ≤ _root_.commutator (PGL2 (ZMod 5)) := by
  intro h
  exact t_outside_psl (pgl2_commutator_le_psl2_range (ZMod 5)
    (h (mem_sup_right (mem_zpowers t))))

@[expose] noncomputable def signC : C :=
  embed sign

@[expose] noncomputable def centralC : C :=
  embed (GeneralLinearGroup.scalar (Fin 2) (-1 : (ZMod 5)ˣ))

@[expose] noncomputable def twistedC : C :=
  embed twist * graphC

theorem signC_val : (signC : Model) = FiveSourceAudit.innerSL (SL3.standardInvolution (ZMod 5)) := by
  change FiveSourceAudit.innerSL (block sign) = _
  rw [sign_block]

theorem centralC_val : (centralC : Model) = centralElement := by
  change FiveSourceAudit.innerSL (block (GeneralLinearGroup.scalar (Fin 2) (-1))) = _
  rw [central_block]
  rfl

theorem twistedC_val : (twistedC : Model) = twistedGraph := by
  change FiveSourceAudit.innerSL (block twist) * graphElement = _
  rw [twist_block]
  rfl

theorem representative_restriction :
    representative.subgroupOf C = closure ({signC,centralC,twistedC} : Set C) := by
  apply Subgroup.map_injective C.subtype_injective
  rw [map_subgroupOf_eq_of_le
    (representative_le_standardSylow.trans standardSylow_le_centralizer), MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.subtype_apply,
    signC_val, centralC_val, twistedC_val]
  rfl

theorem quotient_sign : q signC = projective d := by
  exact (projective_mk sign).symm

theorem quotient_central : q centralC = 1 := quotient_embed_scalar _

theorem quotient_twisted (hmodel : Nonempty (Q ≃* Equiv.Perm (Fin 5))) :
    q twistedC = projective t := by
  change q (embed twist * graphC) = projective (ProjGenLinGroup.mk (twist * skew))
  simp only [map_mul, graph_quotient hmodel, projective_mk]

theorem image_representative (hmodel : Nonempty (Q ≃* Equiv.Perm (Fin 5))) :
    (representative.subgroupOf C).map q = actor.map projective := by
  rw [representative_restriction, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, quotient_sign,
    quotient_central, quotient_twisted hmodel]
  rw [Set.insert_comm, closure_insert_one]
  rw [actor, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union]
  rw [Set.singleton_union]

theorem quotientActor (hmodel : Nonempty (Q ≃* Equiv.Perm (Fin 5))) :
    QuotientActor C representative := by
  constructor
  · change Nat.card ((representative.subgroupOf C).map q) = 4
    rw [image_representative hmodel, card_map_of_injective projective_injective, card_actor]
  · intro h
    change (representative.subgroupOf C).map q ≤ _root_.commutator Q at h
    have hc : (_root_.commutator (PGL2 (ZMod 5))).map projective = _root_.commutator Q := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (projective_surjective hmodel)]
      rfl
    rw [image_representative hmodel, ← hc] at h
    exact actor_outside ((map_le_map_iff_of_injective projective_injective).mp h)

end Position

/-- The fixed full actor has order four in the radical quotient and is
not contained in its derived subgroup, with only the allowed S₅ premise. -/

theorem standardPosition : StandardPosition := by
  intro hmodel
  have transfer (K : Subgroup FiveSourceAudit.Model) (hK : K = Position.C) :
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5)) →
        QuotientActor K representative := by
    subst K
    exact Position.quotientActor
  exact transfer _ Position.centralizer_eq_supplement hmodel

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection
