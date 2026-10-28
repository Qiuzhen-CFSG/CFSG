module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.DualCore

/-!
# The first and middle actual L₁-chief coordinates in S/V

The natural image of V is the marked upper fixed plane: the actual
nontrivial Uα actor centralizes V and its nonzero upper parameter has
exactly that fixed space. The original natural map therefore induces
U/V coordinates in the Borel quotient. The exact Q_K pairing and reverse
product identify (S∩Q_K)/(S∩C_H(U)) with its dual annihilator.

Both targets use the literal L₁ map into the marked Borel. Their chiefness
and noncentrality are proved on these precise actions. No quotient rank
or chief count is assumed; SourceCompletion.Count supplies the consumer.
Source: Aschbacher–Smith 14.7.71–72, printed pp.1075–1076.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem upper_rank : Module.finrank (ZMod 2) SL2FourNatural.upperFixed = 2 := by
  have h := SL2FourNatural.card_upperFixed
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (by decide : 4 = 2 ^ 2))

theorem source_seed_upper
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d) :
    (naturalSection d).imageSpace V = SL2FourNatural.upperFixed := by
  apply Submodule.eq_of_le_of_finrank_eq
  · obtain ⟨a, ha, t, ht, he⟩ := exists_upper_actor d c e.images mark e.image_order
    intro v hv
    obtain ⟨x, hx, rfl⟩ := ((naturalSection d).mem_imageSpace_iff _ _).mp hv
    have hc : (a:G) ∈ centralizer (V : Set G) := by
      rw [centralizer_seed_eq_Q d structural e.separation]
      exact S_le_Q d structural e.separation (critical_le_S c e.conjugate ha)
    have hfix : naturalAction d a (naturalMap d x).toAdd = (naturalMap d x).toAdd := by
      change naturalAction d a ((naturalSection d).coordinates x).toAdd = _
      rw [← (naturalSection d).equivariant a x]
      congr 2
      apply Subtype.ext
      exact (congrArg (fun z => z * (a:G)⁻¹) (hc x hx).symm).trans (by group)
    change d.naturalQuotient.action (d.qH a) (naturalMap d x).toAdd = _ at hfix
    rw [he] at hfix
    change d.naturalQuotient.action (d.naturalQuotient.marking (SL2FourNatural.upper t)) _ = _ at hfix
    rw [d.naturalQuotient.restriction, SL2FourNatural.upper_action] at hfix
    rw [SL2FourNatural.mem_upperFixed]
    have hh := congrFun hfix 0
    have hz : t * (naturalMap d x).toAdd 1 = 0 := add_left_cancel (show (naturalMap d x).toAdd 0 + t * (naturalMap d x).toAdd 1 = (naturalMap d x).toAdd 0 + 0 from by simpa using hh)
    exact (mul_eq_zero.mp hz).resolve_left ht
  · exact (seed_image_finrank d e.separation).trans upper_rank.symm

theorem natural_mem_seed_iff (hp : d.U₀ = F.Vi 1) (x : F.U) :
    (naturalMap d x).toAdd ∈ (naturalSection d).imageSpace V ↔ (x:G) ∈ V := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := ((naturalSection d).mem_imageSpace_iff _ _).mp hx
    have hk : ((x / y : F.U):G) ∈ d.U₀ := by
      apply ((naturalSection d).coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he]
      exact div_self' _
    rw [hp] at hk
    simpa using V.mul_mem (F.le_seed 1 hk) hy
  · intro hx
    exact ((naturalSection d).mem_imageSpace_iff _ _).mpr ⟨x,hx,rfl⟩

variable (m : F.Li L 1 →* borel d.naturalQuotient)
    (hm : ∀ l, (m l).val = d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l))
    (hms : Function.Surjective m)

abbrev firstTarget : Representation (ZMod 2) (F.Li L 1)
    (SL2FourNatural.V ⧸ SL2FourNatural.upperFixed) :=
  (actorQuotient d.naturalQuotient (borel d.naturalQuotient) (borel d.naturalQuotient).le_normalizer).comp m

def firstCoordinates : F.U →* Multiplicative (SL2FourNatural.V ⧸ SL2FourNatural.upperFixed) :=
  ((SL2FourNatural.upperFixed.mkQ).toAddMonoidHom.toMultiplicative).comp (naturalMap d)

theorem firstCoordinates_surjective : Function.Surjective (firstCoordinates d) :=
  SL2FourNatural.upperFixed.mkQ_surjective.comp (naturalMap_surjective d)

theorem firstCoordinates_kernel
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (x : F.U) :
    firstCoordinates d x = 1 ↔ (x:G) ∈ V := by
  change SL2FourNatural.upperFixed.mkQ (naturalMap d x).toAdd = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← source_seed_upper d structural c e mark]
  exact natural_mem_seed_iff d hp x

include hm in
theorem firstCoordinates_equivariant (l : F.Li L 1) (x : F.U) :
    (firstCoordinates d ⟨(l:G)*x*(l:G)⁻¹,
      (mem_normalizer_iff.mp (d.conjugationSection.normalized (F.Li_le L 1 l.property).2) x).mp x.property⟩).toAdd =
      firstTarget d m l (firstCoordinates d x).toAdd := by
  change SL2FourNatural.upperFixed.mkQ (naturalMap d _).toAdd =
    SL2FourNatural.upperFixed.mkQ (d.naturalQuotient.action (m l).val (naturalMap d x).toAdd)
  have hh := (naturalSection d).equivariant (inclusion ((F.Li_le L 1).trans inf_le_right) l) x
  change (naturalMap d _).toAdd = naturalAction d _ (naturalMap d x).toAdd at hh
  rw [hm]
  exact congrArg SL2FourNatural.upperFixed.mkQ hh

include hms in
theorem firstTarget_irreducible : IsIrreducible (firstTarget d m) := by
  apply (irreducible_comp_surjective_iff _ hms _).mpr
  exact actorQuotient_irreducible d.naturalQuotient _ le_rfl (borel d.naturalQuotient).le_normalizer

include hms in
theorem firstTarget_noncentral : ∃ l v, firstTarget d m l v ≠ v := by
  obtain ⟨g,v,hv⟩ := actorQuotient_noncentral d.naturalQuotient _ le_rfl (borel d.naturalQuotient).le_normalizer
  obtain ⟨l,rfl⟩ := hms g
  exact ⟨l,v,hv⟩

abbrev middleSpace := SL2FourNatural.upperFixed.dualAnnihilator

abbrev middleTarget : Representation (ZMod 2) (F.Li L 1) middleSpace :=
  ((SL2FourNatural.BorelDualCore.annihilator
    (actorNatural d.naturalQuotient (borel d.naturalQuotient))
    (actorLine d.naturalQuotient (borel d.naturalQuotient) (borel d.naturalQuotient).le_normalizer)).toRepresentation).comp m

include hms in
theorem middleTarget_irreducible : IsIrreducible (middleTarget d m) := by
  apply (irreducible_comp_surjective_iff _ hms _).mpr
  let := actorQuotient_irreducible d.naturalQuotient _ le_rfl (borel d.naturalQuotient).le_normalizer
  exact SL2FourNatural.BorelDualCore.annihilator_irreducible _ _

include hms in
theorem middleTarget_noncentral : ∃ l v, middleTarget d m l v ≠ v := by
  obtain ⟨g,v,hv⟩ := SL2FourNatural.BorelDualCore.annihilator_noncentral
    (actorNatural d.naturalQuotient (borel d.naturalQuotient))
    (actorLine d.naturalQuotient (borel d.naturalQuotient) (borel d.naturalQuotient).le_normalizer)
    (actorQuotient_noncentral d.naturalQuotient _ le_rfl (borel d.naturalQuotient).le_normalizer)
  obtain ⟨l,rfl⟩ := hms g
  exact ⟨l,v,hv⟩

variable (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (b : QKDualCoordinates d)

def middleCoordinates : ↥(ChiefFactors.S F L ⊓ QK F) →* Multiplicative middleSpace where
  toFun x := Multiplicative.ofAdd ⟨(b.qSection.coordinates ⟨x,x.property.2⟩).toAdd, by
    have hC : (x:G) ∈ centralizer (V:Set G) :=
      (centralizer_seed_eq_Q d structural e.separation).symm ▸
        S_le_Q d structural e.separation x.property.1
    have hh := (mem_centralizer_iff_annihilator d b ⟨x,x.property.2⟩).mp hC
    simpa only [source_seed_upper d structural c e mark] using hh⟩
  map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one b.qSection.coordinates)
  map_mul' x y := by
    apply Subtype.ext
    change (b.qSection.coordinates (⟨x,x.property.2⟩ * ⟨y,y.property.2⟩)).toAdd =
      (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd + (b.qSection.coordinates ⟨y,y.property.2⟩).toAdd
    exact congrArg Multiplicative.toAdd (map_mul b.qSection.coordinates _ _)

theorem middleCoordinates_surjective : Function.Surjective (middleCoordinates d structural c e mark b) := by
  intro v
  have hm : v.toAdd.val ∈ b.qSection.imageSpace (ChiefFactors.S F L ⊓ QK F) := by
    rw [source_intersection_image d structural c e mark b,
      intersection_image_eq_annihilator d structural e.separation b,
      source_seed_upper d structural c e mark]
    exact v.toAdd.property
  obtain ⟨q,hq,he⟩ := (b.qSection.mem_imageSpace_iff _ _).mp hm
  exact ⟨⟨q,hq⟩, Multiplicative.toAdd.injective (Subtype.ext he)⟩

theorem middleCoordinates_kernel (x : ↥(ChiefFactors.S F L ⊓ QK F)) :
    middleCoordinates d structural c e mark b x = 1 ↔ (x:G) ∈ ChiefFactors.S F L ⊓ C F := by
  constructor
  · intro h
    have hzero := congrArg (fun v : Multiplicative middleSpace => v.toAdd.val) h
    exact ⟨x.property.1, (b.qSection.coordinates_eq_one_iff ⟨x,x.property.2⟩).mp
      (Multiplicative.toAdd.injective hzero)⟩
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((b.qSection.coordinates_eq_one_iff ⟨x,x.property.2⟩).mpr h.2)

include hm in
theorem middleCoordinates_equivariant (l : F.Li L 1) (x : ↥(ChiefFactors.S F L ⊓ QK F)) :
    (middleCoordinates d structural c e mark b
      ⟨(l:G)*x*(l:G)⁻¹, (mem_normalizer_iff.mp (L_normalizes_S ((F.Li_le L 1 l.property).1)) x).mp x.property.1,
        (mem_normalizer_iff.mp (b.qSection.normalized ((F.Li_le L 1 l.property).2)) x).mp x.property.2⟩).toAdd =
      middleTarget d m l (middleCoordinates d structural c e mark b x).toAdd := by
  apply Subtype.ext
  change (b.qSection.coordinates _).toAdd =
    (d.naturalQuotient.action (m l).val⁻¹).dualMap (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd
  apply LinearMap.ext
  intro v
  have hh := LinearMap.congr_fun
    (b.qSection.equivariant (inclusion ((F.Li_le L 1).trans inf_le_right) l) ⟨x,x.property.2⟩) v
  change _ = (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd
    (d.naturalQuotient.action (d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l)⁻¹) v) at hh
  have hq : d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l)⁻¹ = (m l).val⁻¹ :=
    (d.qH.map_inv _).trans (congrArg Inv.inv (hm l).symm)
  exact hh.trans (congrArg (fun g : ChapterJ.S5 =>
    (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd (d.naturalQuotient.action g v)) hq)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
