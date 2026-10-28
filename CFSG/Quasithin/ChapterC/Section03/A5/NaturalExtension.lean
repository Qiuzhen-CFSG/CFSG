module
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Quotient
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# Deleted-five blocks do not embed in natural rank-one extensions

The source two-core has trivial image in SL₂ because the block is perfect.
Its elementary commutator layer therefore lies in the extension kernel.
The quotient of that kernel by its ambient center is the actual natural
plane. The block layer injects into this quotient: an element in its kernel
would lie in the proved trivial fixed kernel of the deleted-five block.
The cubic fixed vector in the deleted permutation module contradicts the
fixed-point-free cubic action in the natural plane.

All maps are the original subgroup inclusion, core quotient and conjugation
maps. Neither normality of the block nor a Sylow-order bound is assumed.
Source: Aschbacher--Smith 2.4.25, printed p.543, the symplectic model row.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
variable {F G A : Type*} [Field F] [Finite F] [CharP F 2] [Group G] [Group A]

/-- An alternating-five block is perfect, including its actual two-core. -/
theorem IsAlternatingBlock.perfect_five (hA : IsAlternatingBlock A 5) : Group.IsPerfect A := by
  obtain ⟨a⟩ := hA.2.2.quotient_iso
  have hc : Nat.card (A ⧸ pCore 2 A) = 60 := by
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hq : IsQuasisimple (A ⧸ pCore 2 A) := hA.2.1.quotient.resolve_right (by omega)
  let := hq
  exact BlockCommutation.perfect_of_quasisimple_quotient hA.2.1

/-- No deleted-five block embeds in an extension with the actual SL₂ natural quotient action. -/
theorem no_alternatingFive_in_naturalExtension
    {Q : Subgroup G} [Q.Normal] (d : NaturalExtension (F := F) Q)
    (hA : IsAlternatingBlock A 5) (i : A →* G) (hi : Function.Injective i) : False := by
  let := hA.perfect_five
  let := d.elementary
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hA.2.2
  let q := d.projection.comp i
  have hcore : pCore 2 A ≤ q.ker := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker q
  have hk : q.ker = pCore 2 A := by
    apply le_antisymm ?_ hcore
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    have he : q.ker = Q.comap i := by
      rw [show q = d.projection.comp i from rfl, ← MonoidHom.comap_ker, d.kernel]
    rw [he]
    exact (IsElementaryAbelian.isPGroup 2 Q).comap_of_injective i hi
  let j := QuotientGroup.lift (pCore 2 A) q hcore
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,hk]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  let a := j.comp m.quotientIso.symm.toMonoidHom
  have ha : Function.Injective a := hj.comp m.quotientIso.symm.injective
  have hu : ∀ u : blockU A, i u.val ∈ Q := by
    intro u
    rw [← d.kernel]
    exact hcore (blockU_le_core u.property)
  let iU : blockU A →* Q := (i.comp (blockU A).subtype).codRestrict Q hu
  let r : blockU A →* Multiplicative (Fin 2 → F) :=
    d.moduleIso.toMonoidHom.comp ((QuotientGroup.mk' ((center G).subgroupOf Q)).comp iU)
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro u hu
    have he : QuotientGroup.mk' ((center G).subgroupOf Q) (iU u) = 1 :=
      d.moduleIso.injective (hu.trans (map_one d.moduleIso).symm)
    have hz : i u.val ∈ center G := (QuotientGroup.eq_one_iff (N := (center G).subgroupOf Q) (iU u)).mp he
    have hzA : u.val ∈ center A := by
      rw [mem_center_iff]
      intro v
      apply hi
      simpa only [map_mul] using (mem_center_iff.mp hz (i v))
    have huf : u ∈ blockFixed A := hzA
    simpa only [hA.blockFixed_eq_bot, mem_bot] using huf
  have hb : Function.Bijective (QuotientGroup.mk' (blockFixed A)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hA.blockFixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let b := (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed A)) hb).trans m.moduleIso
  let e : BinaryPermutation.natural (Fin 5) →+ (Fin 2 → F) :=
    (r.comp b.symm.toMonoidHom).toAdditive
  have he : Function.Injective e := hr.comp b.symm.injective
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_natural_injection a ha e he
  intro x v
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) (m.quotientIso.symm x)
  have hx : m.quotientIso (QuotientGroup.mk' (pCore 2 A) l) = x := by
    rw [hl,m.quotientIso.apply_symm_apply]
  let u := b.symm (Multiplicative.ofAdd v)
  have hbv : b u = Multiplicative.ofAdd v := b.apply_symm_apply _
  have hbact : b (blockConjugate A l u) = Multiplicative.ofAdd
      (BinaryPermutation.naturalRepresentation (Fin 5) x.val v) := by
    change m.moduleIso (QuotientGroup.mk' _ (blockConjugate A l u)) = _
    rw [m.intertwining,hx]
    change ρ x (b u) = _
    rw [hbv]
    apply Multiplicative.toAdd.injective
    exact hρ x (Multiplicative.ofAdd v)
  have hax : a x = d.projection (i l) := by
    change j (m.quotientIso.symm x) = _
    rw [←hl]
    rfl
  have hUact : iU (blockConjugate A l u) = extensionConjugate Q (i l) (iU u) := by
    apply Subtype.ext
    exact map_mul i _ _ |>.trans (by rw [map_mul, map_inv]; rfl)
  change (r (b.symm (Multiplicative.ofAdd
    (BinaryPermutation.naturalRepresentation (Fin 5) x.val v)))).toAdd = _
  rw [←hbact,b.symm_apply_apply,hax]
  change (d.moduleIso (QuotientGroup.mk' _ (iU (blockConjugate A l u)))).toAdd = _
  rw [hUact,d.intertwining]
  rfl
end CFSG.Quasithin.ChapterC
