module
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.AlternatingFiveObstruction
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.Quintet
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# The quintet core excludes the original alternating-five module

When the block's literal U is the ambient two-core, faithfulness of the
semilinear action puts the block's entire two-core in that same kernel.
Thus its A5 quotient embeds in the actual semilinear quotient without any
normality assumption on the block. The incompatible cubic fixed spaces
exclude its deleted permutation module in the natural F4 plane.

Source: Aschbacher–Smith, proof of 2.4.25, printed p.543, using H.14.2(2),
p.397. The final theorem uses the intrinsic M23 quintet and its literal action.
-/

public section
open Subgroup
open Sporadic.Mathieu.M23Geometry.ChapterHLocalActions
namespace CFSG.Quasithin.ChapterC

variable {G : Type*} [Group G]
theorem not_alternatingFive_of_semilinear_core_eq
    (f : (G ⧸ pCore 2 G) →* HexSemilinear.Gamma) (hf : Function.Injective f)
    (E : Multiplicative Representation.SL2FourNatural.V ≃* pCore 2 G)
    (hE : ∀ (g : G) (v : Representation.SL2FourNatural.V),
      g * (E (Multiplicative.ofAdd v)).val * g⁻¹ =
      (E (Multiplicative.ofAdd
        (HexSemilinear.natural (f (QuotientGroup.mk' (pCore 2 G) g)) v))).val)
    (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hU : (blockU A).map A.subtype = pCore 2 G) : False := by
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hA.2.2
  have hcent : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    intro g hg
    have ha : HexSemilinear.natural (f (QuotientGroup.mk' (pCore 2 G) g)) = 1 := by
      apply LinearEquiv.ext
      intro v
      apply Multiplicative.ofAdd.injective
      apply E.injective
      apply Subtype.ext
      rw [← hE,← hg _ (E (Multiplicative.ofAdd v)).property,mul_inv_cancel_right]
      rfl
    have hq : f (QuotientGroup.mk' (pCore 2 G) g) = 1 :=
      HexSemilinear.natural_injective (ha.trans HexSemilinear.natural.map_one.symm)
    exact (QuotientGroup.eq_one_iff g).mp (hf (hq.trans f.map_one.symm))
  have hc : (pCore 2 G).subgroupOf A = pCore 2 A := by
    apply le_antisymm
    · apply le_sSup
      exact ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
    · intro a ha
      apply hcent
      rw [← hU]
      rintro _ ⟨v,hv,rfl⟩
      exact congrArg A.subtype (hA.2.1.core_centralizes_blockU ha v hv)
  let q := (QuotientGroup.mk' (pCore 2 G)).comp A.subtype
  have hk : q.ker = pCore 2 A := by
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact hc
  let j := QuotientGroup.lift (pCore 2 A) q hk.symm.le
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,hk]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  let a := (f.comp j).comp m.quotientIso.symm.toMonoidHom
  have ha : Function.Injective a := hf.comp (hj.comp m.quotientIso.symm.injective)
  have hu : blockU A ≤ (pCore 2 G).subgroupOf A := by
    rw [hc]
    exact blockU_le_core
  let i : blockU A →* pCore 2 G :=
    (A.subtype.comp (blockU A).subtype).codRestrict _ (fun u => hu u.property)
  have hi : Function.Injective i := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 G => (z : G)) h
  have hb : Function.Bijective (QuotientGroup.mk' (blockFixed A)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hA.blockFixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let b := (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed A)) hb).trans m.moduleIso
  let d := E.symm.toMonoidHom.comp (i.comp b.symm.toMonoidHom)
  let e : BinaryPermutation.natural (Fin 5) →+ Representation.SL2FourNatural.V := d.toAdditive
  have he : Function.Injective e := E.symm.injective.comp (hi.comp b.symm.injective)
  apply HexSemilinear.no_alternatingFive_natural_injection a ha e he
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
  have hax : a x = f (QuotientGroup.mk' (pCore 2 G) (l : G)) := by
    change f (j (m.quotientIso.symm x)) = _
    rw [← hl]
    rfl
  have hev : E (Multiplicative.ofAdd (e v)) = i u := E.apply_symm_apply _
  apply Multiplicative.ofAdd.injective
  apply E.injective
  apply Subtype.ext
  rw [hax]
  change (E (d (Multiplicative.ofAdd
      (BinaryPermutation.naturalRepresentation (Fin 5) x.val v)))).val = _
  rw [← hbact]
  change (E (E.symm (i (b.symm (b (blockConjugate A l u)))))).val = _
  rw [b.symm_apply_apply,E.apply_symm_apply]
  rw [← hE,hev]
  rfl


/-- The quintet core cannot be the actual U of any alternating-five block. -/
theorem native_quintet_no_alternatingFive_core
    (A : Subgroup Sporadic.Mathieu.M23Geometry.CommonFour.quintetStabilizer)
    (hA : IsAlternatingBlock A 5)
    (hU : (blockU A).map A.subtype = pCore 2 _) : False :=
  not_alternatingFive_of_semilinear_core_eq quintetQuotientEquiv.toMonoidHom
    quintetQuotientEquiv.injective quintetBinaryEquiv quintetBinaryEquiv_conjugation A hA hU

end CFSG.Quasithin.ChapterC
