module
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.AlternatingFiveObstruction
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.Quintet
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# Excluding the alternating A5 block in the native quintet local

A normal subgroup meets the ambient two-core in its own two-core. Its A5
quotient therefore embeds faithfully in the actual semilinear quotient.
Projectivity removes the fixed kernel inside U, giving an equivariant
injection of the original alternating module into the native F4 plane.
The cubic fixed-vector obstruction then excludes this embedding. The last
theorem applies the construction to the actual M23 quintet coordinates.
No central factor in O2 of the block is removed.
Source: Aschbacher–Smith C.3.1(3–4), printed pp.149–151, and H.14.2(2), p.397.
-/

public section
open Subgroup
open Sporadic.Mathieu.M23Geometry.ChapterHLocalActions
namespace CFSG.Quasithin.ChapterC

variable {G : Type*} [Group G] [Finite G]

theorem not_alternatingFive_of_semilinear_core
    (f : (G ⧸ pCore 2 G) →* HexSemilinear.Gamma) (hf : Function.Injective f)
    (E : Multiplicative Representation.SL2FourNatural.V ≃* pCore 2 G)
    (hE : ∀ (g : G) (v : Representation.SL2FourNatural.V),
      g * (E (Multiplicative.ofAdd v)).val * g⁻¹ =
      (E (Multiplicative.ofAdd
        (HexSemilinear.natural (f (QuotientGroup.mk' (pCore 2 G) g)) v))).val)
    (A : Subgroup G) [A.Normal] (hA : IsAlternatingBlock A 5) : False := by
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hA.2.2
  have hc : (pCore 2 G).subgroupOf A = pCore 2 A :=
    (Subgroup.Normal.isSubnormal (inferInstance : A.Normal)).pCore_subgroupOf 2
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

theorem native_quintet_no_normal_alternatingFive
    (A : Subgroup Sporadic.Mathieu.M23Geometry.CommonFour.quintetStabilizer)
    [A.Normal] : ¬ IsAlternatingBlock A 5 :=
  not_alternatingFive_of_semilinear_core quintetQuotientEquiv.toMonoidHom
    quintetQuotientEquiv.injective quintetBinaryEquiv quintetBinaryEquiv_conjugation A

end CFSG.Quasithin.ChapterC
