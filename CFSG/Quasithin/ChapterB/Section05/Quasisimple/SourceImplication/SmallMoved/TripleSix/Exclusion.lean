module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Catalogue
public import Theory.Representation.TripleSixSmallMoved.Obstruction

/-!
# Excluding the covered-A₆ source row on its actual module

The source's F₄ coordinates turn the original component action into a faithful
F₄-linear representation. Its literal central quotient to A₆ gives dihedral
Sylow two-subgroups. The actual offender and whole displacement bound transport
through those same coordinates, contradicting the scalar-plane obstruction.
No choice of a recognized hexacode module, new offender, or split extension is
assumed. In particular the corrected projective-plane convention is preserved.

Source: Aschbacher–Smith B.4.2(8), K.1.3 and 13.7.15(1), pp.86,453,943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved.TripleSix
open SourceInduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private noncomputable def fieldAction (a : ProjectiveLine.TripleSixAction ρ L) :
    Representation BinaryField.four.Carrier L (Fin 3 → BinaryField.four.Carrier) where
  toFun g :=
    { toFun := fun w => a.coordinates (ρ g (a.coordinates.symm w))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro c w
        simpa only [LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          a.scalar_linear g c (a.coordinates.symm w) }
  map_one' := by
    apply LinearMap.ext
    intro w
    change a.coordinates (ρ (1 : G) (a.coordinates.symm w)) = w
    rw [map_one,Module.End.one_apply,LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change a.coordinates (ρ ((g*h : L) : G) (a.coordinates.symm w)) =
      a.coordinates (ρ g (a.coordinates.symm (a.coordinates (ρ h (a.coordinates.symm w)))))
    rw [Subgroup.coe_mul,map_mul,Module.End.mul_apply,LinearEquiv.symm_apply_apply]

/-- The faithful F₄-linear covered-A6 row has no offender moving only a plane. -/
theorem not_plane (hf : Function.Injective ρ) {A : Subgroup G}
    (hA : IsOffender ρ A) (hAL : A ≤ L)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (a : ProjectiveLine.TripleSixAction ρ L) : False := by
  let τ := fieldAction a
  let : FiniteDimensional (ZMod 2) (Fin 3 → BinaryField.four.Carrier) :=
    Module.Finite.equiv a.coordinates
  have hτ : Function.Injective τ := by
    intro g h he
    apply Subtype.ext
    apply hf
    apply LinearMap.ext
    intro v
    apply a.coordinates.injective
    have hh := LinearMap.congr_fun he (a.coordinates v)
    change a.coordinates (ρ g (a.coordinates.symm (a.coordinates v))) =
      a.coordinates (ρ h (a.coordinates.symm (a.coordinates v))) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  let e : ActionEquiv (ρ.comp L.subtype) (restrictScalars (k := ZMod 2) τ) :=
    { groupEquiv := MulEquiv.refl L
      linearEquiv := a.coordinates
      intertwines := fun g v => by
        change a.coordinates (ρ g v) =
          a.coordinates (ρ g (a.coordinates.symm (a.coordinates v)))
        rw [LinearEquiv.symm_apply_apply] }
  have hAr := hA.subgroupOf ρ hAL
  have hAm := hAr.map_equivariant (ρ.comp L.subtype) (restrictScalars τ)
    e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
  have hm := moved_finrank_equivariant (ρ.comp L.subtype) (restrictScalars τ)
    e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines (A.subgroupOf L)
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAL] at hm
  let q := a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q :=
    a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.card q.ker = 3 := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.quotientEquiv.injective,
      QuotientGroup.ker_mk',Nat.card_congr a.centerEquiv.toEquiv]
    exact Nat.card_zmod 3
  have hF : Module.finrank (ZMod 2) BinaryField.four.Carrier = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := BinaryField.four.Carrier)
    rw [Nat.card_zmod,BinaryField.four.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  exact Representation.TripleSixSmallMoved.not_offender_plane τ hF hτ
    (Representation.TripleSixSmallMoved.sylow_card_and_center q hq hk) hAm (hm.symm.le.trans hd)
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved.TripleSix
