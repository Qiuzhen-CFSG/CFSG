module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import Theory.GroupTheory.NormalCentralQuotientAction
import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The original scalar residual in the triple-six source

The literal X=O²(O_{2,Z}(K)) maps onto the full central cubic of K/O2(K).
In the original hexacode chart a generator acts as a nontrivial field
scalar and has no nonzero fixed vector. Thus U∩C_G(X)=1, on the unchanged
whole chosen module. No equality O2(K)=U or block splitting is assumed.

Source: Aschbacher--Smith12.7.1 and12.7.7, printed pp.839 and841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original scalar residual, embedded through the original K. -/
@[expose] def tripleSixScalarResidual (K : Subgroup G) : Subgroup G :=
  ((pResidual 2 (centralPreimage (pCore 2 K))).map
    (centralPreimage (pCore 2 K)).subtype).map K.subtype

/-- The exact scalar residual maps onto the central cubic, retaining the
specified original quotient marking. -/
theorem tripleSixScalarResidual_image (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    ((tripleSixScalarResidual K).subgroupOf K).map
      (a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
        center Atlas.Codes.HexEvenAutomorphisms := by
  let Z := centralPreimage (pCore 2 K)
  let q := a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hZ : Z.map q = center Atlas.Codes.HexEvenAutomorphisms := by
    rw [show Z = centralPreimage (pCore 2 K) from rfl,show q =
      a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) from rfl,
      ←map_map,map_centralPreimage]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (centerCongr a.groupEquiv ⟨z,hz⟩).property
    · intro hx
      exact ⟨a.groupEquiv.symm x,(centerCongr a.groupEquiv.symm ⟨x,hx⟩).property,
        a.groupEquiv.apply_symm_apply x⟩
  have hp : pResidual 2 (center Atlas.Codes.HexEvenAutomorphisms) = ⊤ := by
    apply top_unique
    intro z _
    exact mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (Hexacode.even_center_card ▸ orderOf_dvd_natCard z))
  change ((((pResidual 2 Z).map Z.subtype).map K.subtype).comap K.subtype).map q = _
  rw [comap_map_eq_self_of_injective K.subtype_injective,map_embedded_pResidual,hZ,hp,
    ←MonoidHom.range_eq_map,range_subtype]

/-- The original full chosen U has no nonidentity element centralizing
the actual scalar residual X. -/
theorem tripleSixScalarResidual_fixed_eq_bot (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    U ⊓ centralizer (tripleSixScalarResidual K : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro u hu
  have hz : Atlas.Codes.hexEvenZ ∈ center Atlas.Codes.HexEvenAutomorphisms := by
    rw [←Hexacode.even_kernel_eq_center,Atlas.Codes.hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hm := (tripleSixScalarResidual_image D a).symm ▸ hz
  obtain ⟨x,hx,hxq⟩ := hm
  let v : U := ⟨u,hu.1⟩
  have he := tripleSixPointCoordinates_conjugate D a x v
  change a.groupEquiv (QuotientGroup.mk' (pCore 2 K) x) = Atlas.Codes.hexEvenZ at hxq
  rw [hxq] at he
  have hcomm : (x : G) * u * (x : G)⁻¹ = u := by
    rw [hu.2 x hx,mul_inv_cancel_right]
  rw [hcomm] at he
  have heU : (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
      (Hexacode.evenAction Atlas.Codes.hexEvenZ ((tripleSixPointCoordinates D a v).toAdd))) = v :=
    Subtype.ext he
  have hf := congrArg (tripleSixPointCoordinates D a) heU
  rw [MulEquiv.apply_symm_apply] at hf
  have hscalar := congrArg Multiplicative.toAdd hf
  change Hexacode.action Atlas.Codes.hexZ ((tripleSixPointCoordinates D a v).toAdd) =
    (tripleSixPointCoordinates D a v).toAdd at hscalar
  have hzv := (Hexacode.scalar_fixed_iff _).mp hscalar
  have hfv : tripleSixPointCoordinates D a v = 1 := hzv
  have hv1 : v = 1 := (tripleSixPointCoordinates D a).injective
    (hfv.trans (map_one _).symm)
  exact congrArg Subtype.val hv1

end CFSG.Quasithin.Chapter12.Section07
