module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixOrbits
public import Theory.Representation.HexacodeAction.Field
public import Theory.ElementaryAbelian.Injective

/-!
# The original scalar four-group through a triple-six vector

Pull the field line through an original nonidentity vector back through the
actual chosen-space chart. The resulting subgroup lies in the unchanged U,
has order four, and is fixed pointwise by the original component centralizer
of that vector. Field linearity of the even hexacode action proves the last
assertion, with the actor automorphism in the chart retained.

This constructs the field point used in 12.7.4. Its full-weight marking, the
A5 vector stabilizer, the natural quotient action and the nonsplit full-space
extension remain separate calculations.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4(2),
printed pp.839--840, and K.1.3, printed p.453.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The full original subgroup coordinates attached to the actual action chart. -/
def tripleSixPointCoordinates (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    U ≃* Multiplicative Atlas.Codes.hexacode :=
  D.spaceEquiv.symm.trans a.linearEquiv.toAddEquiv.toMultiplicative

/-- The literal inverse image in U of the F4-line through the chosen t. -/
def tripleSixPoint (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) : Subgroup G :=
  let f := tripleSixPointCoordinates D a
  (((Submodule.span Hexacode.F {(f t).toAdd}).toAddSubgroup.toSubgroup).comap
    f.toMonoidHom).map U.subtype

private theorem point_coordinates_conjugate (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (k : K) (v : U) :
    ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
      (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
        ((tripleSixPointCoordinates D a v).toAdd))) : G) =
      (k : G) * (v : G) * (k : G)⁻¹ := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have he := a.intertwines (QuotientGroup.mk' (pCore 2 K) k) w
  change (D.spaceEquiv (Multiplicative.ofAdd (a.linearEquiv.symm
    (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
      (a.linearEquiv w)))) : G) = _
  rw [← he, a.linearEquiv.symm_apply_apply, D.spaceEquiv_apply]
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg (fun z : U => (z : G)) (D.spaceEquiv.apply_symm_apply v))
  change (k : G) * (w.val.toMul.val : G) * (k : G)⁻¹ = _
  rw [hw]

/-- The scalar point is an actual elementary four-group in the original U;
the original K-centralizer of t fixes the entire point. -/
theorem tripleSixPoint_properties (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1) :
    (t : G) ∈ tripleSixPoint D a t ∧ tripleSixPoint D a t ≤ U ∧
      Nat.card (tripleSixPoint D a t) = 4 ∧
      IsElementaryAbelian 2 (tripleSixPoint D a t) ∧
      K ⊓ centralizer ({(t : G)} : Set G) ≤ centralizer (tripleSixPoint D a t : Set G) := by
  let f := tripleSixPointCoordinates D a
  let w := (f t).toAdd
  let P := Submodule.span Hexacode.F {w}
  have hw : w ≠ 0 := by
    intro h
    have hh : f t = 1 := h
    exact ht (f.injective (hh.trans f.map_one.symm))
  have hle : tripleSixPoint D a t ≤ U := map_subtype_le _
  have hmem : (t : G) ∈ tripleSixPoint D a t := by
    refine ⟨t, ?_, rfl⟩
    exact Submodule.mem_span_singleton_self w
  have hcard : Nat.card (tripleSixPoint D a t) = 4 := by
    change Nat.card ((P.toAddSubgroup.toSubgroup.comap f.toMonoidHom).map U.subtype) = 4
    rw [card_map_of_injective U.subtype_injective, comap_equiv_eq_map_symm',
      card_map_of_injective f.symm.injective]
    change Nat.card P = 4
    rw [Module.natCard_eq_pow_finrank (K := Hexacode.F),
      finrank_span_singleton hw, pow_one, Nat.card_eq_fintype_card, Hexacode.field_card]
  let := D.elementary
  have hel : IsElementaryAbelian 2 (tripleSixPoint D a t) :=
    IsElementaryAbelian.of_injective (inclusion hle) (inclusion_injective hle)
  refine ⟨hmem, hle, hcard, hel, ?_⟩
  intro k hk
  let kK : K := ⟨k, hk.1⟩
  let g := a.groupEquiv (QuotientGroup.mk' (pCore 2 K) kK)
  have hfix : Hexacode.evenAction g w = w := by
    have he := point_coordinates_conjugate D a kK t
    have hc : k * (t : G) * k⁻¹ = t :=
      mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hk.2)
    rw [hc] at he
    have hs : f.symm (Multiplicative.ofAdd (Hexacode.evenAction g w)) = t := Subtype.ext he
    have hh := congrArg f hs
    rw [f.apply_symm_apply] at hh
    exact congrArg Multiplicative.toAdd hh
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hv
  change (f u).toAdd ∈ P at hu
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hu
  have hfu : Hexacode.evenAction g (f u).toAdd = (f u).toAdd := by
    rw [← hr]
    change Hexacode.evenFieldAction g (r • w) = r • w
    rw [map_smul]
    exact congrArg (fun q => r • q) hfix
  have he := point_coordinates_conjugate D a kK u
  change (f.symm (Multiplicative.ofAdd (Hexacode.evenAction g (f u).toAdd)) : G) = _ at he
  rw [hfu] at he
  change (f.symm (f u) : G) = _ at he
  rw [f.symm_apply_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- The literal triple-six row constructs the four-group through any original
nonidentity t, using the proved coordinates rather than an additional model input. -/
theorem original_tripleSix_point (D : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hd : Module.finrank (ZMod 2) D.space = 6)
    (hf : Function.Injective D.quotientAction) (hi : IsIrreducible D.quotientAction)
    (t : G) (htU : t ∈ U) (ht : t ≠ 1) :
    ∃ Vt : Subgroup G, t ∈ Vt ∧ Vt ≤ U ∧ Nat.card Vt = 4 ∧
      IsElementaryAbelian 2 Vt ∧
      K ⊓ centralizer ({t} : Set G) ≤ centralizer (Vt : Set G) := by
  obtain ⟨a⟩ := original_tripleSix_coordinates D eK hd hf hi
  exact ⟨tripleSixPoint D a ⟨t, htU⟩,
    tripleSixPoint_properties D a ⟨t, htU⟩ (fun h => ht (congrArg Subtype.val h))⟩

end CFSG.Quasithin.Chapter12.Section07
