module
public import Theory.GroupTheory.CComponent.TwoComponent.OddQuotient
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CentricRadicalCoreComparison

/-!
# The intrinsic odd-then-two core quotient

The source O_{2',2}(G) is the inverse image of O₂(G/O(G)); we reuse
`AlperinGoldschmidt.primeCorePreimage` under a shorter two-local name.
Its quotient is the iterated quotient, compatibly with representatives
and isomorphisms. For a two-component the odd-core quotient is
quasisimple and its center is its two-core, so the resulting quotient
is nonabelian simple. If the odd core is solvable, O_{2',2} is also
exactly the solvable radical. Finite odd-order solvability is supplied
by the source consumer, keeping this module independent of classification.

Source: GLS II, Chapter B, Lemma 4.8; Aschbacher–Smith, combined manuscript
of 1 March 2004, Lemma I.3.2, printed p.415.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The source O_{2',2}(G), the inverse image of O₂(G/O(G)). -/
abbrev oddTwoCore (G : Type*) [Group G] : Subgroup G :=
  AlperinGoldschmidt.primeCorePreimage 2 G

instance oddTwoCore_normal : (oddTwoCore G).Normal :=
  inferInstanceAs ((pCore 2 (G ⧸ pPrimeCore 2 G)).comap
    (QuotientGroup.mk' (pPrimeCore 2 G))).Normal

/-- Factoring out the source core agrees with the iterated quotient. -/
noncomputable def oddTwoCoreQuotientEquivIterated :
    (G ⧸ oddTwoCore G) ≃*
      ((G ⧸ pPrimeCore 2 G) ⧸ pCore 2 (G ⧸ pPrimeCore 2 G)) :=
  QuotientGroup.liftEquiv _
    (φ := (QuotientGroup.mk' (pCore 2 (G ⧸ pPrimeCore 2 G))).comp
      (QuotientGroup.mk' (pPrimeCore 2 G)))
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    (by rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl)

theorem oddTwoCoreQuotientEquivIterated_mk (x : G) :
    oddTwoCoreQuotientEquivIterated (QuotientGroup.mk' (oddTwoCore G) x) =
      QuotientGroup.mk' (pCore 2 (G ⧸ pPrimeCore 2 G))
        (QuotientGroup.mk' (pPrimeCore 2 G) x) := rfl

theorem oddTwoCore_comap_equiv (e : G ≃* H) :
    (oddTwoCore H).comap e.toMonoidHom = oddTwoCore G := by
  let f := QuotientGroup.congr (pPrimeCore 2 G) (pPrimeCore 2 H) e
    (pPrimeCore_map_iso 2 e)
  have hfc : (pCore 2 (H ⧸ pPrimeCore 2 H)).comap f.toMonoidHom =
      pCore 2 (G ⧸ pPrimeCore 2 G) := by
    rw [← pCore_map_iso 2 f]
    exact comap_map_eq_self_of_injective f.injective _
  ext x
  change QuotientGroup.mk' (pPrimeCore 2 H) (e x) ∈ pCore 2 (H ⧸ pPrimeCore 2 H) ↔ _
  change f (QuotientGroup.mk' (pPrimeCore 2 G) x) ∈ pCore 2 (H ⧸ pPrimeCore 2 H) ↔ _
  exact SetLike.ext_iff.mp hfc (QuotientGroup.mk' (pPrimeCore 2 G) x)

theorem oddTwoCore_map_equiv (e : G ≃* H) :
    (oddTwoCore G).map e.toMonoidHom = oddTwoCore H := by
  rw [← oddTwoCore_comap_equiv e, map_comap_eq_self_of_surjective e.surjective]

instance oddTwoCore_characteristic : (oddTwoCore G).Characteristic :=
  characteristic_iff_map_eq.mpr oddTwoCore_map_equiv

variable [Finite G]

theorem oddTwoCore_isSolvable [Group.IsSolvable (pPrimeCore 2 G)] :
    Group.IsSolvable (oddTwoCore G) := by
  let : Group.IsSolvable (QuotientGroup.mk' (pPrimeCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsNilpotent (pCore 2 (G ⧸ pPrimeCore 2 G)) := pCore_isPGroup.isNilpotent
  exact isSolvable_comap_of_solvable_ker (QuotientGroup.mk' (pPrimeCore 2 G)) _

/-- For a quasisimple odd-core quotient, the source core is the solvable radical. -/
theorem oddTwoCore_eq_solvableRadical_of_quasisimple
    [IsQuasisimple (G ⧸ pPrimeCore 2 G)] [Group.IsSolvable (pPrimeCore 2 G)] :
    oddTwoCore G = solvableRadical G := by
  let Q := G ⧸ pPrimeCore 2 G
  let : Group.IsSolvable (center Q) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hr : solvableRadical Q = center Q := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center Q) inferInstance inferInstance)
  have hz : center Q = pCore 2 Q :=
    IsQuasisimple.center_eq_pCore (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
  let : Group.IsSolvable (QuotientGroup.mk' (pPrimeCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  change (pCore 2 Q).comap _ = _
  rw [← hz, ← hr]
  exact comap_solvableRadical_eq_of_solvable_ker _ (QuotientGroup.mk'_surjective _)

/-- The source quotient of a two-component is simple. -/
theorem IsTwoComponent.isSimpleGroup_quotient_oddTwoCore {L : Subgroup G}
    (hL : L.IsTwoComponent) : IsSimpleGroup (L ⧸ oddTwoCore L) := by
  let := hL.2
  let Q := L ⧸ pPrimeCore 2 L
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  have hz : center Q = pCore 2 Q :=
    IsQuasisimple.center_eq_pCore (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
  let e := (oddTwoCoreQuotientEquivIterated (G := L)).trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact e.isSimpleGroup

/-- The source quotient of a two-component is nonabelian. -/
theorem IsTwoComponent.not_isMulCommutative_quotient_oddTwoCore {L : Subgroup G}
    (hL : L.IsTwoComponent) : ¬ IsMulCommutative (L ⧸ oddTwoCore L) := by
  let := hL.1.perfect
  let := hL.isSimpleGroup_quotient_oddTwoCore
  exact Group.IsPerfect.not_isMulCommutative _

end Subgroup
