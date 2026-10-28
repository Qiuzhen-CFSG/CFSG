module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Basic
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.PCoreImage
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.Quotient

/-!
# The literal quotient action in 14.7.72

The generation branch identifies the Frattini subgroup of S = ⟨Uᴸ⟩ with V.
Its containment in the two-core Q makes S/V elementary abelian. Conjugation
by L on that quotient kills Q ∩ L because [S,Q] ≤ V. Since T normalizes L,
O₂(L) ≤ Q, so this action descends through the original natural marking qL.
The representative formula and the exact kernel of the quotient coordinates
are retained. None of these constructions requires S ≤ L.

The inputs are supplied by the earlier local setup and the independent
14.7.72 generation branch; they do not include a module recognition premise.
Source: Aschbacher–Smith, 14.7.72, printed p.1076 (PDF p.1093),
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

omit [Finite G] in
/-- The generation branch's Frattini equality, on the actual subgroup S. -/
theorem relative_frattini
    (hPhi : (frattini (S F L)).map (S F L).subtype = V) :
    V.subgroupOf (S F L) = frattini (S F L) := by
  apply (map_injective (S F L).subtype_injective)
  rw [hPhi, map_subgroupOf_eq_of_le]
  exact hPhi.symm.le.trans (map_subtype_le _)

omit [Finite G] in
theorem quotient_normal
    (hPhi : (frattini (S F L)).map (S F L).subtype = V) :
    (V.subgroupOf (S F L)).Normal := by
  rw [relative_frattini hPhi]
  infer_instance

theorem quotient_elementary [(V.subgroupOf (S F L)).Normal]
    (hSQ : S F L ≤ Q T L)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V) :
    IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L)) := by
  let : Fact (IsPGroup 2 (S F L)) := ⟨(isPGroup_pCoreIn 2 _).to_le hSQ⟩
  let : IsElementaryAbelian 2 (S F L ⧸ frattini (S F L)) :=
    isElementaryAbelian_quotient_frattini
  let e := QuotientGroup.quotientMulEquivOfEq (relative_frattini hPhi).symm
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

/-- Kernel containment uses relative normalization of L by T. -/
theorem qL_kernel_le_Q
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    d.qL.ker ≤ (Q T L).subgroupOf L := by
  rw [d.qL_ker]
  exact subgroupOf_mono L (pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer hTL))

variable [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- Coordinates are the literal quotient map, with only additive type tags. -/
@[expose] def quotientCoordinates : S F L →*
    Multiplicative (Additive (S F L ⧸ V.subgroupOf (S F L))) where
  toFun s := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' _ s))
  map_one' := (QuotientGroup.mk' _).map_one
  map_mul' := (QuotientGroup.mk' _).map_mul

omit [Finite G] [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))] in
theorem quotientCoordinates_surjective : Function.Surjective
    (quotientCoordinates (F := F) (L := L) (V := V)) :=
  QuotientGroup.mk'_surjective _

omit [Finite G] [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))] in
theorem quotientCoordinates_ker :
    (quotientCoordinates (F := F) (L := L) (V := V)).ker = V.subgroupOf (S F L) := by
  ext s
  exact QuotientGroup.eq_one_iff s

/-- The quotient action for the original qL, with its representative formula. -/
theorem exists_quotient_representation
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅S F L, Q T L⁆ ≤ V) :
    ∃ ρ : Representation (ZMod 2) BinaryLinearThree.Group
        (Additive (S F L ⧸ V.subgroupOf (S F L))),
      ∀ l : L, ∀ s : S F L,
        (quotientCoordinates (F := F) (L := L) (V := V) ⟨(l : G) * (s : G) * (l : G)⁻¹,
          (mem_normalizer_iff.mp (L_normalizes_S l.property) s).mp s.property⟩).toAdd =
        ρ (d.qL l) (quotientCoordinates s).toAdd := by
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action L (S F L) V
    L_normalizes_S d.natural.chosen.normalizes inferInstance
  have hkill : d.qL.ker ≤ α.ker := (qL_kernel_le_Q d hTL).trans
    (quotient_conjugation_action_kills_commutator_layer L (S F L) V (Q T L)
      inferInstance L_normalizes_S hcomm α hα)
  let β := d.qL.liftOfSurjective d.qL_surjective ⟨α, hkill⟩
  have hβ (l : L) : β (d.qL l) = α l :=
    d.qL.liftOfRightInverse_comp_apply (Function.surjInv d.qL_surjective)
      (Function.rightInverse_surjInv d.qL_surjective) ⟨α, hkill⟩ l
  let ρ : Representation (ZMod 2) BinaryLinearThree.Group
      (Additive (S F L ⧸ V.subgroupOf (S F L))) := {
    toFun g := (β g).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      ext v
      change β 1 v.toMul = v.toMul
      rw [map_one]
      rfl
    map_mul' g k := by
      ext v
      change β (g * k) v.toMul = β g (β k v.toMul)
      rw [map_mul]
      rfl }
  refine ⟨ρ, ?_⟩
  intro l s
  change QuotientGroup.mk' _ _ = β (d.qL l) (QuotientGroup.mk' _ s)
  rw [hβ]
  exact (hα l s).symm

/-- The action is on the actual S/V carrier and is marked by the original qL. -/
structure QuotientAction where
  representation : Representation (ZMod 2) BinaryLinearThree.Group
    (Additive (S F L ⧸ V.subgroupOf (S F L)))
  equivariant (l : L) (s : S F L) :
    (quotientCoordinates (F := F) (L := L) (V := V)
      ⟨(l : G) * (s : G) * (l : G)⁻¹,
        (mem_normalizer_iff.mp (L_normalizes_S l.property) s).mp s.property⟩).toAdd =
      representation (d.qL l) (quotientCoordinates s).toAdd

/-- Construct the descended action, rather than assume an action witness. -/
noncomputable def quotientAction
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅S F L, Q T L⁆ ≤ V) : QuotientAction d where
  representation := (exists_quotient_representation d hTL hcomm).choose
  equivariant := (exists_quotient_representation d hTL hcomm).choose_spec

/-- The representative law uniquely determines the descended representation. -/
theorem QuotientAction.representation_unique (a b : QuotientAction d) :
    a.representation = b.representation := by
  ext g v
  obtain ⟨l, rfl⟩ := d.qL_surjective g
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (V.subgroupOf (S F L)) v.toMul
  have hv : (quotientCoordinates s).toAdd = v := hs
  rw [← hv, ← a.equivariant, ← b.equivariant]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition
