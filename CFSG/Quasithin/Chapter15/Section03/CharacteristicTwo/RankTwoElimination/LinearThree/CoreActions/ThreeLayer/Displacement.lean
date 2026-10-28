module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement.PlaneAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Frattini
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Full displacement by the actual plane residual

Write Q = [O₂(L), L]. The center marking transports U = [V,Y_L] to a
binary plane. Its setwise stabilizer is the image of L ∩ N_G(U). Since
Y_L is two-perfect and S ∩ L is a normalizing two-group, the supplied
parabolic equality identifies the image of Y_L with the genuine two-residual
of that stabilizer. This residual displaces both dual summands of Q/Z(Q).
Lifting through the layer map gives [Q,Y_L] Z(Q) = Q, and Z(Q) ≤ Φ(Q)
then gives [Q,Y_L] = Q.

Both layers use the same quotient marking. Every order-four subgroup of the
natural center is allowed, so the calculation retains either plane orientation.
The preceding local geometry and the existence of the C.1.34 layers remain
inputs of this conditional action calculation.

Source: Aschbacher–Smith, C.1.34(3), printed pp.136–137, and the third-case
paragraph of 15.3.23, printed p.1129 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "Res" => Matrix.PSL3Two.MarkedAutomorphisms.residual

/-- The component quotient in the common natural/dual marking. -/
noncomputable def actorMap {L : Subgroup G} (e : (L ⧸ pCore 2 L) ≃* SL) : L →* SL :=
  e.toMonoidHom.comp (QuotientGroup.mk' _)

/-- The actual subgroup of the natural center, in its supplied coordinates. -/
noncomputable def coordinatePlane {L Z : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (U : Subgroup G) :
    Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2 ((U.subgroupOf Z).map (naturalCoordinates m).toMonoidHom).toAddSubgroup

private lemma coordinatePlane_mem {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (z : Z) :
    (naturalCoordinates m z).toAdd ∈ coordinatePlane m U ↔ (z : G) ∈ U := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (naturalCoordinates m).injective he ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

private lemma coordinatePlane_card {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (hUZ : U ≤ Z) :
    Nat.card (coordinatePlane m U) = Nat.card U := by
  let f : U → coordinatePlane m U := fun u =>
    ⟨(naturalCoordinates m ⟨u, hUZ u.property⟩).toAdd,
      (coordinatePlane_mem m _).mpr u.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      have hh := (naturalCoordinates m).injective
        (congrArg (fun x : coordinatePlane m U => Multiplicative.ofAdd (x : W)) huv)
      exact congrArg (fun z : Z => (z : G)) hh
    · intro v
      obtain ⟨z, hz⟩ := (naturalCoordinates m).surjective (Multiplicative.ofAdd v.val)
      have hzU : (z : G) ∈ U := (coordinatePlane_mem m z).mp (by rw [hz]; exact v.property)
      exact ⟨⟨z, hzU⟩, Subtype.ext (congrArg Multiplicative.toAdd hz)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

variable [Finite G]

private lemma normalizer_image {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (hUZ : U ≤ Z) :
    ((L ⊓ normalizer (U : Set G)).subgroupOf L).map (actorMap e) =
      stabilizer (coordinatePlane m U) := by
  have hiff (l : L) : actorMap e l ∈ stabilizer (coordinatePlane m U) ↔
      (l : G) ∈ normalizer (U : Set G) := by
    rw [stabilizer, MulAction.mem_stabilizer_set' (Set.toFinite _)]
    constructor
    · intro h
      apply mem_normalizer_fintype
      intro u hu
      have he := h ((coordinatePlane_mem m ⟨u, hUZ hu⟩).mpr hu)
      change ρ (e (QuotientGroup.mk' _ l)) (naturalCoordinates m ⟨u, hUZ hu⟩).toAdd ∈ coordinatePlane m U at he
      rw [← naturalCoordinates_intertwining m l ⟨u, hUZ hu⟩] at he
      exact (coordinatePlane_mem m _).mp he
    · intro hn v hv
      obtain ⟨z, hz⟩ := (naturalCoordinates m).surjective (Multiplicative.ofAdd v)
      have hu : (z : G) ∈ U := (coordinatePlane_mem m z).mp (by rw [hz]; exact hv)
      have hc := (coordinatePlane_mem m (layerConjugate L Z m.normalized l z)).mpr
        ((hn z).mp hu)
      rw [naturalCoordinates_intertwining, hz] at hc
      exact hc
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (hiff l).mpr hl.2
  · intro hg
    obtain ⟨l, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    exact ⟨l, ⟨l.property, (hiff l).mp hg⟩, rfl⟩

/-- The image of the genuine Y_L is the two-residual of the plane stabilizer. -/
theorem YL_residual_image (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    {U : Subgroup G} (hUZ : U ≤ coreCenter L)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hpar : YL d L ⊔ (d.S ⊓ L) = L ⊓ normalizer (U : Set G)) :
    ((YL d L).subgroupOf L).map (actorMap e) = Res (stabilizer (coordinatePlane m U)) := by
  have hYL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hp : IsPPerfect 2 ((YL d L).subgroupOf L) :=
    (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L).of_surjective
      (subgroupOfEquivOfLe hYL).symm.toMonoidHom (subgroupOfEquivOfLe hYL).symm.surjective
  have hS : IsPGroup 2 ((d.S ⊓ L).subgroupOf L) :=
    (d.T.isPGroup'.to_le (show d.S ⊓ L ≤ (d.T : Subgroup G) from inf_le_left.trans inf_le_left)).comap_subtype
  have hn : (d.S ⊓ L).subgroupOf L ≤ normalizer (((YL d L).subgroupOf L) : Set L) := by
    rw [← subgroupOf_normalizer_eq hYL]
    exact fun s hs => hSYL hs.1
  have hr := embedded_pResidual_join_pGroup ((YL d L).subgroupOf L)
    ((d.S ⊓ L).subgroupOf L) hp hS hn
  rw [← subgroupOf_sup hYL inf_le_right, hpar] at hr
  rw [← hr, map_embedded_pResidual, normalizer_image m hUZ]
  rfl


private noncomputable def layerMap {L Q Z : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {e : (L ⧸ pCore 2 L) ≃* SL} {σ : Representation (ZMod 2) SL V}
    (n : LayerModel L Q Z e σ) : Q →* Multiplicative V := by
  let _ := n.lower_normal
  exact n.quotientIso.toMonoidHom.comp (QuotientGroup.mk' _)

omit [Finite G] in
private lemma layerMap_surjective {L Q Z : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {e : (L ⧸ pCore 2 L) ≃* SL} {σ : Representation (ZMod 2) SL V}
    (n : LayerModel L Q Z e σ) : Function.Surjective (layerMap n) := by
  let _ := n.lower_normal
  exact n.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
private lemma layerMap_ker {L Q Z : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {e : (L ⧸ pCore 2 L) ≃* SL} {σ : Representation (ZMod 2) SL V}
    (n : LayerModel L Q Z e σ) : (layerMap n).ker = Z.subgroupOf Q := by
  let _ := n.lower_normal
  ext q
  change n.quotientIso (QuotientGroup.mk' _ q) = 1 ↔ _
  rw [map_eq_one_iff n.quotientIso n.quotientIso.injective]
  exact QuotientGroup.eq_one_iff q

omit [Finite G] in
private lemma commutator_sup_lower {L Q Z Y : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {e : (L ⧸ pCore 2 L) ≃* SL} {σ : Representation (ZMod 2) SL V}
    (n : LayerModel L Q Z e σ) (hYL : Y ≤ L)
    (hfull : Coinvariants.ker (σ.comp ((Y.subgroupOf L).map (actorMap e)).subtype) = ⊤) :
    ⁅Q,Y⁆ ⊔ Z = Q := by
  let H := ⁅Q,Y⁆
  have hHQ : H ≤ Q := le_normalizer_iff_commutator_le_left.mp (hYL.trans n.normalized)
  let f := layerMap n
  let D : Submodule (ZMod 2) V :=
    AddSubgroup.toZModSubmodule 2 ((H.subgroupOf Q).map f).toAddSubgroup
  have hd : Coinvariants.ker (σ.comp ((Y.subgroupOf L).map (actorMap e)).subtype) ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩, rfl⟩
    obtain ⟨l, hl, he⟩ := g.property
    obtain ⟨q, hq⟩ := layerMap_surjective n (Multiplicative.ofAdd v)
    let c : Q := layerConjugate L Q n.normalized l q * q⁻¹
    have hc : (c : G) ∈ H := by
      change ⁅(l : G), (q : G)⁆ ∈ ⁅Q,Y⁆
      rw [commutator_comm Q Y]
      exact commutator_mem_commutator hl q.property
    refine ⟨c, hc, ?_⟩
    apply Multiplicative.toAdd.injective
    change (f c).toAdd = σ g v - v
    have hi := n.intertwining l q
    change (f (layerConjugate L Q n.normalized l q)).toAdd =
      σ (actorMap e l) (f q).toAdd at hi
    change actorMap e l = (g : SL) at he
    rw [he, hq] at hi
    change (f (layerConjugate L Q n.normalized l q * q⁻¹)).toAdd = _
    rw [map_mul, map_inv]
    simpa only [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg, f] using
      congrArg₂ (fun x y : V => x - y) hi (congrArg Multiplicative.toAdd hq)
  have hD : D = ⊤ := top_unique (hfull ▸ hd)
  apply le_antisymm (sup_le hHQ n.lower_le)
  intro q hq
  have hmem : (f ⟨q,hq⟩).toAdd ∈ D := hD ▸ Submodule.mem_top
  obtain ⟨h, hh, he⟩ := hmem
  change f h = f ⟨q,hq⟩ at he
  have hz : h⁻¹ * ⟨q,hq⟩ ∈ Z.subgroupOf Q := by
    rw [← layerMap_ker n]
    change f (h⁻¹ * ⟨q,hq⟩) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hh' : (h : G) ∈ H ⊔ Z := (show H ≤ H ⊔ Z from le_sup_left) hh
  have hz' : (h : G)⁻¹ * q ∈ H ⊔ Z := (show Z ≤ H ⊔ Z from le_sup_right) hz
  simpa only [mul_inv_cancel_left] using (H ⊔ Z).mul_mem hh' hz'

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
open Displacement
variable {G : Type*} [Group G] [Finite G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

/-- Full displacement on the actual doubled-dual quotient Q/Z(Q). -/
theorem YL_commutator_sup_center (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel L (commutatorCore L) (coreCenter L) e (DualCopies (ZMod 2) 2))
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hU : Nat.card (⁅d.V,YL d L⁆ : Subgroup G) = 4)
    (hUZ : ⁅d.V,YL d L⁆ ≤ coreCenter L)
    (hpar : YL d L ⊔ (d.S ⊓ L) = L ⊓ normalizer ((⁅d.V,YL d L⁆ : Subgroup G) : Set G)) :
    ⁅commutatorCore L,YL d L⁆ ⊔ coreCenter L = commutatorCore L := by
  have hYL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  apply commutator_sup_lower n hYL
  rw [YL_residual_image d L m hUZ hSYL hpar]
  exact dual_copies_displacement _ ((coordinatePlane_card m hUZ).trans hU)


/-- The plane residual fully displaces Q in the third C.1.34 case. -/
theorem YL_full_displacement (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel L (commutatorCore L) (coreCenter L) e (DualCopies (ZMod 2) 2))
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hU : Nat.card (⁅d.V,YL d L⁆ : Subgroup G) = 4)
    (hUZ : ⁅d.V,YL d L⁆ ≤ coreCenter L)
    (hpar : YL d L ⊔ (d.S ⊓ L) = L ⊓ normalizer ((⁅d.V,YL d L⁆ : Subgroup G) : Set G)) :
    ⁅commutatorCore L,YL d L⁆ = commutatorCore L := by
  have hYL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  exact eq_core_of_sup_center L _ m n
    (le_normalizer_iff_commutator_le_left.mp (hYL.trans n.normalized))
    (YL_commutator_sup_center d L m n hSYL hU hUZ hpar)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
end
