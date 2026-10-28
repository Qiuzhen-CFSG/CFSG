module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceScalarAction

/-!
# The source triple-cover inference and exact marked E₄ automizer

The marked rank-two hypothesis excludes the simple A₆ alternative and
selects a compatible equivalence with the concrete hexacode triple cover.
The two actual source marks provide cubic coordinates on L₁/O₂(L₁).
Every element of N_M(L₁) preserves both axes; an element of T∩L inverts
only the second. The simultaneous cubic inverter lifted from the source
wreath overgroup moves the cover scalar. That motion survives the intrinsic
two-core quotient, since a cubic central element cannot lie in a two-group.
The independent-sign calculation therefore gives an actual equivalence of
the automizer image with E₄, for M = N_G(L).

`source_tripleCover_and_automizer` consumes the earlier compatible model
alternative, 13.2.2(3), the moving component data and the source clauses
13.8.13 and 13.7.3(9). It proves both requested inferences. In particular,
no residual-image identity, cubic order, prescribed automizer image, scalar
inversion or identity [L₁,T] = L₁ remains as a premise. The exact E₄ route
uses the accepted source wreath construction beyond its rank and quotient
order consequences. The containing source-theorem owner supplies the named
earlier results and the moving component data.

Here `one L T V₁` and `markedResidual L T V₁` are definitionally the same
ambient subgroup O²(N_{LT}(V₁)). All actions retain literal conjugation.

Source: Aschbacher–Smith, 13.8.16(1), printed p.952 (PDF p.969), standing
pp.946–947; Notation 13.2.1 and Lemma 13.2.2, pp.877–878.
-/

@[expose] public section
open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
namespace SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- Motion of the actual cover scalar survives in the first cubic coordinate
of the literal R/O₂(R). The proof excludes a cubic element from a two-group. -/
theorem scalar_moves_in_coordinates (L T V V₁ M : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hn : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hML : M ≤ normalizer (L : Set G))
    (hf : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hz : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hx : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (hmove : ∃ m : (M ⊓ normalizer (one L T V₁ : Set G) : Subgroup G),
      coverAction d M hML (inclusion inf_le_left m) Atlas.Codes.hexEvenZ ≠ Atlas.Codes.hexEvenZ) :
    ∃ m, ∃ c : Model.C3, coordinateAction (one L T V₁) M
      (Coordinates.equiv L T V₁ hn hTV hf hz hx) m (c, 1) ≠ (c, 1) := by
  obtain ⟨m, hm⟩ := hmove
  let R := one L T V₁
  have hRL : R ≤ L := one_le_L_of_factorization L T V₁ hn hf
  have hZR : zero L ≤ R := zero_le_one_of_factorization L T V₁ hf
  let f := d.subgroupMap R hRL
  let e := Coordinates.equiv L T V₁ hn hTV hf hz hx
  have hZ : Atlas.Codes.hexEvenZ ∈ center Model.Cover := by
    rw [← Representation.Hexacode.even_kernel_eq_center, Atlas.Codes.hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hzi := hZ
  rw [← d.zero_image] at hzi
  obtain ⟨l, hl, he⟩ := hzi
  let z : zero L := ⟨l.val, hl⟩
  let r : R := inclusion hZR z
  have hr : f r = Atlas.Codes.hexEvenZ := he
  let q := QuotientGroup.mk' (pCore 2 (zero L)) z
  refine ⟨m, Coordinates.zeroEquiv L hz q, ?_⟩
  intro hfix
  have hq : automizerAction R M m (zeroCoreMap L T V₁ hn hf q) =
      zeroCoreMap L T V₁ hn hf q := by
    apply e.injective
    rw [← Coordinates.equiv_zero L T V₁ hn hTV hf hz hx q] at hfix
    change e (automizerAction R M m (e.symm (e _))) = e _ at hfix
    rwa [MulEquiv.symm_apply_apply] at hfix
  have hqr : zeroCoreMap L T V₁ hn hf q = QuotientGroup.mk' (pCore 2 R) r :=
    localCoreMap_mk _ _ _ _ z
  rw [hqr] at hq
  let r' := R.normalizerMonoidHom (inclusion inf_le_right m) r
  have hp : r' * r⁻¹ ∈ pCore 2 R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 R) (r' * r⁻¹) = 1
    rw [map_mul, map_inv]
    have hq' := hq
    change quotientAction R _ inf_le_right m (QuotientGroup.mk' (pCore 2 R) r) =
      QuotientGroup.mk' (pCore 2 R) r at hq'
    rw [quotientAction_mk] at hq'
    rw [show QuotientGroup.mk' (pCore 2 R) r' = QuotientGroup.mk' (pCore 2 R) r from hq',
      mul_inv_cancel]
  let a := coverAction d M hML (inclusion inf_le_left m)
  have hab : f (r' * r⁻¹) = a Atlas.Codes.hexEvenZ * Atlas.Codes.hexEvenZ⁻¹ := by
    rw [map_mul, map_inv]
    change d.subgroupMap R hRL (R.normalizerMonoidHom (inclusion inf_le_right m) r) *
      (f r)⁻¹ = _
    rw [d.subgroupMap_conjugation R M hRL hML m r, hr]
  have haz : a Atlas.Codes.hexEvenZ ∈ center Model.Cover := by
    have hmap := characteristic_iff_map_eq.mp
      (inferInstance : (center Model.Cover).Characteristic) a
    rw [← hmap]
    exact mem_map_of_mem a.toMonoidHom hZ
  have h3 : IsPGroup 3 (center Model.Cover) := IsPGroup.of_card (n := 1)
    (by simpa using Representation.Hexacode.even_center_card)
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
    ((pCore 2 R).map f) (center Model.Cover) (pCore_isPGroup.map f) h3
  have hone : f (r' * r⁻¹) = 1 := hd.le_bot
    ⟨mem_map_of_mem f hp, hab.symm ▸ (center Model.Cover).mul_mem haz ((center Model.Cover).inv_mem hZ)⟩
  rw [hab, mul_inv_eq_one] at hone
  exact hm hone

/-- Exact image calculation from the source marks and actual scalar motion.
The remaining motion premise is discharged below by the source pair. -/
noncomputable def automizerEquivE4_of_scalar_motion (L T V V₁ M : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hn : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hML : M ≤ normalizer (L : Set G)) (hTM : T ≤ M)
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (hf : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hmove : ∃ m : (M ⊓ normalizer (one L T V₁ : Set G) : Subgroup G),
      coverAction d M hML (inclusion inf_le_left m) Atlas.Codes.hexEvenZ ≠ Atlas.Codes.hexEvenZ) :
    (automizerAction (one L T V₁) M).range ≃* E4 := by
  have hz := CubicOrders.zero_core_card d
  have hx := CubicOrders.plus_core_card d T V₁ hn S hS hTV hV₁V hc
  let e := Coordinates.equiv L T V₁ hn hTV hf hz hx
  have ha := Coordinates.axes_preserved L T V₁ hn hTV hf hz hx V M hLV d hML S hS hV₁V hc
  let c := MulAut.congr e
  have hr : (automizerAction (one L T V₁) M).range.map c.toMonoidHom =
      (coordinateAction (one L T V₁) M e).range := (MonoidHom.range_comp _ _).symm
  exact ((c.subgroupMap (automizerAction (one L T V₁) M).range).trans
    (MulEquiv.subgroupCongr hr)).trans
      (Diagonal.imageEquivE4 (coordinateAction (one L T V₁) M e) ha.1 ha.2
        (Coordinates.derivedFlip_mem L T V₁ hn hTV hf hz hx M hTM)
        (scalar_moves_in_coordinates L T V V₁ M hLV d hn hTV hML hf hz hx hmove))

/-- The actual E₄ automizer in the moving L₃(2) source branch. All marking,
cubic-order, inverter and scalar-motion premises are discharged. The two
remaining source clauses are precisely 13.8.13 and 13.7.3(9), besides the
explicit earlier factorization 13.2.2(3). -/
noncomputable def source_automizerEquivE4
    (L V V₁ H G₁ K K₀ : Subgroup G) (T : Sylow 2 G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (hf : one L T V₁ = plus L T V₁ ⊔ zero L)
    (s : WreathOvergroup.SourcePair.Input H (one L T V₁) T K K₀)
    (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ normalizer (L : Set G))
    (htheta : one L T V₁ =
      closure {x : G | x ∈ H ⊓ normalizer (L : Set G) ∧ orderOf x = 3}) :
    (automizerAction (one L T V₁) (normalizer (L : Set G))).range ≃* E4 :=
  automizerEquivE4_of_scalar_motion L T V V₁ (normalizer (L : Set G)) hLV d hTL hTV
    le_rfl hTL (T.subtype le_sup_right) rfl hV₁V hc hf
    (SourceScalarAction.normalizer_scalar_moves_of_source_pair L V V₁ H G₁ K K₀ T
      hLV d hTL hV₁V s hH hex htheta)

/-- The two inferences used together in 13.8.16(1): rank two selects the
compatible concrete triple cover, and its marked automizer is E₄. The model
alternative is the earlier natural-module result 13.5.2; `hfactor` is the
earlier clause 13.2.2(3), applicable after selecting the covered branch.
The source assembly supplies the moving pair and clauses 13.8.13 and 13.7.3(9).
No rank-to-family tag, prescribed image, or commutator-generation premise occurs. -/
theorem source_tripleCover_and_automizer
    (L V V₁ H G₁ K K₀ : Subgroup G) (T : Sylow 2 G)
    (hLV : L ≤ normalizer (V : Set G))
    (hmodels : Nonempty (SimplePointModel L V hLV) ∨ Nonempty (CoverPointModel L V hLV))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (hrank : primeRank 3 (one L T V₁) = 2)
    (hfactor : CoverPointModel L V hLV → one L T V₁ = plus L T V₁ ⊔ zero L)
    (s : WreathOvergroup.SourcePair.Input H (one L T V₁) T K K₀)
    (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ normalizer (L : Set G))
    (htheta : one L T V₁ =
      closure {x : G | x ∈ H ⊓ normalizer (L : Set G) ∧ orderOf x = 3}) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty ((automizerAction (one L T V₁)
        (normalizer (L : Set G))).range ≃* E4) := by
  obtain ⟨d⟩ := coverPointModel_of_marked_rank L T V V₁ hLV hmodels T.isPGroup' hTL hV₁V hc hrank
  exact ⟨⟨d.quotientEquiv⟩, ⟨source_automizerEquivE4 L V V₁ H G₁ K K₀ T hLV d
    hTL hTV hV₁V hc (hfactor d) s hH hex htheta⟩⟩

end SourceAssembly
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
end
