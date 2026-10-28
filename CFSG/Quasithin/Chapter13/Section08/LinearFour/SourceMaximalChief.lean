module
public import Theory.Representation.HexacodeAction.CentralChiefCount
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Transport
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.MaximalQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions

/-!
# The original central residual on the maximal chief quotient

The canonical covered quotient maps the literal L₀ onto its center. Choose
an L-normal subgroup maximal below the given generated two-group span and
above V. The seed commutator relation makes the intersection of this span
with L₀ surject onto the maximal quotient. Its faithful binary action then
contributes half its binary degree to every complete chief series of L₀.
All scalar and character data are constructed from the same covered map.

The final application reduces the nine-factor bound to excluding order 64
for these literal maximal quotients. That exclusion, including the extra-line
tensor movement, is still required; it is not asserted here. The normal
nodes, generating seed and its commutator relation are explicit earlier
inputs. In particular these conditional results do not assert containment
of an arbitrary normalized ambient span in L.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Notation 13.2.1 and Lemma 13.8.30, printed pp.877 and 964.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- The same canonical quotient maps the actual central residual onto the
center of the covered model. No central-image marking is assumed. -/
theorem source_zero_cover_image (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms) :
    ((zero L).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
        center HexEvenAutomorphisms := by
  have hc : Nat.card (center (L ⧸ pCore 2 L)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans
      Representation.Hexacode.even_center_card
  have hr : residual (center (L ⧸ pCore 2 L)) = center (L ⧸ pCore 2 L) := by
    apply le_antisymm (residual_le _)
    intro x hx
    refine ⟨⟨x,hx⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (hc ▸ orderOf_dvd_natCard (⟨x,hx⟩ : center (L ⧸ pCore 2 L)))
  have hs : Source.starImage L (zero L) = center (L ⧸ pCore 2 L) := by
    rw [zero,star_residual L (centralPreimage L) (map_subtype_le _)]
    have hh : Source.starImage L (centralPreimage L) = center (L ⧸ pCore 2 L) := by
      unfold Source.starImage centralPreimage
      rw [←comap_subtype,comap_map_eq_self_of_injective L.subtype_injective,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    rw [hh,hr]
  rw [←map_map]
  change (Source.starImage L (zero L)).map e.toMonoidHom = _
  rw [hs]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (Subgroup.centerCongr e ⟨x,hx⟩).property
  · intro y hy
    refine ⟨(Subgroup.centerCongr e).symm ⟨y,hy⟩,
      ((Subgroup.centerCongr e).symm ⟨y,hy⟩).property,?_⟩
    exact congrArg Subtype.val ((Subgroup.centerCongr e).apply_symm_apply ⟨y,hy⟩)

/-- The intrinsic maximal quotient gives its binary degree bound on every
complete chief series of the original ambient subgroup L₀. Relative
normality, the intersections and the canonical quotient map are retained. -/
theorem exists_source_maximal_quotient_chief_bound
    (L : Subgroup G) (V U : NormalNode L) (hVU : V < U)
    (hp : IsPGroup 2 U.val) (S : Subgroup L) (hSU : S ≤ U.val)
    (hU : U.val = conjugateSpanBy S ⊤)
    (hseed : S ≤ V.val ⊔ ⁅S,(zero L).subgroupOf L⁆)
    (e : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms) :
    ∃ W : NormalNode L, V ≤ W ∧ W ⋖ U ∧
      U.val ≤ W.val ⊔ (zero L).subgroupOf L ∧
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        (Module.finrank Bit (Additive (Section W U)) = 6 ∨
          Module.finrank Bit (Additive (Section W U)) = 18) ∧
        ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
          Module.finrank Bit (Additive (Section W U)) ≤ 2 * t.noncentralTwoCount := by
  let X := (zero L).subgroupOf L
  let : X.Normal := normal_subgroupOf_of_le_normalizer (L_normalizes_zero L)
  obtain ⟨W,hVW,hWU,hcover,hbin,σ,hirr,hf,hσ,hdegree⟩ :=
    exists_source_maximal_quotient V U hVU hp X S hSU hU hseed e
      (source_zero_cover_image L e)
  let := hbin
  let := hirr
  refine ⟨W,hVW,hWU,hcover,hbin,hdegree,?_⟩
  intro t ht0 ht1
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : (π.comp X.subtype).range = center HexEvenAutomorphisms := by
    rw [MonoidHom.range_comp,range_subtype]
    exact source_zero_cover_image L e
  let d : BinaryConjugationSection X (U.val ⊓ X) (W.val ⊓ X)
      (σ.comp (π.comp X.subtype)) := by
    have q := source_intersection_coordinates W U X hWU.le hcover
    rw [←hσ] at q
    exact q
  let eX : X ≃* zero L := subgroupOfEquivOfLe (zero_le L)
  have ht := t.mapActor_complete eX.symm ht0 ht1
  have hc := Representation.Hexacode.binary_degree_le_twice_chief_count
    X (U.val ⊓ X) (W.val ⊓ X) σ hf (π.comp X.subtype) hπ d
      (t.mapActor eX.symm) ht.1 ht.2
  simpa only [ChiefSeries.mapActor_noncentralTwoCount] using hc

/-- Excluding order 64 for the literal maximal quotients discharges the
complete nine-factor premise. This is a conditional application, not a
proof of the still-required tensor movement exclusion. -/
theorem source_nine_factors_of_maximal_quotients_not_64
    (L : Subgroup G) (V U : NormalNode L) (hVU : V < U)
    (hp : IsPGroup 2 U.val) (S : Subgroup L) (hSU : S ≤ U.val)
    (hU : U.val = conjugateSpanBy S ⊤)
    (hseed : S ≤ V.val ⊔ ⁅S,(zero L).subgroupOf L⁆)
    (e : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms)
    (hlarge : ∀ W : NormalNode L, V ≤ W → W ⋖ U → Nat.card (Section W U) ≠ 64)
    (t : ChiefSeries (zero L)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    9 ≤ t.noncentralTwoCount := by
  obtain ⟨W,hVW,hWU,_,hbin,hdegree,hcount⟩ :=
    exists_source_maximal_quotient_chief_bound L V U hVU hp S hSU hU hseed e
  let := hbin
  have hn : Module.finrank Bit (Additive (Section W U)) ≠ 6 := by
    intro hd
    apply hlarge W hVW hWU
    change Nat.card (Additive (Section W U)) = 64
    rw [Module.natCard_eq_pow_finrank (K := Bit),hd]
    norm_num [Bit]
  have hc := hcount t ht0 ht1
  omega

end CFSG.Quasithin.Chapter13.Section08.LinearFour
