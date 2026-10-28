module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NormalAtT
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Centralizers
public import Theory.SpecificGroups.AlternatingSix.M10.SylowSemidihedral
public import GorensteinWalter.PGL2SplitTorus
public import Theory.GroupTheory.SymmetricSixQuotientObstruction
import Mathlib.Tactic

/-!
# The symmetric-six obstruction in the nonfull A₆ source branches

Source 2.5.18 makes the original K normal in C_G(t), and its centralizer
supplements H there. The actual action kernel in H is O₂(H). Consequently
any S₆ overgroup of K in C_G(t) embeds in the literal quotient H/O₂(H).
For M₁₀ and PGL₂(9), this would be an isomorphism by order, contradicting
an element of order eight in those quotients.

The fixed-subgroup adapter keeps the actual action of t and all subgroup
inclusions. In particular the marked A₈ transposition centralizer supplies
the S₆ required by the original componenthood argument.

Source: Aschbacher–Smith 2.5.21, printed p.566, using 2.5.18, printed p.560.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection

private def fixedSubgroupEquivCentralizer
    {G : Type*} [Group G] (X : Subgroup G) (t : G) (a : MulAut X)
    (ha : ∀ x : X, (a x : G) = t * (x : G) * t⁻¹) :
    a.fixedSubgroup ≃* (X ⊓ centralizer ({t} : Set G) : Subgroup G) where
  toFun x := ⟨x, x.val.property, mem_centralizer_singleton_iff.mpr (by
    have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup a x.val).mp x.property)
    rw [ha] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm)⟩
  invFun x := ⟨⟨x, x.property.1⟩, (MulAut.mem_fixedSubgroup a _).mpr (by
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def onePairFixedEquiv :
    (MulAut.conjNormal (H := alternatingGroup (Fin 8))
      Theory.SpecificGroups.SymmetricEight.Involutions.onePair).fixedSubgroup ≃*
      Equiv.Perm (Fin 6) :=
  (fixedSubgroupEquivCentralizer (alternatingGroup (Fin 8))
    Theory.SpecificGroups.SymmetricEight.Involutions.onePair
    (MulAut.conjNormal (H := alternatingGroup (Fin 8))
      Theory.SpecificGroups.SymmetricEight.Involutions.onePair) (fun _ => rfl)).trans
    BinaryNaturalDual.FourActors.PermutationCatalogue.onePairCentralizerEquiv

theorem a8_marked_fixed_equiv
    {G : Type*} [Group G] (X : Subgroup G) (t : G) (a : MulAut X)
    (ha : ∀ x : X, (a x : G) = t * (x : G) * t⁻¹)
    (eX : X ≃* alternatingGroup (Fin 8))
    (he : MulAut.congr eX a = MulAut.conjNormal (H := alternatingGroup (Fin 8))
      Theory.SpecificGroups.SymmetricEight.Involutions.onePair) :
    Nonempty ((X ⊓ centralizer ({t} : Set G) : Subgroup G) ≃* Equiv.Perm (Fin 6)) := by
  let e := MulAut.fixedSubgroupCongr eX a
  rw [he] at e
  exact ⟨(fixedSubgroupEquivCentralizer X t a ha).symm.trans (e.trans onePairFixedEquiv)⟩

private theorem source_quotient_transport
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (t : G) (hHJ : H ≤ centralizer ({t} : Set G))
    (hn : (K.subgroupOf (centralizer ({t} : Set G))).Normal) :
    let J := centralizer ({t} : Set G)
    let D := K.subgroupOf J
    let A := H.subgroupOf J
    let N := centralizer (D : Set J)
    letI := hn
    Nonempty ((A ⧸ N.subgroupOf A) ≃* (H ⧸ pCore 2 H)) := by
  let J := centralizer ({t} : Set G)
  let D := K.subgroupOf J
  let A := H.subgroupOf J
  let N := centralizer (D : Set J)
  let := hn
  have hKJ : K ≤ J := c.component_le.trans hHJ
  let eH : A ≃* H := subgroupOfEquivOfLe hHJ
  have hmap : (N.subgroupOf A).map eH.toMonoidHom = pCore 2 H := by
    rw [← MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen,
      MulAut.conjNormal_ker_eq_centralizer]
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩ b hb
      apply Subtype.ext
      exact congrArg (fun y : J => (y : G)) (ha ⟨b, hKJ hb⟩ hb)
    · intro hx
      refine ⟨eH.symm x, ?_, eH.apply_symm_apply x⟩
      intro k hk
      apply Subtype.ext
      exact congrArg (fun y : H => (y : G)) (hx ⟨k, c.component_le hk⟩ hk)
  exact ⟨QuotientGroup.congr _ _ eH hmap⟩

theorem source_symmetric_six_false
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    {Q : Type*} [Group Q] [Finite Q]
    (eQ : (H ⧸ pCore 2 H) ≃* Q)
    (hcard : Nat.card Q = 720) (h8 : ∃ q : Q, orderOf q = 8)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (C : Subgroup G) (hKC : K ≤ C) (hCt : C ≤ centralizer ({t} : Set G))
    (eC : C ≃* Equiv.Perm (Fin 6)) : False := by
  let eKH := (subgroupOfEquivOfLe c.component_le).trans eK
  let : (K.subgroupOf H).Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) _ eKH c.component
  let J := centralizer ({t} : Set G)
  have hHJ : H ≤ J :=
    (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  have hKJ : K ≤ J := c.component_le.trans hHJ
  let D := K.subgroupOf J
  let A := H.subgroupOf J
  let E := C.subgroupOf J
  let N := centralizer (D : Set J)
  let : D.Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ)
  let eD := (subgroupOfEquivOfLe hKJ).trans eK
  let : Nontrivial D := eD.symm.injective.nontrivial
  have hDE : D ≤ E := fun _ hx => hKC hx
  let eE := (subgroupOfEquivOfLe hCt).trans eC
  have hsupp : A ⊔ N = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hHJ,
      Subgroup.map_centralizer_subtype, map_subgroupOf_eq_of_le hKJ,
      ← MonoidHom.range_eq_map, range_subtype]
    exact (source_normal_component_centralizer_supplement
      c hG hempty hgen hb hstar t ht htC htZ).symm
  obtain ⟨e⟩ := source_quotient_transport c hG hempty hgen t hHJ (show D.Normal from inferInstance)
  exact symmetric_six_quotient_obstruction D A E hDE eE hsupp (e.trans eQ) hcard h8


/-- Either literal nonfull A₆ quotient contradicts an S₆ overgroup of K in G_t. -/
theorem source_nonfull_a6_symmetric_six_false
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hQ : Nonempty ((H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F))
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (C : Subgroup G) (hKC : K ≤ C) (hCt : C ≤ centralizer ({t} : Set G))
    (eC : C ≃* Equiv.Perm (Fin 6)) : False := by
  rcases hQ with hQ | hQ
  · obtain ⟨eQ⟩ := hQ
    have h8 : ∃ q : AlternatingSix.M10.extension, orderOf q = 8 := by
      let P : Sylow 2 AlternatingSix.M10.extension := default
      let e := AlternatingSix.M10.sylowTwoEquivSemidihedral P
      refine ⟨(e.symm (Semidihedral.standardRotation 4 (by decide)) : P), ?_⟩
      rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, Semidihedral.standardRotation_order]
      norm_num
    exact source_symmetric_six_false c hG hempty hgen hb hstar eK eQ
      AlternatingSix.M10.Action.card_extension h8 t ht htC htZ C hKC hCt eC
  · obtain ⟨eQ⟩ := hQ
    have h8 : ∃ q : GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F,
        orderOf q = 8 := by
      obtain ⟨U, _, hcyc, hcard, _⟩ := GorensteinWalter.pgl2_split_torus_reflection_data
        Atlas.Comparisons.Exceptional.Nine.F
      let : IsCyclic U := hcyc
      obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
      refine ⟨x, ?_⟩
      rw [Subgroup.orderOf_coe, hx, hcard, Atlas.Comparisons.Exceptional.Nine.card]
    have hc : Nat.card (GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) = 720 := by
      rw [GorensteinWalter.pgl2_card_formula, Atlas.Comparisons.Exceptional.Nine.card]
      norm_num
    exact source_symmetric_six_false c hG hempty hgen hb hstar eK eQ
      hc h8 t ht htC htZ C hKC hCt eC

/-- Apply the obstruction to the actual fixed group of a containing component. -/
theorem source_nonfull_a6_fixed_symmetric_six_false
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hQ : Nonempty ((H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F))
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (X : Subgroup G) (hKX : K ≤ X) (a : MulAut X)
    (hact : ∀ x : X, (a x : G) = t * (x : G) * t⁻¹)
    (eFix : a.fixedSubgroup ≃* Equiv.Perm (Fin 6)) : False := by
  have hKJ : K ≤ centralizer ({t} : Set G) := c.component_le.trans
    (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  exact source_nonfull_a6_symmetric_six_false c hG hempty hgen hb hstar eK hQ
    t ht htC htZ (X ⊓ centralizer ({t} : Set G)) (le_inf hKX hKJ) inf_le_right
    ((fixedSubgroupEquivCentralizer X t a hact).symm.trans eFix)

/-- The marked transposition alternative of 2.5.19 cannot occur in either
nonfull A₆ quotient branch of 2.5.21. -/
theorem source_nonfull_a6_transposition_false
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hQ : Nonempty ((H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F))
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (X : Subgroup G) (hKX : K ≤ X) (a : MulAut X)
    (hact : ∀ x : X, (a x : G) = t * (x : G) * t⁻¹)
    (eX : X ≃* alternatingGroup (Fin 8))
    (he : MulAut.congr eX a = MulAut.conjNormal (H := alternatingGroup (Fin 8))
      Theory.SpecificGroups.SymmetricEight.Involutions.onePair) : False := by
  obtain ⟨eC⟩ := a8_marked_fixed_equiv X t a hact eX he
  have hKJ : K ≤ centralizer ({t} : Set G) := c.component_le.trans
    (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  exact source_nonfull_a6_symmetric_six_false c hG hempty hgen hb hstar eK hQ
    t ht htC htZ (X ⊓ centralizer ({t} : Set G)) (le_inf hKX hKJ) inf_le_right eC

end CFSG.Quasithin.Chapter2.Section05.Overcomponents
