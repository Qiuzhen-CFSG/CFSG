module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.SylowFacts
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The marked Sylow-five product

For the product normalizer in Aschbacher, *Sporadic Groups* (1994), 47.2,
printed p.261, the first-coordinate map on P has kernel P ∩ E(C_G(E)).
Its image has order dividing ten, while the kernel order divides both 25
and 60. Thus the kernel has order five. The two marked product factors
are disjoint, so adjoining E gives all of P.

The component equivalence below is built from the second coordinate of
`RootFiveWitness.equiv`; the ambient component and inverter are preserved.
These facts feed the local-intersection assembly in `MarkedLocal`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {E : Subgroup G}

/-- The ambient inclusion given by the marked product isomorphism. -/
def modelEmbedding (W : RootFiveWitness D E) :
    DihedralGroup 5 × alternatingGroup (Fin 5) →* G :=
  (normalizer (E : Set G)).subtype.comp W.equiv.symm.toMonoidHom

theorem modelEmbedding_injective (W : RootFiveWitness D E) :
    Function.Injective (modelEmbedding W) :=
  (normalizer (E : Set G)).subtype_injective.comp W.equiv.symm.injective

theorem mem_component_iff (W : RootFiveWitness D E) (x : normalizer (E : Set G)) :
    (x : G) ∈ fiveComponent E ↔ (W.equiv x).1 = 1 := by
  rw [← W.component_factor]
  constructor
  · rintro ⟨a, ha, he⟩
    have hx : W.equiv.symm a = x := Subtype.ext he
    have hx' : a = W.equiv x := W.equiv.symm.injective (hx.trans (W.equiv.symm_apply_apply x).symm)
    exact hx' ▸ ha.1
  · intro hx
    exact ⟨W.equiv x, ⟨hx, mem_top _⟩, congrArg Subtype.val (W.equiv.symm_apply_apply x)⟩

theorem component_card (W : RootFiveWitness D E) : Nat.card (fiveComponent E) = 60 := by
  rw [← W.component_factor]
  change Nat.card (((⊥ : Subgroup (DihedralGroup 5)).prod (⊤ : Subgroup (alternatingGroup (Fin 5)))).map (modelEmbedding W)) = 60
  rw [card_map_of_injective (modelEmbedding_injective W)]
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_bot, card_top, one_mul, InvolutionGeometry.card_A5]

theorem disjoint_dihedral_component (W : RootFiveWitness D E) :
    Disjoint (E ⊔ zpowers W.inverter) (fiveComponent E) := by
  rw [← W.dihedral_factor, ← W.component_factor]
  apply disjoint_map (modelEmbedding_injective W)
  rw [disjoint_iff, eq_bot_iff]
  intro a ha
  exact Prod.ext ha.2.1 ha.1.2

theorem disjoint_E_component (W : RootFiveWitness D E) : Disjoint E (fiveComponent E) :=
  (disjoint_dihedral_component W).mono_left le_sup_left

omit [Finite G] in
/-- The component's embedding commutes with the original five-subgroup. -/
theorem component_centralizes_E : fiveComponent E ≤ centralizer (E : Set G) :=
  map_subtype_le _

/-- The second coordinate in the original, marked root-family isomorphism. -/
def componentEmbedding (W : RootFiveWitness D E) : alternatingGroup (Fin 5) →* G :=
  (modelEmbedding W).comp (MonoidHom.inr _ _)

theorem componentEmbedding_injective (W : RootFiveWitness D E) :
    Function.Injective (componentEmbedding W) := by
  intro a b hab
  exact congrArg Prod.snd (modelEmbedding_injective W hab)

theorem componentEmbedding_range (W : RootFiveWitness D E) :
    (componentEmbedding W).range = fiveComponent E := by
  rw [← W.component_factor]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(1, a), ⟨rfl, mem_top _⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    apply congrArg (modelEmbedding W)
    exact Prod.ext ha.1.symm rfl

/-- An equivalence using W's actual component embedding. -/
noncomputable def componentEquiv (W : RootFiveWitness D E) :
    fiveComponent E ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr (componentEmbedding_range W).symm).trans
    (MonoidHom.ofInjective (componentEmbedding_injective W)).symm

theorem inverter_order (W : RootFiveWitness D E) : orderOf W.inverter = 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp W.inverter_conj
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq D.z).trans D.localType.involution

/-- The intersection specified by 47.2 has order five. -/
theorem intersection_card (hG : Nat.card G = 604800) (W : RootFiveWitness D E)
    (P : Sylow 5 G) (hEP : E ≤ (P : Subgroup G)) :
    Nat.card ((P : Subgroup G) ⊓ fiveComponent E : Subgroup G) = 5 := by
  let Y := (P : Subgroup G) ⊓ fiveComponent E
  have hPN : (P : Subgroup G) ≤ normalizer (E : Set G) :=
    (sylow_le_centralizer hG P E hEP).trans (centralizer_le_normalizer _)
  let f : P →* DihedralGroup 5 :=
    (MonoidHom.fst _ _).comp (W.equiv.toMonoidHom.comp (inclusion hPN))
  have hk : f.ker.map (P : Subgroup G).subtype = Y := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, (mem_component_iff W (inclusion hPN a)).mpr ha⟩
    · rintro ⟨hxP, hxL⟩
      exact ⟨⟨x, hxP⟩, (mem_component_iff W (inclusion hPN ⟨x, hxP⟩)).mp hxL, rfl⟩
  have hkcard : Nat.card f.ker = Nat.card Y := by
    rw [← hk, card_map_of_injective (P : Subgroup G).subtype_injective]
  have hmul := f.ker.card_mul_index
  rw [index_ker, hkcard, sylow_card hG P] at hmul
  have hd : Nat.card Y ∣ 5 := by
    exact Nat.dvd_gcd
      (show Nat.card Y ∣ 25 from (sylow_card hG P) ▸ card_dvd_of_le inf_le_left)
      (show Nat.card Y ∣ 60 from (component_card W) ▸ card_dvd_of_le inf_le_right)
  rcases (show Nat.Prime 5 by decide).eq_one_or_self_of_dvd _ hd with hone | hfive
  · have hr : Nat.card f.range ∣ 10 := by
      simpa only [DihedralGroup.nat_card] using f.range.card_subgroup_dvd_card
    rw [hone, one_mul] at hmul
    rw [hmul] at hr
    norm_num at hr
  · exact hfive

/-- The two original factors form the actual Sylow subgroup. -/
theorem intersection_product (hG : Nat.card G = 604800) (hE : Nat.card E = 5)
    (W : RootFiveWitness D E) (P : Sylow 5 G) (hEP : E ≤ (P : Subgroup G)) :
    E ⊔ ((P : Subgroup G) ⊓ fiveComponent E) = (P : Subgroup G) := by
  let Y := (P : Subgroup G) ⊓ fiveComponent E
  have hd : Disjoint E Y := (disjoint_E_component W).mono_right inf_le_right
  have hn : Y ≤ normalizer (E : Set G) :=
    (inf_le_right.trans component_centralizes_E).trans (centralizer_le_normalizer _)
  apply eq_of_le_of_card_ge (sup_le hEP inf_le_left)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint E Y hn hd,
    hE, intersection_card hG W P hEP, sylow_card hG P]

/-- The already proved self-centralization of P determines the component
centralizer of its five-line; no additional alternating-group calculation is needed. -/
theorem component_intersection_centralizer (hG : Nat.card G = 604800)
    (hE : Nat.card E = 5) (W : RootFiveWitness D E) (P : Sylow 5 G)
    (hEP : E ≤ (P : Subgroup G)) :
    fiveComponent E ⊓ centralizer (((P : Subgroup G) ⊓ fiveComponent E : Subgroup G) : Set G) =
      (P : Subgroup G) ⊓ fiveComponent E := by
  let Y := (P : Subgroup G) ⊓ fiveComponent E
  have hCP : fiveComponent E ⊓ centralizer (Y : Set G) ≤ centralizer (P : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← intersection_product hG hE W P hEP]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans component_centralizes_E))
      (le_centralizer_iff.mp inf_le_right)
  rw [(sylow_facts_of_root_member hG W P hEP).2] at hCP
  apply le_antisymm (le_inf hCP inf_le_left)
  exact le_inf inf_le_right
    (inf_le_left.trans (sylow_le_centralizer hG P Y inf_le_left))

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
