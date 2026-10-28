module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SylowSubnormalIntersection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Normalizer
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# Projecting and placing the two cubic generators

For the selected component C of A, its full action on the elementary eight-group
W identifies C/O₂(C) with Aut(W). Composing the A-action with the inverse gives
an actual homomorphism A → C/O₂(C), restricting to the quotient map on C.
Distinct components commute modulo the solvable radical, so at most one can
cover this perfect simple image. Consequently C is normal in A.

The image of the actual T∩C is Sylow in C/O₂(C). Each cubic generator has
non-two-group image: otherwise two-perfectness kills that image and the other
cubic generator would cover a group of order 168. The binary parabolic
recognition theorem and an explicit cubic/Borel commutator then give
P = [P, image(T∩C)]. A normal non-two-subgroup of a two-perfect group with
cubic two-core quotient is the whole group. This lifts the image identity,
proves both generator placements, and gives A = C.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.4.8(2), printed p.1009. The final theorem consumes the selected
component constructed in Components.Selection. No new earlier-source premise
is required; construction of that component remains with the source assembly.
-/

public section
open Subgroup

private theorem radical_le_ker {G D : Type*} [Group G] [Finite G]
    [Group D] [IsSimpleGroup D] [Group.IsPerfect D]
    (f : G →* D) (hf : Function.Surjective f) : solvableRadical G ≤ f.ker := by
  have hn : ((solvableRadical G).map f).Normal := Normal.map inferInstance f hf
  rcases hn.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · have hs : Group.IsSolvable ((solvableRadical G).map f) :=
      Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
    rw [h] at hs
    let := hs
    have hD : Group.IsSolvable D := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).surjective
    exact (Group.IsPerfect.not_isSolvable D hD).elim

private theorem component_eq_of_full_image {G D : Type*} [Group G] [Finite G]
    [Group D] [IsSimpleGroup D] [Group.IsPerfect D]
    (f : G →* D) (hf : Function.Surjective f)
    {C K : Subgroup G} (hC : C.IsCComponent) (hK : K.IsCComponent)
    (hCf : C.map f = ⊤) (hKf : K.map f = ⊤) : C = K := by
  by_contra hne
  let q := QuotientGroup.mk' (solvableRadical G)
  have hneq : C.map q ≠ K.map q := fun he =>
    hne (hC.eq_of_map_quotient_eq hK _ he)
  have hc := (hC.map_quotient (solvableRadical G)).commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G))
    (hK.map_quotient (solvableRadical G)) hneq
  have hr : ⁅C, K⁆ ≤ solvableRadical G := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hc
    exact hc
  have he : ⁅C, K⁆.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
    (hr.trans (radical_le_ker f hf))
  rw [map_commutator, hCf, hKf] at he
  have ht : ⁅(⊤ : Subgroup D),⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  exact top_ne_bot (ht.symm.trans he)

private theorem component_normal_of_full_image {G D : Type*} [Group G] [Finite G]
    [Group D] [IsSimpleGroup D] [Group.IsPerfect D]
    (f : G →* D) (hf : Function.Surjective f)
    {C : Subgroup G} (hC : C.IsCComponent) (hCf : C.map f = ⊤) : C.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply component_eq_of_full_image f hf (hC.map_equiv (MulAut.conj g)) hC _ hCf
  have hc : f.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (f g)).toMonoidHom.comp f := by ext; simp
  rw [map_map, hc, ← map_map, hCf, map_top_of_surjective _ (MulAut.conj (f g)).surjective]
open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionCubic
variable {G D : Type*} [Group G] [Finite G] [Group D]

omit [Finite G] in
private theorem normal_eq_top (hp : IsPPerfect 2 G)
    (hc : Nat.card (G ⧸ pCore 2 G) = 3)
    (N : Subgroup G) [N.Normal] (hn : ¬ IsPGroup 2 N) : N = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Fact (Nat.Prime (Nat.card (G ⧸ pCore 2 G))) := ⟨hc ▸ (by decide)⟩
  have ht : N.map q = ⊤ := by
    rcases (N.map q).eq_bot_or_eq_top_of_prime_card with h | h
    · have hi : N ≤ pCore 2 G := by
        simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using h
      exact (hn (pCore_isPGroup.to_le hi)).elim
    · exact h
  have hgen : N ⊔ pCore 2 G = ⊤ := by
    have hm := congrArg (comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
  have hperfect : IsPPerfect 2 (⊤ : Subgroup G) := hp.of_surjective
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.surjective
  exact top_unique (le_normal_of_isPPerfect_of_le_sup_pGroup ⊤ N (pCore 2 G)
    hperfect pCore_isPGroup hgen.ge)

omit [Finite G] in
private theorem image_core_card (hc : Nat.card (G ⧸ pCore 2 G) = 3)
    (f : G →* D) (hf : Function.Surjective f) (hn : ¬ IsPGroup 2 D) :
    Nat.card (D ⧸ pCore 2 D) = 3 := by
  have hmap : (pCore 2 G).map f ≤ pCore 2 D :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  have hd : (pCore 2 D).index ∣ 3 := by
    rw [← hc, ← index_eq_card]
    exact (index_dvd_of_le hmap).trans ((pCore 2 G).index_map_dvd hf)
  rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ hd with h | h
  · have he := index_eq_one.mp h
    have hh : IsPGroup 2 (⊤ : Subgroup D) := he ▸ pCore_isPGroup
    exact (hn (hh.of_equiv topEquiv)).elim
  · exact h

omit [Finite G] in
private theorem eq_commutator (K S : Subgroup G)
    (hp : IsPPerfect 2 K) (hc : Nat.card (K ⧸ pCore 2 K) = 3)
    (hn : S ≤ normalizer (K : Set G))
    (f : G →* D) (hi : ¬ IsPGroup 2 (K.map f))
    (he : K.map f = ⁅K.map f, S.map f⁆) : K = ⁅K, S⁆ := by
  have hle : ⁅K, S⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hn
  let N := ⁅K, S⁆.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_left K S)
  have hnp : ¬ IsPGroup 2 N := by
    intro hh
    have hd : IsPGroup 2 (⁅K, S⁆ : Subgroup G) := hh.of_equiv (subgroupOfEquivOfLe hle)
    apply hi
    rw [he, ← map_commutator]
    exact hd.map f
  have ht := normal_eq_top hp hc N hnp
  apply le_antisymm _ hle
  intro x hx
  exact (show (⟨x, hx⟩ : K) ∈ N from ht ▸ mem_top _)
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionCubic
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type*} [Group G] [Finite G]
variable {A W T : Subgroup G} [IsElementaryAbelian 2 W]
variable {hn : A ≤ normalizer (W : Set G)}

namespace SelectedComponent
/-- The equivalence induced by C acting on the actual moved eight-group. -/
noncomputable def actionEquiv (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    coreQuotient S.carrier ≃* MulAut W :=
  coreConjugationEquiv S.carrier W (S.component.1.trans hn) S.surjective
    (kernel_eq_core_of_full_action_and_quotient hW _ S.surjective S.quotient.some)

/-- The source projection has target C/O₂(C), marked by the literal action. -/
noncomputable def projection (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    A →* coreQuotient S.carrier :=
  (S.actionEquiv hW).symm.toMonoidHom.comp (conjugation A W hn)

/-- On C the projection is exactly its intrinsic two-core quotient map. -/
theorem projection_component (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    (S.projection hW).comp (inclusion S.component.1) =
      QuotientGroup.mk' (pCore 2 S.carrier) := by
  ext c
  apply (S.actionEquiv hW).injective
  change S.actionEquiv hW ((S.actionEquiv hW).symm
    (conjugation A W hn (inclusion S.component.1 c))) = _
  rw [MulEquiv.apply_symm_apply]
  change (conjugation A W hn) (inclusion S.component.1 c) =
    coreConjugationEquiv S.carrier W (S.component.1.trans hn) S.surjective _
      (QuotientGroup.mk' (pCore 2 S.carrier) c)
  rw [coreConjugationEquiv_mk]
  exact DFunLike.congr_fun (conjugation_restrict
    (S.component.1.trans hn) hn S.component.1) c

/-- The component already covers the target of the projection. -/
theorem projection_surjective (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    Function.Surjective (S.projection hW) := by
  intro x
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (pCore 2 S.carrier) x
  exact ⟨inclusion S.component.1 c,
    (DFunLike.congr_fun (S.projection_component hW) c).trans hc⟩

/-- The projection kernel is the relative centralizer of the moved space. -/
theorem projection_ker (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    (S.projection hW).ker = (centralizer (W : Set G)).subgroupOf A := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ (S.actionEquiv hW).symm.injective,
    conjugation_ker]

/-- The full simple image singles out C among all components, so C is normal in A. -/
theorem normal (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    (S.carrier.subgroupOf A).Normal := by
  obtain ⟨e⟩ := S.quotient
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let : IsSimpleGroup (coreQuotient S.carrier) := e.isSimpleGroup
  let : Group.IsPerfect (coreQuotient S.carrier) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  apply component_normal_of_full_image (S.projection hW) (S.projection_surjective hW) S.component.2
  apply top_unique
  intro x _
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 S.carrier) x
  exact mem_map.mpr ⟨inclusion S.component.1 c, c.property,
    DFunLike.congr_fun (S.projection_component hW) c⟩
end SelectedComponent
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionModel
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open scoped commutatorElement

private theorem point_commutator :
    residual pointParabolicSL = ⁅residual pointParabolicSL, borelSL⁆ := by
  have hn : borelSL ≤ normalizer (pointA : Set SL) := by
    apply le_normalizer_iff.mpr
    intro s hs a ha
    exact pointA_conj s (show s ∈ pointParabolicSL from hs.1) a ha
  have hle : ⁅pointA, borelSL⁆ ≤ pointA := le_normalizer_iff_commutator_le_left.mp hn
  let N := ⁅pointA, borelSL⁆.subgroupOf pointA
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_left pointA borelSL)
  have hc : cubic ∈ ⁅pointA, borelSL⁆ := by
    have he : ⁅cubic, Bruhat.upper 4⁆ = cubic⁻¹ := by decide +kernel
    have hm := commutator_mem_commutator cubic_mem (Bruhat.upper_mem 4)
    rw [he] at hm
    exact inv_mem_iff.mp hm
  have hnp : ¬ IsPGroup 2 N := by
    intro hp
    obtain ⟨n, he⟩ := hp ⟨⟨cubic, cubic_mem⟩, hc⟩
    have hx : cubic ^ (2 ^ n) = 1 := congrArg (fun x : N => (x.val : SL)) he
    have ho : orderOf cubic = 1 := Nat.eq_one_of_dvd_coprimes
      ((by decide : Nat.Coprime 2 3).pow_left n)
      (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one cubic_cube)
    exact (by decide +kernel : cubic ≠ 1) (orderOf_eq_one_iff.mp ho)
  have hp : IsPPerfect 2 pointA := by
    rw [← point_residual]
    exact isPPerfect_embedded_pResidual 2 pointParabolicSL
  have ht := ProjectionCubic.normal_eq_top hp card_point_core_quotient N hnp
  rw [point_residual]
  apply le_antisymm _ hle
  intro a ha
  exact (show (⟨a, ha⟩ : pointA) ∈ N from ht ▸ mem_top _)

private theorem line_commutator :
    residual lineParabolicSL = ⁅residual lineParabolicSL, borelSL⁆ := by
  have hm : (residual pointParabolicSL).map flagDuality.toMonoidHom =
      residual lineParabolicSL := by
    change ((pResidual 2 pointParabolicSL).map pointParabolicSL.subtype).map _ = _
    rw [map_embedded_pResidual, flagDuality_map_point]
    rfl
  have he := congrArg (map flagDuality.toMonoidHom) point_commutator
  simpa only [map_commutator, hm, flagDuality_map_borel] using he

private theorem commutator_of_cubic (P : Subgroup SL) (S : Sylow 2 SL)
    (hp : IsPPerfect 2 P) (hc : Nat.card (P ⧸ pCore 2 P) = 3)
    (hn : (S : Subgroup SL) ≤ normalizer (P : Set SL)) :
    P = ⁅P,(S : Subgroup SL)⁆ := by
  obtain ⟨_, _, _, _, g, P₀, hP₀, _, hP, hS, _⟩ := ResidualRecognition.recognize P S hp hc hn
  apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_commutator, hP, hS]
  rcases hP₀ with rfl | rfl
  · exact point_commutator
  · exact line_commutator
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionModel

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type*} [Group G] [Finite G]
variable {A W : Subgroup G} [IsElementaryAbelian 2 W]
variable {hn : A ≤ normalizer (W : Set G)}
namespace SelectedComponent

/-- The actual ambient Sylow intersection maps to a Sylow subgroup of C/O₂(C). -/
theorem projection_sylow (T : Sylow 2 G)
    (S : SelectedComponent A W T hn) (hW : Nat.card W = 8) :
    ∃ Q : Sylow 2 (coreQuotient S.carrier),
      (Q : Subgroup (coreQuotient S.carrier)) =
        (((T : Subgroup G) ⊓ S.carrier).subgroupOf A).map (S.projection hW) := by
  let J := S.carrier ⊔ (T : Subgroup G)
  let C := S.carrier.subgroupOf J
  let : C.Normal := S.normal_join
  obtain ⟨R, hR⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal C
  let e : C ≃* S.carrier := subgroupOfEquivOfLe (show S.carrier ≤ J from le_sup_left)
  let R₀ : Sylow 2 S.carrier := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR₀ : (R₀ : Subgroup S.carrier) = (T : Subgroup G).subgroupOf S.carrier := by
    change (R : Subgroup C).map e.toMonoidHom = _
    rw [hR]
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hc
      exact ⟨⟨⟨c,(show S.carrier ≤ J from le_sup_left) c.property⟩, c.property⟩, hc, rfl⟩
  let q := QuotientGroup.mk' (pCore 2 S.carrier)
  refine ⟨R₀.mapSurjective (f := q) (QuotientGroup.mk'_surjective _), ?_⟩
  change (R₀ : Subgroup S.carrier).map q = _
  dsimp only [q]
  rw [hR₀, ← S.projection_component hW, ← map_map]
  congr 1
  ext a
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨hc, c.property⟩
  · intro ha
    exact ⟨⟨a, ha.2⟩, ha.1, rfl⟩
end SelectedComponent
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionCubic
variable {G D : Type*} [Group G] [Finite G] [Group D]

omit [Finite G] in
private theorem core_card_subgroupOf {K A : Subgroup G} (hKA : K ≤ A)
    (hc : Nat.card (K ⧸ pCore 2 K) = 3) :
    Nat.card ((K.subgroupOf A) ⧸ pCore 2 (K.subgroupOf A)) = 3 := by
  let e := subgroupOfEquivOfLe hKA
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc

private theorem map_ne_top (K : Subgroup G)
    (hc : Nat.card (K ⧸ pCore 2 K) = 3)
    (f : G →* D) (hD : Nat.card D = 168) : K.map f ≠ ⊤ := by
  intro he
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have hk : Nat.card K = 3 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K), hc, hn]
  have hd := K.card_map_dvd f
  rw [he, Nat.card_congr Subgroup.topEquiv.toEquiv, hD, hk] at hd
  have hseven : 7 ∣ 3 * 2 ^ n := (by decide : 7 ∣ 168).trans hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hseven with h | h
  · norm_num at h
  · have := (by decide : Nat.Prime 7).dvd_of_dvd_pow h
    norm_num at this

private theorem image_not_two (K L : Subgroup G) (hp : IsPPerfect 2 K)
    (hc : Nat.card (L ⧸ pCore 2 L) = 3) (hgen : K ⊔ L = ⊤)
    (f : G →* D) (hf : Function.Surjective f) (hD : Nat.card D = 168) :
    ¬ IsPGroup 2 (K.map f) := by
  intro hi
  have hh := hp.hom_eq_one_of_isPGroup hi (f.subgroupMap K)
  have he : K.map f = ⊥ := by
    apply eq_bot_iff.mpr
    rintro y ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (DFunLike.congr_fun hh ⟨k, hk⟩)
  have ht : K.map f ⊔ L.map f = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective f hf]
  rw [he, bot_sup_eq] at ht
  exact map_ne_top L hc f hD ht
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionCubic

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionModel
open Matrix.PSL3Two
variable {D : Type*} [Group D] [Finite D]

private theorem commutator_of_equiv (e : D ≃* SL) (P : Subgroup D) (S : Sylow 2 D)
    (hp : IsPPerfect 2 P) (hc : Nat.card (P ⧸ pCore 2 P) = 3)
    (hn : (S : Subgroup D) ≤ normalizer (P : Set D)) :
    P = ⁅P,(S : Subgroup D)⁆ := by
  let Q := P.map e.toMonoidHom
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let a := e.subgroupMap P
  have hQp : IsPPerfect 2 Q := hp.of_surjective a.toMonoidHom a.surjective
  have hQc : Nat.card (Q ⧸ pCore 2 Q) = 3 := by
    have he := Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv
    exact he.symm.trans hc
  have hRn : (R : Subgroup SL) ≤ normalizer (Q : Set SL) :=
    (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  have h := commutator_of_cubic Q R hQp hQc hRn
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_commutator]
  exact h
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components.ProjectionModel

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type*} [Group G] [Finite G]
variable {A W : Subgroup G} [IsElementaryAbelian 2 W]
variable {hn : A ≤ normalizer (W : Set G)}
namespace SelectedComponent

/-- A cubic generator is generated by its commutators with T∩C and lies in C.
The image identity is proved in the marked quotient before it is lifted. -/
theorem generator_placement (T : Sylow 2 G)
    (S : SelectedComponent A W T hn) (hW : Nat.card W = 8)
    (K B : Subgroup G) (hKA : K ≤ A) (hBA : B ≤ A) (hgen : K ⊔ B = A)
    (hp : IsPPerfect 2 K) (hc : Nat.card (coreQuotient K) = 3)
    (hB : Nat.card (coreQuotient B) = 3)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    (K.subgroupOf A).map (S.projection hW) =
      ⁅(K.subgroupOf A).map (S.projection hW),
        (((T : Subgroup G) ⊓ S.carrier).subgroupOf A).map (S.projection hW)⁆ ∧
    K = ⁅K,(T : Subgroup G) ⊓ S.carrier⁆ ∧ K ≤ S.carrier := by
  let K' := K.subgroupOf A
  let B' := B.subgroupOf A
  let U' := ((T : Subgroup G) ⊓ S.carrier).subgroupOf A
  let f := S.projection hW
  have hUp : (T : Subgroup G) ⊓ S.carrier ≤ A := inf_le_right.trans S.component.1
  have hKp : IsPPerfect 2 K' := hp.of_surjective
    (subgroupOfEquivOfLe hKA).symm.toMonoidHom (subgroupOfEquivOfLe hKA).symm.surjective
  have hKc := ProjectionCubic.core_card_subgroupOf hKA hc
  have hBc := ProjectionCubic.core_card_subgroupOf hBA hB
  have hgen' : K' ⊔ B' = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKA, map_subgroupOf_eq_of_le hBA,
      hgen, ← MonoidHom.range_eq_map, range_subtype]
  have hcard : Nat.card (coreQuotient S.carrier) = 168 :=
    (Nat.card_congr S.quotient.some.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hnot : ¬ IsPGroup 2 (K'.map f) :=
    ProjectionCubic.image_not_two K' B' hKp hBc hgen' f (S.projection_surjective hW) hcard
  have hn' : U' ≤ normalizer (K' : Set A) := by
    apply le_normalizer_iff.mpr
    intro t ht k hk
    exact le_normalizer_iff.mp hTK t ht.1 k hk
  obtain ⟨Q, hQ⟩ := S.projection_sylow T hW
  have hQP : (Q : Subgroup (coreQuotient S.carrier)) ≤ normalizer (K'.map f : Set _) := by
    rw [hQ]
    exact (map_mono hn').trans (le_normalizer_map f)
  have hPp : IsPPerfect 2 (K'.map f) :=
    hKp.of_surjective (f.subgroupMap K') (f.subgroupMap_surjective K')
  have hPc : Nat.card ((K'.map f) ⧸ pCore 2 (K'.map f)) = 3 :=
    ProjectionCubic.image_core_card hKc (f.subgroupMap K') (f.subgroupMap_surjective K') hnot
  have he := ProjectionModel.commutator_of_equiv
    (S.quotient.some.trans Matrix.PSL3Two.equiv.symm) (K'.map f) Q hPp hPc hQP
  rw [hQ] at he
  have hk := ProjectionCubic.eq_commutator K' U' hKp hKc hn' f hnot he
  have hcomm : K = ⁅K,(T : Subgroup G) ⊓ S.carrier⁆ := by
    have hm := congrArg (map A.subtype) hk
    simpa only [K', U', map_commutator, map_subgroupOf_eq_of_le hKA,
      map_subgroupOf_eq_of_le hUp] using hm
  refine ⟨he, hcomm, ?_⟩
  have hAC : A ≤ normalizer (S.carrier : Set G) :=
    (normal_subgroupOf_iff_le_normalizer S.component.1).mp (S.normal hW)
  exact hcomm.le.trans ((commutator_mono le_rfl inf_le_right).trans
    (le_normalizer_iff_commutator_le_right.mp (hKA.trans hAC)))
end SelectedComponent
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type*} [Group G] [Finite G]

/-- Both source cubic generators are contained in the selected component.
The conclusion retains the literal Sylow intersections and commutators. -/
theorem selectedComponent_eq_localJoin
    (T : Sylow 2 G) {H V₂ E X L₂ : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E) [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hL₂ : twoResidual L₂ = L₂) (hLc : Nat.card (coreQuotient L₂) = 3)
    (hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G))
    (hn : localJoin L₂ X ⊔ (T : Subgroup G) ≤ normalizer (movedSpace V₂ X : Set G))
    (S : SelectedComponent (localJoin L₂ X) (movedSpace V₂ X) T (le_sup_left.trans hn)) :
    L₂ = ⁅L₂,(T : Subgroup G) ⊓ S.carrier⁆ ∧
      X = ⁅X,(T : Subgroup G) ⊓ S.carrier⁆ ∧
      L₂ ≤ S.carrier ∧ X ≤ S.carrier ∧ localJoin L₂ X = S.carrier := by
  have hL := S.generator_placement T hX.2.1 L₂ X le_sup_left le_sup_right rfl
    (isPPerfect_of_twoResidual_eq hL₂) hLc hX.1.coreQuotient_card hTL₂
  have hY := S.generator_placement T hX.2.1 X L₂ le_sup_right le_sup_left (sup_comm X L₂)
    (isPPerfect_of_twoResidual_eq hX.1.residual_eq) hX.1.coreQuotient_card hLc hX.1.T_normalizes
  exact ⟨hL.2.1, hY.2.1, hL.2.2, hY.2.2,
    le_antisymm (sup_le hL.2.2 hY.2.2) S.component.1⟩
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
