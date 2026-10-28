module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Hyperplanes
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!+# Fixed subgroups in the factor construction of Section 15.4

For a single factor, the index-two fixed subgroup of `E` restricts to an
index-two fixed subgroup of every noncentralizing subgroup `Z ≤ E`. For two
factors, a quotient with two binary coordinates, interchanged by an element
of `T`, has diagonal image on `C_E(T)`. Restricting the first coordinate gives
the same index-two result. The coordinate witness retains its actual kernel
and conjugation action; constructing it from the modules of 15.4.12 is a
separate obligation.

The other calculation uses the fixed-point theorem for a finite two-group.
An invariant elementary subgroup disjoint from the central omega subgroup is
trivial. Applied to `C_E(X) ∩ C_E(Y₁)`, this gives `|C_E(X)| = 2` and `|E| = 8`.
The intersection inequality then constructs the nontrivial common fixed
subgroup `E₀`. These intermediate results do not assert 15.4.18 or assume
its factor-count conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.14 and the second paragraph of 15.4.18,
printed pp.1161–1162.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Central involutions of `T` belong to the exact Thompson omega center `E`. -/
theorem centralOmega_le_thompsonAlpha (T : Subgroup G) :
    Stellmacher.omegaOneCenterAmbient T ≤ ChapterB.thompsonAlpha T := by
  let Z := Stellmacher.omegaOneCenterAmbient T
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian T
  apply Stellmacher.elementary_centralizer_maxJ_le_omegaCenter T Z
  · intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).1
  · intro z hz
    apply mem_centralizer_iff.mpr
    intro j hj
    have hJT : Stellmacher.elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hA => hA.1
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 j (hJT hj)

/-- The single-factor index in 15.4.12(6)(i) restricts to `Z`.
Noncentralization excludes index one. -/
theorem centralizer_index_two_of_single_factor {E Z Y : Subgroup G}
    (hZE : Z ≤ E)
    (hindex : (E ⊓ centralizer (Y : Set G)).relIndex E = 2)
    (hne : ¬ Z ≤ centralizer (Y : Set G)) :
    (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2 := by
  have hle : (Z ⊓ centralizer (Y : Set G)).relIndex Z ≤ 2 := by
    rw [inf_relIndex_left]
    have h := relIndex_le_of_le_right (H := centralizer (Y : Set G)) hZE
      (index_ne_zero_of_finite : (centralizer (Y : Set G)).relIndex E ≠ 0)
    rw [inf_relIndex_left] at hindex
    exact hindex ▸ h
  have hn : (Z ⊓ centralizer (Y : Set G)).relIndex Z ≠ 1 := by
    intro h
    exact hne ((relIndex_eq_one.mp h).trans inf_le_right)
  have hp : 0 < (Z ⊓ centralizer (Y : Set G)).relIndex Z :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  omega

/-- The quotient coordinates needed from the two-factor action. The kernel
is exactly `C_E(Y)`, and conjugation by the supplied element of `T` interchanges
the two binary coordinates. This is a mathematical witness, not a family tag. -/
structure SwappedBinaryQuotient (E T Y : Subgroup G) where
  projection : E →* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  surjective : Function.Surjective projection
  kernel : projection.ker = (centralizer (Y : Set G)).subgroupOf E
  swapper : G
  swapper_mem : swapper ∈ T
  normalizes : swapper ∈ normalizer (E : Set G)
  conjugation : ∀ e : E,
    projection ⟨swapper * (e : G) * swapper⁻¹,
      (mem_normalizer_iff.mp normalizes (e : G)).mp e.property⟩ =
      ((projection e).2, (projection e).1)

/-- A noncentralizing subgroup fixed by the factor swap has fixed index two.
The proof derives the hyperplane; it is not a field of the coordinate witness. -/
theorem centralizer_index_two_of_swapped_quotient {E T Z Y : Subgroup G}
    (d : SwappedBinaryQuotient E T Y) (hZE : Z ≤ E)
    (hTZ : T ≤ centralizer (Z : Set G))
    (hne : ¬ Z ≤ centralizer (Y : Set G)) :
    (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2 := by
  let q : Z →* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    d.projection.comp (inclusion hZE)
  let f : Z →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp q
  have hdiag (z : Z) : (q z).1 = (q z).2 := by
    have hc : d.swapper * (z : G) * d.swapper⁻¹ = z := by
      have hh := (mem_centralizer_iff.mp (hTZ d.swapper_mem) z z.property).symm
      rw [hh, mul_inv_cancel_right]
    have he := d.conjugation (inclusion hZE z)
    have heq : (⟨d.swapper * (z : G) * d.swapper⁻¹,
        (mem_normalizer_iff.mp d.normalizes (z : G)).mp (hZE z.property)⟩ : E) =
        inclusion hZE z := Subtype.ext hc
    have hp := congrArg d.projection heq
    exact congrArg Prod.fst (hp.symm.trans he)
  have hker : f.ker = (Z ⊓ centralizer (Y : Set G)).subgroupOf Z := by
    ext z
    change f z = 1 ↔ (z : G) ∈ Z ⊓ centralizer (Y : Set G)
    have hq : q z = 1 ↔ (z : G) ∈ centralizer (Y : Set G) := by
      change inclusion hZE z ∈ d.projection.ker ↔ _
      rw [d.kernel]
      rfl
    constructor
    · intro hz
      refine ⟨z.property, hq.mp ?_⟩
      apply Prod.ext
      · exact hz
      · exact (hdiag z).symm.trans hz
    · intro hz
      exact congrArg Prod.fst (hq.mpr hz.2)
  have hle : (Z ⊓ centralizer (Y : Set G)).relIndex Z ≤ 2 := by
    change ((Z ⊓ centralizer (Y : Set G)).subgroupOf Z).index ≤ 2
    rw [← hker, index_ker]
    have h := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    simpa using h
  have hn : (Z ⊓ centralizer (Y : Set G)).relIndex Z ≠ 1 := by
    intro h
    exact hne ((relIndex_eq_one.mp h).trans inf_le_right)
  have hp : 0 < (Z ⊓ centralizer (Y : Set G)).relIndex Z :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  omega

omit [Finite G] in
/-- Uniqueness of the maximal two-local overgroup forces noncentralization
whenever the centralizer of `Z` has two different maximal two-local overgroups. -/
theorem not_centralizes_of_distinct_overgroups {T Z Y M M₁ M₂ : Subgroup G}
    (hTZ : T ≤ centralizer (Z : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ T ≤ N → N = M)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hC₁ : centralizer (Z : Set G) ≤ M₁)
    (hC₂ : centralizer (Z : Set G) ≤ M₂) (hne : M₁ ≠ M₂) :
    ¬ Z ≤ centralizer (Y : Set G) := by
  intro hZY
  have hYC := le_centralizer_iff.mp hZY
  exact hne ((hunique M₁ hM₁ ((sup_le hYC hTZ).trans hC₁)).trans
    (hunique M₂ hM₂ ((sup_le hYC hTZ).trans hC₂)).symm)

/-- The fixed-point argument for an invariant elementary subgroup of `T`.
It uses relative normality in `T`, not ambient normality. -/
theorem eq_bot_of_normalized_of_disjoint_centralOmega {T D : Subgroup G}
    (hT : IsPGroup 2 T) [IsElementaryAbelian 2 D] (hDT : D ≤ T)
    (hn : T ≤ normalizer (D : Set G))
    (hdis : Stellmacher.omegaOneCenterAmbient T ⊓ D = ⊥) : D = ⊥ := by
  by_contra hD
  let Dₜ := D.subgroupOf T
  have hDₜ : Dₜ ≠ ⊥ := by
    intro hb
    exact hD (by rw [← map_subgroupOf_eq_of_le hDT]; change Dₜ.map T.subtype = ⊥
                 rw [hb, Subgroup.map_bot])
  let : Dₜ.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial Dₜ := (nontrivial_iff_ne_bot Dₜ).mpr hDₜ
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  obtain ⟨d, hd, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) Dₜ
  have hz : ((d : T) : G) ∈ Stellmacher.omegaOneCenterAmbient T := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(d : T).property, elemPow_eq_one_of_isElementaryAbelian _ d.property, ?_⟩
    intro t ht
    exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨t, ht⟩)
  have he : ((d : T) : G) = 1 := by
    exact mem_bot.mp (hdis ▸ (show ((d : T) : G) ∈
      Stellmacher.omegaOneCenterAmbient T ⊓ D from ⟨hz, d.property⟩))
  exact hd (Subtype.ext (Subtype.ext he))

/-- The two-group fixed-point argument turns disjoint central fixed subgroups
into disjoint fixed subgroups in the full Thompson omega center. -/
theorem fixed_subgroups_disjoint {T E X Y M₁ M₂ : Subgroup G}
    (hT : IsPGroup 2 T) [IsElementaryAbelian 2 E] (hET : E ≤ T)
    (hTE : T ≤ normalizer (E : Set G))
    (hTX : T ≤ normalizer (X : Set G)) (hTY : T ≤ normalizer (Y : Set G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ T ≤ M → M = M₂)
    (hne : M₁ ≠ M₂) :
    (E ⊓ centralizer (X : Set G)) ⊓ (E ⊓ centralizer (Y : Set G)) = ⊥ := by
  let Z := Stellmacher.omegaOneCenterAmbient T
  let D := (E ⊓ centralizer (X : Set G)) ⊓ (E ⊓ centralizer (Y : Set G))
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian T
  have hDE : D ≤ E := inf_le_left.trans inf_le_left
  let : IsElementaryAbelian 2 D := {
    toIsMulCommutative := .of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (hDE ha) (hDE hb)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun d =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (d : G) (hDE d.property)) }
  have hTZ : T ≤ centralizer (Z : Set G) := by
    intro t ht
    exact mem_centralizer_iff.mpr fun z hz =>
      (((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 t ht).symm
  have hd : (Z ⊓ centralizer (X : Set G)) ⊓ (Z ⊓ centralizer (Y : Set G)) = ⊥ :=
    centralizers_disjoint_of_unique hTZ huniqueX huniqueY hne
  have hnorm (A : Subgroup G) (hTA : T ≤ normalizer (A : Set G)) :
      T ≤ normalizer ((E ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    (le_inf hTE (hTA.trans (normalizer_le_normalizer_centralizer A))).trans
      inf_normalizer_le_normalizer_inf
  have hnD : T ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht d hd
    exact ⟨(mem_normalizer_iff.mp (hnorm X hTX ht) d).mp hd.1,
      (mem_normalizer_iff.mp (hnorm Y hTY ht) d).mp hd.2⟩
  have hZD : Z ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    exact (le_of_eq hd) ⟨⟨hz.1, hz.2.1.2⟩, ⟨hz.1, hz.2.2.2⟩⟩
  exact eq_bot_of_normalized_of_disjoint_centralOmega (D := D) hT (hDE.trans hET) hnD hZD

/-- Cardinal calculation in the mixed-factor construction. The two indices
come from the single and double alternatives of 15.4.12(6); the order-two
subgroup `Zₓ` is the already constructed central fixed line. -/
theorem mixed_omega_card {E E₁ Eₓ Zₓ : Subgroup G}
    (hdis : E₁ ⊓ Eₓ = ⊥) (hEₓ : Eₓ ≤ E)
    (h₁ : E₁.relIndex E = 2) (hₓ : Eₓ.relIndex E = 4)
    (hZₓ : Zₓ ≤ Eₓ) (hcZₓ : Nat.card Zₓ = 2) :
    Nat.card Eₓ = 2 ∧ Nat.card E = 8 := by
  have hsmall : Nat.card Eₓ ≤ 2 := by
    have h := relIndex_le_of_le_right (H := E₁) hEₓ
      (index_ne_zero_of_finite : E₁.relIndex E ≠ 0)
    rw [h₁] at h
    have he : E₁.relIndex Eₓ = Nat.card Eₓ := by
      rw [← inf_relIndex_right, hdis, relIndex_bot_left]
    rwa [he] at h
  have hlarge : 2 ≤ Nat.card Eₓ := hcZₓ ▸ card_le_of_le hZₓ
  have hc : Nat.card Eₓ = 2 := le_antisymm hsmall hlarge
  refine ⟨hc, ?_⟩
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) Eₓ E bot_le hEₓ
  simpa only [relIndex_bot_left, hc, hₓ] using h.symm

omit [Finite G] in
/-- Two subgroups of index two in a group of order eight intersect nontrivially.
This is applied only after the mixed-factor calculation constructs that order. -/
theorem common_fixed_ne_bot {E E₁ E₂ : Subgroup G}
    (hcard : Nat.card E = 8) (h₁ : E₁.relIndex E = 2)
    (h₂ : E₂.relIndex E = 2) : E₁ ⊓ E₂ ≠ ⊥ := by
  intro hb
  have h := relIndex_inf_le (H := E₁) (K := E₂) (L := E)
  rw [hb, relIndex_bot_left, hcard, h₁, h₂] at h
  omega

omit [Finite G] in
/-- The generated mixed-factor group centralizes the constructed common fixed
subgroup whenever its common two-subgroup centralizes `E`. -/
theorem mixed_join_centralizes {E Tᵢ Y₁ Y₂ : Subgroup G}
    (hTE : Tᵢ ≤ centralizer (E : Set G)) :
    (Y₁ ⊔ Tᵢ) ⊔ (Y₂ ⊔ Tᵢ) ≤ centralizer
      (((E ⊓ centralizer (Y₁ : Set G)) ⊓
        (E ⊓ centralizer (Y₂ : Set G))) : Set G) := by
  let E₀ := (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G))
  have hE₀ : E₀ ≤ E := inf_le_left.trans inf_le_left
  have hT : Tᵢ ≤ centralizer (E₀ : Set G) := hTE.trans (centralizer_le hE₀)
  have h₁ := le_centralizer_iff.mpr
    (inf_le_left.trans inf_le_right :
      (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G)) ≤
        centralizer (Y₁ : Set G))
  have h₂ := le_centralizer_iff.mpr
    (inf_le_right.trans inf_le_right :
      (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G)) ≤
        centralizer (Y₂ : Set G))
  exact sup_le (sup_le h₁ hT) (sup_le h₂ hT)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
