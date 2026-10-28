module

public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import GorensteinWalter.AutAlternatingFour
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The normal alternating factor in an index-two extension of E₄ × S₄

The derived subgroup of E₄ × S₄ is its A₄ factor. Its centralizer is the
central E₄ factor. In a normal extension of order 192, conjugation on A₄
therefore has the full image Aut(A₄) ≃ S₄; its kernel has order eight and
generates the extension together with the original subgroup.

These are the first structural steps in the endpoint recognition used in
Aschbacher--Smith F.5.4(3), printed p.301.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace ElementaryFourSymmetricFourExtension
abbrev V := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
abbrev S := Equiv.Perm (Fin 4)
abbrev Model := V × S

 theorem derived_model : commutator Model = (⊥ : Subgroup V).prod (alternatingGroup (Fin 4)) := by
  rw [_root_.commutator_def, ← top_prod_top, commutator_prod_prod]
  rw [← _root_.commutator_def, ← _root_.commutator_def, (commutator_eq_bot_iff V).mpr inferInstance,
    Theory.SpecificGroups.SymmetricFourResidual.derived_eq]

 def derivedModelEquiv : commutator Model ≃* alternatingGroup (Fin 4) :=
  (MulEquiv.subgroupCongr derived_model).trans
    (((⊥ : Subgroup V).prodEquiv (alternatingGroup (Fin 4))).trans MulEquiv.uniqueProd)

 private theorem centralizer_even : ∀ x : S,
    (∀ y : S, y.sign = 1 → y * x = x * y) → x = 1 := by decide +kernel

 theorem centralizer_derived_model : centralizer (commutator Model : Set Model) =
    (⊤ : Subgroup V).prod ⊥ := by
  ext x
  rw [derived_model]
  constructor
  · intro hx
    refine ⟨mem_top _, ?_⟩
    apply centralizer_even x.2
    intro y hy
    exact congrArg Prod.snd (hx (1,y) ⟨rfl,hy⟩)
  · rintro ⟨_,hx⟩ y ⟨hy,_⟩
    change x.2=1 at hx
    change y.1=1 at hy
    apply Prod.ext <;> simp [hx,hy]

 theorem centralizer_derived_model_card : Nat.card (centralizer (commutator Model : Set Model)) = 4 := by
  rw [centralizer_derived_model,Nat.card_congr ((⊤ : Subgroup V).prodEquiv (⊥ : Subgroup S)).toEquiv,
    Nat.card_prod,Nat.card_congr (topEquiv (G := V)).toEquiv]
  simp [V,Nat.card_eq_fintype_card]

variable {G : Type*} [Group G] [Finite G]

 def derivedEquiv (E : Subgroup G) (e : E ≃* Model) : (⁅E,E⁆ : Subgroup G) ≃* alternatingGroup (Fin 4) := by
  let e₀ : commutator E ≃* (⁅E,E⁆ : Subgroup G) :=
    ((commutator E).equivMapOfInjective E.subtype E.subtype_injective).trans
      (MulEquiv.subgroupCongr E.map_subtype_commutator)
  let e₁ : commutator E ≃* commutator Model :=
    (e.subgroupMap (commutator E)).trans (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective,←_root_.commutator_def]))
  exact e₀.symm.trans (e₁.trans derivedModelEquiv)

 def centralizer_derived_inside_equiv (E : Subgroup G) (e : E ≃* Model) :
    ((centralizer ((⁅E,E⁆ : Subgroup G) : Set G)).subgroupOf E) ≃*
      centralizer (commutator Model : Set Model) := by
  let C := (centralizer ((⁅E,E⁆ : Subgroup G) : Set G)).subgroupOf E
  have hC : C = centralizer (commutator E : Set E) := by
    ext x
    constructor
    · intro hx y hy
      apply Subtype.ext
      exact hx y (E.map_subtype_commutator ▸ mem_map_of_mem E.subtype hy)
    · intro hx y hy
      rw [← E.map_subtype_commutator] at hy
      obtain ⟨y,hy,rfl⟩ := hy
      exact congrArg Subtype.val (hx y hy)
  have he : (centralizer (commutator E : Set E)).map e.toMonoidHom =
      centralizer (commutator Model : Set Model) := by
    have hmap : (commutator E).map e.toMonoidHom = commutator Model := by
      rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,←_root_.commutator_def]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩ z hz
      rw [←hmap] at hz
      obtain ⟨z,hz,rfl⟩ := hz
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hy z hz)
    · intro hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      intro y hy
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hx (e y) (hmap ▸ mem_map_of_mem e.toMonoidHom hy)
  exact (MulEquiv.subgroupCongr hC).trans
    ((e.subgroupMap _).trans (MulEquiv.subgroupCongr he))

theorem centralizer_derived_card_and_sup (E : Subgroup G) [E.Normal]
    (e : E ≃* Model) (hG : Nat.card G = 192) :
    Nat.card (centralizer ((⁅E,E⁆ : Subgroup G) : Set G)) = 8 ∧
      E ⊔ centralizer ((⁅E,E⁆ : Subgroup G) : Set G) = ⊤ := by
  let A := (⁅E,E⁆ : Subgroup G)
  let K := centralizer (A : Set G)
  let n : G →* normalizer (A : Set G) :=
    { toFun := fun g => ⟨g, by rw [normalizer_eq_top]; trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let a := A.normalizerMonoidHom.comp n
  have hk : a.ker = K := by
    ext g
    change n g ∈ A.normalizerMonoidHom.ker ↔ g ∈ K
    rw [normalizerMonoidHom_ker]
    rfl
  let b := a.comp E.subtype
  have hb : b.ker = K.subgroupOf E := by
    change a.ker.comap E.subtype = K.comap E.subtype
    rw [hk]
  have hc : Nat.card b.ker = 4 := by
    rw [hb]
    exact (Nat.card_congr (centralizer_derived_inside_equiv E e).toEquiv).trans
      centralizer_derived_model_card
  have hE : Nat.card E = 96 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Model,V,S,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  let ea : S ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  have hAut : Nat.card (MulAut A) = 24 := by
    rw [Nat.card_congr (MulAut.congr (derivedEquiv E e)).toEquiv,
      ←Nat.card_congr ea.toEquiv]
    norm_num [S,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hbs : Function.Surjective b := b.surjective_of_card_ker_le_div (by rw [hc,hE,hAut])
  have has : Function.Surjective a := by
    intro x
    obtain ⟨y,hy⟩ := hbs x
    exact ⟨y,hy⟩
  have hK : Nat.card K = 8 := by
    have hh := a.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr has,
      Nat.card_congr (topEquiv (G := MulAut A)).toEquiv,hAut,hk,hG] at hh
    omega
  refine ⟨hK,?_⟩
  apply eq_top_of_card_eq
  have hEK : Nat.card (E ⊓ K : Subgroup G) = 4 := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe (show E ⊓ K ≤ E from inf_le_left)).toEquiv]
    have he : (E ⊓ K).subgroupOf E = b.ker := by
      rw [hb]
      ext x
      exact and_iff_right x.property
    rw [he,hc]
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes E K
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hE,hK,hEK] at hh
  change Nat.card (E ⊔ K : Subgroup G) = Nat.card G
  rw [hG]
  omega

end ElementaryFourSymmetricFourExtension
