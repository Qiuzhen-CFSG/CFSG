module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSolvableCubic
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.FivePairSource
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallResidual
/-!
# Centralizers of offenders in the small chief actions

Every offender in a paired small natural action contains a nontrivial
coordinate offender. An element exchanging the two coordinates cannot
centralize that subgroup, so its centralizer lies in the offender base.

For the solvable alternatives, the actual source product and the bound
|G| ≤ 72 give at most two factors. Independence forces a centralizing
actor to fix an active factor; the factor-permutation kernel is exactly
the offender subgroup. For the paired symmetric-five action, the marked
codimension identity gives the coordinate product and the whole-action
identification retains the literal base axes. The single symmetric-five
alternative has offender subgroup equal to the whole actor.

The final wrappers use the original chief representation and its action
homomorphism. They discharge the centralizer premise of the original
Thompson-image upper bound, without assuming that the original maximum
elementary actor is itself an offender.

Source: Aschbacher–Smith, B.1.8, B.6.9 and 3.1.9(5), pp.577–578.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction BinaryPermutation

private theorem perm_eq_one_of_small_fixed {n : ℕ} (hn : n ≤ 2)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (hi : p i = i) : p = 1 := by
  apply Equiv.ext
  intro j
  change p j = j
  by_cases hji : j=i
  · simpa [hji] using hi
  have hpi : p j ≠ i := fun h => hji (p.injective (h.trans hi.symm))
  apply Fin.ext
  have : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have : (p j).val ≠ i.val := fun h => hpi (Fin.ext h)
  omega

/-- Each actual small natural actor has order at most 72. -/
theorem SmallNaturalWreathAction.card_le_seventy_two {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (h : SmallNaturalWreathAction ρ) : Nat.card G ≤ 72 := by
  have hs : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  rcases h with ⟨c,e,he⟩ | ⟨e,c,he⟩
  · rw [Nat.card_congr e.toEquiv,hs]
    decide
  · rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card,hs]
    norm_num [Nat.card_eq_fintype_card]

/-- The actual one- or two-factor solvable alternatives have every offender
centralizer inside their offender subgroup. -/
theorem small_natural_offender_centralizer_le
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (hsmall : SmallNaturalWreathAction ρ)
    (hcore : pCore 2 G=⊥) (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : IsOffender ρ A) :
    centralizer (A : Set G) ≤ offenderSubgroup ρ := by
  obtain ⟨d,_,_,hr,_⟩ := source_solvable_minimalParabolic_factors
    (ρ := ρ) T hP hsmall.solvable hcore hf ⟨A,hA⟩
  let D := d.toSolvableFFFactors
  have hc : D.count ≤ 2 := by
    have he := D.offenderSubgroup_card
    have hle := Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype
      (offenderSubgroup ρ).subtype_injective
    have hg := hsmall.card_le_seventy_two
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 6) (show 3 ≤ D.count by omega)
    rw [←he] at hh
    norm_num at hh
    omega
  have hs := SolvableFFFactors.not_strong_of_ratio_eq_one d.ratio_one
  have hb := (isBestOffender_iff_of_not_strong ρ hs A).mpr
    ⟨hA.1,le_antisymm hA.2 (Nat.le_of_not_gt (fun h => hs ⟨A,hA.1,h⟩))⟩
  obtain ⟨C,hC,⟨i,hi⟩,hAC⟩ := (D.isBestOffender_iff_sylowProduct hf d.ratio_one A).mp hb
  have hCi : C i ≤ D.factor i := SolvableFFFactors.IsSylowChoice.le D (hC i)
  have hCA : C i ≤ A := hAC ▸ le_iSup C i
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hi
  have hxi : (x:G) ∈ D.factor i := hCi x.property
  have hne : (x:G) ≠ 1 := fun hh => hx (Subtype.ext hh)
  intro g hg
  rw [←D.factorConjugation_ker_eq_of_centralizer_eq_bot
    (D.centralizer_eq_bot_of_residual hf hcore hr)]
  apply perm_eq_one_of_small_fixed hc _ i
  by_contra hn
  have he : g*(x:G)*g⁻¹=(x:G) := by
    rw [←mem_centralizer_iff.mp hg x (hCA x.property),mul_inv_cancel_right]
  have hxj : (x:G) ∈ D.factor (D.factorConjugation g i) := by
    rw [←D.factor_map_conj g i]
    have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hxi
    change g*(x:G)*g⁻¹ ∈ _ at hh
    rwa [he] at hh
  exact hne (Subgroup.disjoint_def.mp (D.factors_independent.pairwiseDisjoint hn) hxj hxi)

private theorem centralizer_base_first (w : FivePair.Wreath)
    (a : Equiv.Perm (Fin 5)) (ha : a ≠ 1)
    (hc : FivePair.base (a,1) * w = w * FivePair.base (a,1)) :
    w.right = 1 := by
  by_contra hn
  have hh := congrArg (fun z : FivePair.Wreath => z.left 1) hc
  have hinv : w.right⁻¹ ≠ 1 := inv_ne_one.mpr hn
  simp only [RegularWreathProduct.mul_left,Pi.mul_apply,FivePair.base,
    inv_one,one_mul,ite_true,mul_one,hinv,ite_false] at hh
  exact ha (mul_right_cancel (hh.trans (one_mul _).symm))

private theorem centralizer_base_second (w : FivePair.Wreath)
    (a : Equiv.Perm (Fin 5)) (ha : a ≠ 1)
    (hc : FivePair.base (1,a) * w = w * FivePair.base (1,a)) :
    w.right = 1 := by
  by_contra hn
  have hh := congrArg (fun z : FivePair.Wreath => z.left FivePair.swapIndex) hc
  have hwr : w.right = FivePair.swapIndex := by
    have h : ∀ z : FivePair.C2, z=1 ∨ z=FivePair.swapIndex := by decide
    exact (h w.right).resolve_left hn
  simp only [RegularWreathProduct.mul_left,Pi.mul_apply,FivePair.base,
    inv_one,one_mul,FivePair.swapIndex_ne_one,ite_false,hwr,
    FivePair.swapIndex_inv,FivePair.swapIndex_mul_self,ite_true,mul_one] at hh
  exact ha (mul_right_cancel (hh.trans (one_mul _).symm))
/-- The marked symmetric-five pair places each actual offender centralizer
in its literal offender base. -/
theorem source_pair_five_offender_centralizer_le
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (hcore : pCore 2 G = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    {A : Subgroup G} (hA : IsOffender ρ A) :
    centralizer (A : Set G) ≤ offenderSubgroup ρ := by
  let Y := offenderSubgroup ρ
  obtain ⟨B,hBA,hB⟩ := hA.exists_bestOffender ρ
  have hBY : B ≤ Y := hB.le_offenderSubgroup ρ
  let C := (B.subgroupOf Y).map c.action.groupEquiv.toMonoidHom
  have hB' : IsOffender (ρ.comp Y.subtype) (B.subgroupOf Y) :=
    (hB.isOffender ρ).subgroupOf ρ hBY
  have hC : IsOffender FivePair.action C := by
    let := hB'.1.2
    refine ⟨⟨fun hz => hB'.1.1
      ((map_eq_bot_iff_of_injective _ c.action.groupEquiv.injective).mp hz),
      IsElementaryAbelian.map _⟩, ?_⟩
    rw [rank_map_injective _ c.action.groupEquiv.injective,←c.symmetric_fixedCodim]
    exact hB'.2
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hjC : C.map j = B := by
    rw [map_map]
    have hj : j.comp c.action.groupEquiv.toMonoidHom = Y.subtype := by
      ext x
      simp [j]
    rw [hj,map_subgroupOf_eq_of_le hBY]
  obtain ⟨e,hbase,hemap⟩ := source_two_factor_five_whole_action ρ hf T hP ⟨A,hA⟩ hcore d c
  have heact (a : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) (v : V) :
      e.linearEquiv (ρ (j a) v) = FivePair.action a (e.linearEquiv v) := by
    change e.linearEquiv.toLinearMap _ = FivePair.action a (e.linearEquiv.toLinearMap _)
    rw [hemap]
    have hh := c.symmetricCoreMap_action (c.action.groupEquiv.symm a) v
    simpa [j,Y] using hh
  have hebase (a : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) :
      e.groupEquiv (j a) = FivePair.base a := by
    apply FivePair.wreathRepresentation_injective
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := e.linearEquiv.surjective v
    rw [←e.intertwines,heact]
    exact (FivePair.wreathToLinear_base a (e.linearEquiv u)).symm
  have hn : ¬ IsStrongFFModule (coreRepresentation (Fin 5)) :=
    fun ⟨E,hE⟩ => Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) E hE
  obtain ⟨hsplit,h₁,h₂⟩ := offender_product_of_not_strong _ _ hn hn hC
  intro g hg
  have hcomm (a : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) (ha : a ∈ C) :
      FivePair.base a * e.groupEquiv g = e.groupEquiv g * FivePair.base a := by
    rw [←hebase,←map_mul,←map_mul]
    apply congrArg e.groupEquiv
    exact mem_centralizer_iff.mp hg (j a) (hBA (hjC ▸ mem_map_of_mem j ha))
  have hw : (e.groupEquiv g).right = 1 := by
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact (hC.1.1 (by rw [hsplit,h₁,h₂,bot_prod_bot])).elim
      · obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h₂.1.1
        exact centralizer_base_second (e.groupEquiv g) a
          (fun hh => ha (Subtype.ext hh)) (hcomm (1,a) (hsplit.ge ⟨one_mem _,a.property⟩))
    · obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h₁.1.1
      exact centralizer_base_first (e.groupEquiv g) a
        (fun hh => ha (Subtype.ext hh)) (hcomm (a,1) (hsplit.ge ⟨a.property,one_mem _⟩))
  have hgmap : e.groupEquiv g ∈ Y.map e.groupEquiv.toMonoidHom := by
    rw [hbase]
    exact hw
  obtain ⟨y,hy,hyg⟩ := hgmap
  have hyG : y=g := e.groupEquiv.injective hyg
  exact hyG ▸ hy
/-- All three actual small chief alternatives satisfy the same centralizer bound. -/
theorem small_offender_centralizer_le_offenderSubgroup
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hcore : pCore 2 D = ⊥)
    (hsmall : SmallNaturalWreathAction ρ ∨ ChiefFiveMarkedSection ρ ∨
      ∃ d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5))))
    {A : Subgroup D} (hA : IsOffender ρ A) :
    centralizer (A : Set D) ≤ offenderSubgroup ρ := by
  let := hi
  rcases hsmall with hs | ⟨hqs,c,⟨e⟩⟩ | ⟨d,⟨c⟩⟩
  · exact small_natural_offender_centralizer_le ρ T hP hs hcore hf hA
  · obtain ⟨_,hY⟩ := source_quasisimple_five_whole_action ρ hf T hP ⟨A,hA⟩ hcore hqs c e
    rw [hY]
    exact le_top
  · exact source_pair_five_offender_centralizer_le ρ hf T hP hcore d c hA

/-- The bound on the literal original chief image, deriving its faithful,
irreducible, reduced minimal-parabolic hypotheses from the original action. -/
theorem minimalParabolic_small_chief_offender_centralizer_le
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ∃ d : SourceTwoFactorCase ((imageRepresentation ρ).comp
        (offenderSubgroup (imageRepresentation ρ)).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5))))
    {B : Subgroup (actionImage ρ)} (hB : IsOffender (imageRepresentation ρ) B) :
    centralizer (B : Set (actionImage ρ)) ≤ offenderSubgroup (imageRepresentation ρ) := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1.1
    obtain ⟨g,hg⟩ := hq (b : actionImage ρ)
    apply hb
    apply Subtype.ext
    change (b : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  exact small_offender_centralizer_le_offenderSubgroup _ (imageRepresentation_injective ρ)
    (imageRepresentation_irreducible ρ inferInstance) (S.mapSurjective hq)
    (minimalParabolic_reduced_image S hS q hq hc hn).2 hc hsmall hB

/-- An original elementary actor whose chief image contains an offender
already has its entire image in the offender subgroup. -/
theorem chief_small_elementary_actor_le_offenderSubgroup
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ∃ d : SourceTwoFactorCase ((imageRepresentation ρ).comp
        (offenderSubgroup (imageRepresentation ρ)).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5))))
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    {B : Subgroup (actionImage ρ)} (hB : IsOffender (imageRepresentation ρ) B)
    (hBA : B ≤ actionSubgroup ρ A) :
    actionSubgroup ρ A ≤ offenderSubgroup (imageRepresentation ρ) := by
  apply le_trans ?_ (minimalParabolic_small_chief_offender_centralizer_le ρ S hS hsmall hB)
  let : IsElementaryAbelian 2 (actionSubgroup ρ A) := IsElementaryAbelian.map (actionHom ρ)
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  exact congrArg Subtype.val (mul_comm' (⟨b,hBA hb⟩ : actionSubgroup ρ A) ⟨a,ha⟩)

end CFSG.Quasithin.ChapterB
