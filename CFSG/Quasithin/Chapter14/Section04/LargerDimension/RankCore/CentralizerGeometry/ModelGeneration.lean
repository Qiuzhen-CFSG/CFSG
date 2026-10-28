module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Source
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Alternating.Aut
public import CFSG.Quasithin.ChapterH.Section10To12.Defs

/-!
# Model generation in the literal four alternatives of 14.4.2

The source calculation in 14.4.7 is a calculation in the actual residual
image `K*` of `H/O₂(H)`.  This file records the reusable group-theoretic
calculation behind it.  A noncentral actor on a normal quasisimple component
gives the whole component by the component dichotomy.  For `S₇` the actor's
exact elementary order eight excludes the trivial centralizer.  For the
genuine triple cover of `M₂₂`, the centralizer is contained in the generalized
Fitting subgroup and its intersection with the cover is central of order three,
which is again too small for an order-thirty-two actor.  In `Ω⁺₄(4)`, the
marked element interchanges the two embedded components; its component orbit is
therefore the full residual.  The product alternative retains the exact
rank-three projection argument: an order-eight elementary subgroup cannot
project trivially to either factor because the two factors have binary ranks
one and two.

These are the literal residual and marked-subgroup interfaces used by the
consumer in `CentralizerGeometry.Source`; no `g² = 1` or transported marking
is built into them.

Source: Aschbacher--Smith, 14.4.2(3)--(6) and 14.4.7, printed pp.1006 and
1008--1009.

The complete calculation from the actual model alternatives and its literal
quotient consumer are in `ModelGeneration.SourceCases`. This base module
retains the earlier conditional interfaces for compatibility.
-/

@[expose] public section

open Subgroup
open Theory.GroupTheory
open CFSG.Quasithin.ChapterH.Section10To12
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry

variable {Q : Type*} [Group Q]

/-! ### The component calculation -/

theorem component_commutator_eq_self (K X : Subgroup Q) [K.Normal]
    [IsQuasisimple K] (hcentral : ¬ X ≤ centralizer (K : Set Q)) :
    ⁅K, X⁆ = K := by
  let hK : IsComponent Q K :=
    ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  rcases hK.commutator_dichotomy X with hb | he
  · rw [commutator_comm] at hb
    exact (hcentral (commutator_eq_bot_iff_le_centralizer.mp hb)).elim
  · have horbit : (⨆ a : X, K.map (MulAut.conj (a : Q)).toMonoidHom) = K := by
      apply le_antisymm
      · apply iSup_le
        intro a
        exact (Normal.map_conj_eq K (a : Q)).le
      · exact le_iSup_of_le (1 : X) (by
          convert (le_rfl : K ≤ K) using 1; ext x; simp)
    rw [horbit] at he
    exact he

theorem simple_commutator_eq_self (K X : Subgroup Q) [K.Normal]
    [IsSimpleGroup K] [Group.IsPerfect K]
    (hcentral : ¬ X ≤ centralizer (K : Set Q)) :
    ⁅K, X⁆ = K := by
  rcases simple_subnormal_commutator_dichotomy K X
      (inferInstance : K.Normal).isSubnormal with hb | he
  · rw [commutator_comm] at hb
    exact (hcentral (commutator_eq_bot_iff_le_centralizer.mp hb)).elim
  · have horbit : (⨆ a : X, K.map (MulAut.conj (a : Q)).toMonoidHom) = K := by
      apply le_antisymm
      · apply iSup_le
        intro a
        exact (Normal.map_conj_eq K (a : Q)).le
      · exact le_iSup_of_le (1 : X) (by
          convert (le_rfl : K ≤ K) using 1; ext x; simp)
    rw [horbit] at he
    exact he

/-! ### The `Ω⁺₄(4)` component interchange -/

/-- Legacy conditional interface, retained for compatibility. Its ambient
normality assumption on L₁ is incompatible with the distinct-component swap.
The source calculation in `ModelGeneration.Components` instead proves
subnormality of the actual embedded factors and uses no such assumption. -/
theorem orthogonal_four_plus_generation (K L₁ L₂ X : Subgroup Q) [K.Normal]
    [L₁.Normal] (hcomponent : IsComponent Q L₁)
    (hK : K = L₁ ⊔ L₂) (hL₁K : L₁ ≤ K)
    (hXK : X ≤ normalizer (K : Set Q)) (hne : L₁ ≠ L₂)
    (hinter : ∃ x : X,
      L₁.map (MulAut.conj (x : Q)).toMonoidHom = L₂) :
    ⁅K, X⁆ = K := by
  obtain ⟨x, hx⟩ := hinter
  have horbit_le : (⨆ a : X, L₁.map (MulAut.conj (a : Q)).toMonoidHom) ≤ K := by
    apply iSup_le
    intro a
    have hmapK := mem_normalizer_iff_map_conj_eq.mp (hXK a.property)
    rw [← hmapK]
    exact map_mono hL₁K
  have horbit_ge : K ≤ (⨆ a : X, L₁.map (MulAut.conj (a : Q)).toMonoidHom) := by
    rw [hK]
    apply sup_le
    · exact le_iSup_of_le (1 : X) (by
        convert (le_rfl : L₁ ≤ L₁) using 1; ext y; simp)
    · rw [← hx]
      exact le_iSup (fun a : X => L₁.map (MulAut.conj (a : Q)).toMonoidHom) x
  have horbit : (⨆ a : X, L₁.map (MulAut.conj (a : Q)).toMonoidHom) = K :=
    le_antisymm horbit_le horbit_ge
  have hnotcentral : ¬ X ≤ centralizer (L₁ : Set Q) := by
    intro hc
    have hxl := (centralizer_le_normalizer (L₁ : Set Q)) (hc x.property)
    have heq := mem_normalizer_iff_map_conj_eq.mp hxl
    exact hne (heq.symm.trans hx)
  rcases hcomponent.commutator_dichotomy X with hb | he
  · rw [commutator_comm] at hb
    exact (hnotcentral (commutator_eq_bot_iff_le_centralizer.mp hb)).elim
  · rw [horbit] at he
    apply le_antisymm (commutator_le_left K X)
    calc
      K = ⁅L₁, X⁆ := he.symm
      _ ≤ ⁅K, X⁆ := commutator_mono hL₁K le_rfl

/-! ### The `S₇` branch -/

theorem symmetric_seven_generation (K X : Subgroup Q) [K.Normal]
    (hmodel : K ≃* alternatingGroup (Fin 7))
    (hcentral : centralizer (K : Set Q) = ⊥)
    (hX : Nat.card X = 8) : ⁅K, X⁆ = K := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num [Nat.card_fin])
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num [Nat.card_fin])⟩
  let : IsSimpleGroup K := hmodel.isSimpleGroup
  let : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := hmodel.symm.toMonoidHom) hmodel.symm.surjective
  apply simple_commutator_eq_self K X
  intro hXc
  have hXbot : X = ⊥ := le_bot_iff.mp (hcentral ▸ hXc)
  rw [hXbot] at hX
  norm_num at hX

/-! ### The genuine triple cover of `M₂₂` -/

theorem triple_M22_generation (K X : Subgroup Q)
    (hmodel : IsTripleM22 (K : Subgroup Q))
    (hF : generalizedFitting Q = K) [K.Normal]
    [Finite Q] (_hquot : IsPGroup 2 (Q ⧸ K)) (hX : Nat.card X = 32) :
    ⁅K, X⁆ = K := by
  let : IsQuasisimple K := hmodel.quasisimple
  have hres : pResidual 2 Q = K :=
    (SimpleSocle.layer_residuals K _hquot).2.1
  have hC : centralizer (K : Set Q) ≤ K := by
    rw [← hF]
    exact centralizer_generalizedFitting_le Q
  apply component_commutator_eq_self K X
  intro hXc
  have hXC : X ≤ K := hXc.trans hC
  have hcenter : X ≤ (center K).map K.subtype := by
    intro x hx
    let xK : K := ⟨x, hXC hx⟩
    have hxK : xK ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (hXc hx)) y y.property
    exact ⟨xK, hxK, rfl⟩
  have hdvd : Nat.card X ∣ Nat.card ((center K).map K.subtype) :=
    card_dvd_of_le hcenter
  have hc := Subgroup.card_map_of_injective K.subtype_injective (K := center K)
  rw [hX, hc, hmodel.center_card] at hdvd
  norm_num at hdvd

/-! ### Exact rank-three projections in the product branch -/

namespace ProductModel

variable {X : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))}

theorem snd_nonbot_of_card_eight (hX : Nat.card X = 8)
    (hEl : IsElementaryAbelian 2 X) :
    X.map (MonoidHom.fst _ _) ≠ ⊥ := by
  intro h
  let f : X → Equiv.Perm (Fin 5) :=
    fun a => (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).2
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · have ha : (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).1 = 1 := by
        have ha' : (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).1 ∈
            X.map (MonoidHom.fst _ _) := mem_map_of_mem _ a.property
        rw [h] at ha'
        exact mem_bot.mp ha'
      have hb : (b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).1 = 1 := by
        have hb' : (b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).1 ∈
            X.map (MonoidHom.fst _ _) := mem_map_of_mem _ b.property
        rw [h] at hb'
        exact mem_bot.mp hb'
      simp [ha, hb]
    · exact hab
  let E := X.map (MonoidHom.snd _ _)
  let f' : X → E := fun a => ⟨f a, mem_map_of_mem _ a.property⟩
  have hf' : Function.Injective f' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg Subtype.val (hf (congrArg Subtype.val hab))
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hle : Nat.card X ≤ Nat.card E :=
    Finite.card_le_of_injective' hf' (by
      intro hz
      exact (Nat.ne_of_gt hpos hz).elim)
  have hE : IsElementaryAbelian 2 E := hEl.map _
  have hbound := (primeRank_le_iff_elementary_card_le
      (Equiv.Perm (Fin 5))).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    _ hE
  rw [hX] at hle
  omega

theorem fst_nonbot_of_card_eight (hX : Nat.card X = 8)
    (hEl : IsElementaryAbelian 2 X) :
    X.map (MonoidHom.snd _ _) ≠ ⊥ := by
  intro h
  let f : X → Equiv.Perm (Fin 3) :=
    fun a => (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).1
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · exact hab
    · have ha : (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).2 = 1 := by
        have ha' : (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).2 ∈
            X.map (MonoidHom.snd _ _) := mem_map_of_mem _ a.property
        rw [h] at ha'
        exact mem_bot.mp ha'
      have hb : (b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).2 = 1 := by
        have hb' : (b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)).2 ∈
            X.map (MonoidHom.snd _ _) := mem_map_of_mem _ b.property
        rw [h] at hb'
        exact mem_bot.mp hb'
      simp [ha, hb]
  let E := X.map (MonoidHom.fst _ _)
  let f' : X → E := fun a => ⟨f a, mem_map_of_mem _ a.property⟩
  have hf' : Function.Injective f' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg Subtype.val (hf (congrArg Subtype.val hab))
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hle : Nat.card X ≤ Nat.card E :=
    Finite.card_le_of_injective' hf' (by
      intro hz
      exact (Nat.ne_of_gt hpos hz).elim)
  have hE : IsElementaryAbelian 2 E := hEl.map _
  have hbound := (primeRank_le_iff_elementary_card_le
      (Equiv.Perm (Fin 3))).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricThree_primeRank_le_one
    _ hE
  rw [hX] at hle
  omega

/-! The remaining factor calculation is exposed at the exact source interface:
the two axis commutators are the only model-specific inputs, while the
elementary rank argument above proves that both projections are nontrivial.
This avoids silently replacing the rank-three actor by a rank-greater-than-one
assumption. -/

theorem product_generation_of_axis_commutators
    (K X : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)))
    [K.Normal] (hK : K =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 5)))
    (hleft : (alternatingGroup (Fin 3)).map (MonoidHom.inl _ _) ≤ ⁅K, X⁆)
    (hright : (alternatingGroup (Fin 5)).map (MonoidHom.inr _ _) ≤ ⁅K, X⁆) :
    ⁅K, X⁆ = K := by
  apply le_antisymm (commutator_le_left K X)
  rw [hK] at hleft hright ⊢
  exact (prod_le_iff.mpr ⟨hleft, hright⟩)

end ProductModel

/-! ### A literal consumer application

The following theorem is the source-facing application used by 14.4.7.  Its
quotient is the one in `EarlierGeometry.centralizer_eq_bot_of_star_generation`
and its actor is the literal image of `W`; the model equalities are rewritten
before the consumer is called.  In particular, no symmetry assumption on `g`
is introduced. -/

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

theorem EarlierGeometry.centralizer_eq_bot_of_symmetric_seven
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (T M : Subgroup G) (hTH : T ≤ H) (hTL : T ≤ normalizer (L : Set G))
    (K X : Subgroup ((conjugate H g) ⧸ pCore 2 (conjugate H g)))
    [K.Normal]
    (hK : (pResidual 2 (conjugate H g)).map
      (QuotientGroup.mk' (pCore 2 (conjugate H g))) = K)
    (hX : ((W U V₂).subgroupOf (conjugate H g)).map
      (QuotientGroup.mk' (pCore 2 (conjugate H g))) = X)
    (hmodel : K ≃* alternatingGroup (Fin 7))
    (hcentral : centralizer
      (K : Set ((conjugate H g) ⧸ pCore 2 (conjugate H g))) = ⊥)
    (hXcard : Nat.card X = 8)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ conjugate T g ≤ N → N = M)
    (hKM : ¬ conjugate ((pResidual 2 H).map H.subtype) g ≤ M) :
    conjugate ((pResidual 2 H).map H.subtype) g ≤
        centralizer (D H U g : Set G) ∧
      D H U g ⊓ centralizer (L : Set G) = ⊥ := by
  apply d.centralizer_eq_bot_of_star_generation hrank T M hTH hTL
    (by rw [hK, hX]; exact (symmetric_seven_generation K X hmodel hcentral hXcard).symm)
    hunique hKM

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
