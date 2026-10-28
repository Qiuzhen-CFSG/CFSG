module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.LinearReciprocal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LinearReciprocal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import Theory.Representation.BinaryPermutation.SixCoreSmallImage
public import Theory.Representation.BinaryConjugationCoordinates.FixedIndex
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank

/-!
# The two action indices in a mixed reciprocal linear pair: structure at the original group

Let U=V₀ be the actual six-dimensional omega module. Its proved non-FF
property gives |V:C_V(Uᵍ)| < |Uᵍ:C_{Uᵍ}(V)| whenever the mixed commutator
is nontrivial and the reciprocal containments hold. If the first index
were two, the hyperplane-fixer calculation for the original augmentation
core would bound the second by two, a contradiction. The elementary
S₆ actor has order at most eight, so the indices are exactly four and
eight. Consequently both literal fixed groups have order eight; mutual
normalization places the commutator in their intersection.

The final theorem applies this to the original pair A=H₂, B=L₂T with
Uᵍ≤O₂(B) and V≤O₂(B)ᵍ. Whole-module recognition and the non-FF theorem
already cover the natural-plus-dual, point-core and line-core rows, so
no extra module or small-image premise is assumed. Original Hypothesis1331,
ChosenModule, CoreMarking, Structural1222 and Source1332OneTwo remain intact.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/MixedLinearIndices` proof for the local step.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Theory.GroupTheory Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A hyperplane fixed in the actual core permits an action image of order at most two. -/
theorem core_actor_index_le_two_of_fixed_index_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (A : Subgroup G) (hAM : A ≤ normalizer (L : Set G))
    (hsmall : (centralizer (A : Set G)).relIndex V ≤ 2) :
    (centralizer (V : Set G)).relIndex A ≤ 2 := by
  have hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,hq,_,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hAM)
  have hf (a : A) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨a.val,(hAM.trans hn) a.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (f a) (m.coordinate v).toAdd :=
    hq (inclusion hAM a) v
  have hi := model_fixed_index A V (hAM.trans hn)
    (BinaryPermutation.coreRepresentation (Fin 6)) f m.coordinate hf
  have hd : fixedCodim (BinaryPermutation.coreRepresentation (Fin 6)) f.range ≤ 1 := by
    have hp : 2 ^ fixedCodim (BinaryPermutation.coreRepresentation (Fin 6)) f.range ≤ 2 ^ 1 :=
      hi.symm ▸ hsmall
    exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hp
  have hb := BinaryPermutation.SixCoreSmallImage.card_le_two_of_fixedCodim_le_one f.range hd
  have hc := model_card_range A V (hAM.trans hn)
    (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
    f m.coordinate hf
  rw [inf_relIndex_left] at hc
  rwa [hc] at hb

omit [Finite G] in
private theorem centralizer_index_conj_at (A B : Subgroup G) (g : G) :
    (centralizer (A.conjBy g : Set G)).relIndex (B.conjBy g) =
      (centralizer (A : Set G)).relIndex B := by
  change (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
    (B.map (MulAut.conj g).toMonoidHom) = _
  rw [coe_map, MulEquiv.coe_toMonoidHom, ← Theory.GroupTheory.map_centralizer_equiv (A : Set G) (MulAut.conj g)]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

private theorem index_lt_of_nonFF_image_at
    (H U A : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 A]
    (hHU : H ≤ normalizer (U : Set G))
    (hn : ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hHU)))))
    (hAH : A ≤ H) (hm : ¬ A ≤ centralizer (U : Set G)) :
    (centralizer (U : Set G)).relIndex A < (centralizer (A : Set G)).relIndex U := by
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion hHU))
  let e : U ≃* Multiplicative (Additive U) := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul u)
    invFun v := v.toAdd.toMul
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact centralizer_index_lt_of_nonFF A U (hAH.trans hHU) (imageRepresentation ρ)
    (imageRepresentation_injective ρ) ((actionHom ρ).comp (inclusion hAH)) e
      (fun _ _ => rfl) hn hm

/-- The order-two branch of the mixed non-FF comparison is impossible. -/
theorem mixed_nonFF_indices_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (hn : ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hHU)))))
    (g : G) (h₁ : U.conjBy g ≤ normalizer (L : Set G)) (h₂ : V ≤ H.conjBy g)
    (hm : ⁅V,U.conjBy g⁆ ≠ ⊥) :
    2 < (centralizer (U.conjBy g : Set G)).relIndex V ∧
      (centralizer (U.conjBy g : Set G)).relIndex V <
        (centralizer (V : Set G)).relIndex (U.conjBy g) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy g⁻¹) := IsElementaryAbelian.map _
  have hVH : V.conjBy g⁻¹ ≤ H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₂
    change V.conjBy g⁻¹ ≤ (H.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hmove : ¬ V.conjBy g⁻¹ ≤ centralizer (U : Set G) := by
    intro hc
    have hc' := map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rw [Theory.GroupTheory.map_centralizer_equiv (U : Set G) (MulAut.conj g)] at hc'
    change (V.conjBy g⁻¹).conjBy g ≤ centralizer (U.conjBy g : Set G) at hc'
    rw [conjBy_inv'] at hc'
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr hc')
  have hi := index_lt_of_nonFF_image_at H U (V.conjBy g⁻¹) hHU hn hVH hmove
  have ht := centralizer_index_conj_at U (V.conjBy g⁻¹) g
  have hu := centralizer_index_conj_at (V.conjBy g⁻¹) U g
  rw [conjBy_inv'] at ht hu
  rw [←ht,←hu] at hi
  refine ⟨?_,hi⟩
  by_contra! hs
  have hb := core_actor_index_le_two_of_fixed_index_at h structural D m (U.conjBy g) h₁ hs
  have hne : (centralizer (U.conjBy g : Set G)).relIndex V ≠ 1 :=
    fun he => hm (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp he))
  have hp : (centralizer (U.conjBy g : Set G)).relIndex V ≠ 0 := index_ne_zero_of_finite
  omega

/-- The actual full-normalizer action of an elementary subgroup has order at most eight. -/
theorem core_elementary_actor_index_le_eight_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAM : A ≤ normalizer (L : Set G)) :
    (centralizer (V : Set G)).relIndex A ≤ 8 := by
  have hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,hq,_,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hAM)
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := model_card_range A V (hAM.trans hn)
    (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
    f m.coordinate (fun a v => hq (inclusion hAM a) v)
  rw [inf_relIndex_left] at hc
  rw [←hc]
  exact (primeRank_le_iff_elementary_card_le _).mp
    BinaryNaturalDual.FiveActors.ModuleGeometry.symmetric_six_rank_le_three f.range inferInstance

/-- The remaining mixed non-FF action has the exact indices four and eight. -/
theorem mixed_nonFF_exact_indices_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (hn : ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hHU)))))
    (g : G) (h₁ : U.conjBy g ≤ normalizer (L : Set G)) (h₂ : V ≤ H.conjBy g)
    (hm : ⁅V,U.conjBy g⁆ ≠ ⊥) :
    (centralizer (U.conjBy g : Set G)).relIndex V = 4 ∧
      (centralizer (V : Set G)).relIndex (U.conjBy g) = 8 := by
  let := D.elementary
  let : IsElementaryAbelian 2 (U.conjBy g) := IsElementaryAbelian.map _
  obtain ⟨hlo,hlt⟩ := mixed_nonFF_indices_at h structural D m H U hHU hn g h₁ h₂ hm
  have hhi := core_elementary_actor_index_le_eight_at h structural D m (U.conjBy g) h₁
  obtain ⟨i,hi⟩ := (IsElementaryAbelian.isPGroup 2 V).index
    ((centralizer (U.conjBy g : Set G)).subgroupOf V)
  obtain ⟨j,hj⟩ := (IsElementaryAbelian.isPGroup 2 (U.conjBy g)).index
    ((centralizer (V : Set G)).subgroupOf (U.conjBy g))
  change (centralizer (U.conjBy g : Set G)).relIndex V = 2 ^ i at hi
  change (centralizer (V : Set G)).relIndex (U.conjBy g) = 2 ^ j at hj
  rw [hi] at hlo hlt
  rw [hj] at hlt hhi
  have hi₁ : 1 < i := (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hlo
  have hij : i < j := (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hlt
  have hj₃ : j ≤ 3 := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hhi
  have hi₂ : i = 2 := by omega
  have hj₃' : j = 3 := by omega
  exact ⟨hi.trans (by rw [hi₂]; rfl),hj.trans (by rw [hj₃']; rfl)⟩


/-- In the six-dimensional case both literal fixed groups have order eight,
and the mixed commutator lies in their intersection. -/
theorem mixed_nonFF_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (hn : ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hHU)))))
    (hcard : Nat.card U = 64)
    (g : G) (h₁ : U.conjBy g ≤ normalizer (L : Set G)) (h₂ : V ≤ H.conjBy g)
    (hm : ⁅V,U.conjBy g⁆ ≠ ⊥) :
    (centralizer (U.conjBy g : Set G)).relIndex V = 4 ∧
      (centralizer (V : Set G)).relIndex (U.conjBy g) = 8 ∧
      Nat.card (V ⊓ centralizer (U.conjBy g : Set G) : Subgroup G) = 8 ∧
      Nat.card (U.conjBy g ⊓ centralizer (V : Set G) : Subgroup G) = 8 ∧
      ⁅V,U.conjBy g⁆ ≤ (V ⊓ centralizer (U.conjBy g : Set G)) ⊓
        (U.conjBy g ⊓ centralizer (V : Set G)) := by
  obtain ⟨hi,hj⟩ := mixed_nonFF_exact_indices_at h structural D m H U hHU hn g h₁ h₂ hm
  have hcV := relIndex_mul_relIndex (⊥ : Subgroup G)
    (V ⊓ centralizer (U.conjBy g : Set G)) V bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hi,m.card_module] at hcV
  have hcU := relIndex_mul_relIndex (⊥ : Subgroup G)
    (U.conjBy g ⊓ centralizer (V : Set G)) (U.conjBy g) bot_le inf_le_left
  have hcUg : Nat.card (U.conjBy g) = 64 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hcard
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hj,hcUg] at hcU
  let := D.elementary
  let : IsElementaryAbelian 2 (U.conjBy g) := IsElementaryAbelian.map _
  have hUV : U.conjBy g ≤ normalizer (V : Set G) :=
    h₁.trans (normalizer_component_le_module_at h structural D m)
  have hVU : V ≤ normalizer (U.conjBy g : Set G) :=
    h₂.trans ((map_mono hHU).trans (U.le_normalizer_map (MulAut.conj g).toMonoidHom))
  have hcommV : ⁅V,U.conjBy g⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hUV
  have hcommU : ⁅V,U.conjBy g⁆ ≤ U.conjBy g :=
    le_normalizer_iff_commutator_le_right.mp hVU
  exact ⟨hi,hj,by omega,by omega,
    le_inf (le_inf hcommV (hcommU.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))
      (le_inf hcommU (hcommV.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))⟩

open Stellmacher Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- Apply the mixed comparison to the actual original pair and literal
R₂=O₂(B), including the two fixed subgroups and the shared commutator bound. -/
theorem original_linear_pair_mixed_indices_and_centralizers_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (hBM : B ≤ normalizer (L : Set G)) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    Nat.card U = 64 ∧ ∀ g : G,
      U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      (centralizer (U.conjBy g : Set G)).relIndex V = 4 ∧
        (centralizer (V : Set G)).relIndex (U.conjBy g) = 8 ∧
        Nat.card (V ⊓ centralizer (U.conjBy g : Set G) : Subgroup G) = 8 ∧
        Nat.card (U.conjBy g ⊓ centralizer (V : Set G) : Subgroup G) = 8 ∧
        ⁅V,U.conjBy g⁆ ≤ (V ⊓ centralizer (U.conjBy g : Set G)) ⊓
          (U.conjBy g ⊓ centralizer (V : Set G)) := by
  obtain ⟨he,hn,hcard,_⟩ := original_linear_pair_module_nonFF_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin
  let := he
  refine ⟨hcard,fun g h₁ h₂ hm => ?_⟩
  exact mixed_nonFF_centralizers_at h structural D m (A ⊔ B)
    (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))
    (le_normalizer_conjugateSpanBy _ _) hn hcard g
    (h₁.trans ((pCoreIn_le 2 B).trans hBM))
    (h₂.trans (map_mono ((pCoreIn_le 2 B).trans le_sup_right))) hm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
