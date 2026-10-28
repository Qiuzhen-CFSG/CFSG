module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Cover
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.MovedCore
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The actual five-dimensional module at a nonsingular point

Restrict the original augmentation cover to the six complementary letters.
Its projection to V/C_V(L) is injective, and equivariance identifies its
ambient image with V_v=[V,L_v]. This constructs an actual core marking,
retaining the original conjugation and quotient projection. In particular
V_v has order 32, lies in O₂(L_v), and meets C_V(L) trivially.

The constant six-letter word supplies the source vector v₀. It generates
C_{V_v}(L_v), has the same image as v in V/C_V(L), and is nonsingular.
The literal consumer gives m₂(K_v)≥5 using V_v≤L_v≤K_v. The later block
argument's movement of this fixed line forces C_V(L)≠1, since the canonical
K_v centralizes v. The movement premise is not asserted here.

Component recognition, the block/splitting arguments and the fusion and
weak-closure steps remain necessary for 12.6.2 and 12.6.23.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
the paragraph preceding 12.6.6, printed p.824; the rank input in12.6.12,
pp.825--826, and the fixed-line arguments in12.6.17--18, p.827.
-/

@[expose] public noncomputable section
open Subgroup Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem Vv_le_V (hn : L ≤ normalizer (V : Set G)) (v : G) : Vv L V v ≤ V :=
  le_normalizer_iff_commutator_le_left.mp ((Lv_le_L L v).trans hn)

omit [Finite G] in
/-- The chosen-module inclusion supplies the elementary structure on the actual commutator. -/
theorem Vv_elementary (hn : L ≤ normalizer (V : Set G)) (v : G) :
    IsElementaryAbelian 2 (Vv L V v) := IsElementaryAbelian.of_le (Vv_le_V hn v)

/-- A six-letter core maps bijectively onto the literal ambient commutator.
Its action and projection are those of the original source marking. -/
theorem OrthogonalMarking.local_core_image
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    ∃ F : core (Fin 6) →ₗ[ZMod 2] Additive V,
      Function.Injective F ∧
      (V.subtype.comp F.toAddMonoidHom.toMultiplicativeLeft).range = Vv L V (v : G) ∧
      (∀ l : Lv L (v : G), ∀ w,
        F (alternatingCoreRepresentation (Fin 6) (D.localSixMap v i j hij hp l) w) =
          seedRepresentation L V chosen.normalizes (inclusion (Lv_le_L L (v : G)) l) (F w)) ∧
      ∀ w, D.coordinates (Submodule.Quotient.mk (F w)) =
        coreToNatural (Fin 8) (extendSix i j hij w) := by
  obtain ⟨f,hf,he,hproj⟩ := D.core_cover chosen
  let F := f.comp (extendSix i j hij)
  let ψ := V.subtype.comp F.toAddMonoidHom.toMultiplicativeLeft
  have hFi : Function.Injective F := by
    intro x y hxy
    apply toNatural_extendSix_injective i j hij
    exact (hproj _).symm.trans ((congrArg (fun w : Additive V =>
      D.coordinates (Submodule.Quotient.mk w)) hxy).trans (hproj _))
  have hFR : ψ.range = Vv L V (v : G) := by
    let W : Submodule (ZMod 2) (Additive V) :=
      AddSubgroup.toZModSubmodule 2 ((Vv L V (v : G)).subgroupOf V).toAddSubgroup
    let ρ := (alternatingCoreRepresentation (Fin 8)).comp (pointFixer i j).subtype
    have hW : Coinvariants.ker ρ ≤ W.comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,w⟩,rfl⟩
      obtain ⟨l,rfl⟩ := D.localPairMap_surjective v i j hij hp a
      change (f (alternatingCoreRepresentation (Fin 8)
        (D.actorMap (inclusion (Lv_le_L L (v : G)) l)) w - w)).toMul.val ∈ Vv L V (v : G)
      rw [map_sub,he]
      change (l : G) * ((f w).toMul : G) * (l : G)⁻¹ / ((f w).toMul : G) ∈ Vv L V (v : G)
      rw [div_eq_mul_inv]
      change ⁅(l : G), ((f w).toMul : G)⁆ ∈ Vv L V (v : G)
      rw [Vv,commutator_comm]
      exact commutator_mem_commutator l.property (f w).toMul.property
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact hW ((pointFixer_moved_core i j hij).ge ⟨w.toAdd,rfl⟩)
    · rw [Vv,commutator_comm]
      apply commutator_le.mpr
      intro l hl x hx
      obtain ⟨w,hw⟩ := hf (Additive.ofMul (show V from ⟨x,hx⟩))
      let l' : Lv L (v : G) := ⟨l,hl⟩
      let a := D.localPairMap v i j hij hp l'
      have hm := (pointFixer_moved_core i j hij).le (Coinvariants.sub_mem_ker (ρ := ρ) a w)
      obtain ⟨u,hu⟩ := hm
      refine ⟨Multiplicative.ofAdd u,?_⟩
      have hfu := congrArg f hu
      change F u = f (alternatingCoreRepresentation (Fin 8)
        (D.actorMap (inclusion (Lv_le_L L (v : G)) l')) w - w) at hfu
      rw [map_sub,he,hw] at hfu
      have hval := congrArg (fun z : Additive V => (z.toMul : G)) hfu
      change ψ (Multiplicative.ofAdd u) = l * x * l⁻¹ / x at hval
      simpa only [div_eq_mul_inv, commutatorElement_def] using hval
  refine ⟨F,hFi,hFR,?_,fun w => hproj (extendSix i j hij w)⟩
  intro l w
  change f (extendSix i j hij (alternatingCoreRepresentation (Fin 6)
    (pointFixerEquiv i j hij (D.localPairMap v i j hij hp l)) w)) = _
  rw [extendSix_equivariant]
  exact he (inclusion (Lv_le_L L (v : G)) l) (extendSix i j hij w)

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem Lv_normalizes_Vv (L V : Subgroup G) (v : G) :
    Lv L v ≤ normalizer (Vv L V v : Set G) := normalizer_commutator_ge_right V (Lv L v)

/-- The actual five-dimensional core marking, with the original conjugation
and quotient projection. No nonsingular-centralizer containment is assumed. -/
theorem OrthogonalMarking.local_core_marking
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    let := Vv_elementary chosen.normalizes (v : G)
    ∃ E : core (Fin 6) ≃ₗ[ZMod 2] Additive (Vv L V (v : G)),
      (∀ l : Lv L (v : G), ∀ w,
        E (alternatingCoreRepresentation (Fin 6) (D.localSixMap v i j hij hp l) w) =
          seedRepresentation (Lv L (v : G)) (Vv L V (v : G)) (Lv_normalizes_Vv L V (v : G)) l (E w)) ∧
      ∀ w, D.coordinates (Submodule.Quotient.mk (Additive.ofMul
        (show V from ⟨(E w).toMul, Vv_le_V chosen.normalizes _ (E w).toMul.property⟩))) =
          coreToNatural (Fin 8) (extendSix i j hij w) := by
  let := Vv_elementary chosen.normalizes (v : G)
  obtain ⟨F,hF,hFR,he,hpF⟩ := D.local_core_image chosen v i j hij hp
  let ψ := V.subtype.comp F.toAddMonoidHom.toMultiplicativeLeft
  have hψ : Function.Injective ψ := by
    intro x y hxy
    exact hF (Subtype.ext hxy)
  let e : Multiplicative (core (Fin 6)) ≃* Vv L V (v : G) :=
    (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hFR)
  let E : core (Fin 6) ≃ₗ[ZMod 2] Additive (Vv L V (v : G)) :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditiveRight.toZModLinearMap 2) e.bijective
  refine ⟨E,?_,?_⟩
  · intro l w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : Additive V => (z.toMul : G)) (he l w)
  · intro w
    exact hpF w

/-- The rank-five input used in the component exclusion of 12.6.12. -/
theorem OrthogonalMarking.nonsingular_moved_card
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    Nat.card (Vv L V (v : G)) = 2 ^ 5 := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  let := Vv_elementary chosen.normalizes (v : G)
  obtain ⟨E,_,_⟩ := D.local_core_marking chosen v i j hij hp
  rw [← Nat.card_congr (Additive.toMul : Additive (Vv L V (v : G)) ≃ _),
    ← Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod,finrank_core]
  rfl

/-- Restricting the original projection to V_v is injective. -/
theorem OrthogonalMarking.nonsingular_moved_disjoint_fixed
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    Vv L V (v : G) ⊓ ZV L V = ⊥ := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨F,hF,hFR,_,hproj⟩ := D.local_core_image chosen v i j hij hp
  apply le_bot_iff.mp
  rintro x ⟨hx,hz⟩
  obtain ⟨w,hw⟩ := hFR.ge hx
  have he : Submodule.Quotient.mk (F w.toAdd) = (0 : Vhat L V chosen.normalizes) := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_fixedSeed_iff L V chosen.normalizes _).mpr
    change (F w.toAdd).toMul.val = x at hw
    rw [hw]
    exact hz
  have hw0 : w.toAdd = 0 := toNatural_extendSix_injective i j hij (by
    change coreToNatural (Fin 8) (extendSix i j hij w.toAdd) =
      coreToNatural (Fin 8) (extendSix i j hij 0)
    rw [← hproj,he,map_zero,map_zero,map_zero])
  have hFx : F w.toAdd = 0 := by rw [hw0,map_zero]
  change x = 1
  exact hw.symm.trans (congrArg (fun z : Additive V => (z.toMul : G)) hFx)

/-- The source vector v₀ generates C_{V_v}(L_v), and maps to the same
nonsingular vector as v under the original quotient projection. -/
theorem OrthogonalMarking.nonsingular_moved_fixed_line
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    ∃ v₀ : V, (v₀ : G) ∈ Vv L V (v : G) ∧ v₀ ≠ 1 ∧ D.Nonsingular v₀ ∧
      ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (v₀ : G) ∧
      (Submodule.Quotient.mk (Additive.ofMul v₀) : Vhat L V chosen.normalizes) =
        Submodule.Quotient.mk (Additive.ofMul v) := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨F,hF,hFR,he,hproj⟩ := D.local_core_image chosen v i j hij hp
  let z : core (Fin 6) := ⟨allOne (Fin 6), by change (∑ _ : Fin 6, (1 : ZMod 2)) = 0; decide⟩
  let v₀ : V := (F z).toMul
  have hzfix (a : alternatingGroup (Fin 6)) :
      alternatingCoreRepresentation (Fin 6) a z = z := by
    apply Subtype.ext
    exact permute_allOne (Fin 6) a.val
  have hfixed (w : core (Fin 6)) :
      (F w).toMul.val ∈ centralizer (Lv L (v : G) : Set G) ↔
        ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a w = w := by
    constructor
    · intro hc a
      obtain ⟨l,rfl⟩ := D.localSixMap_surjective v i j hij hp a
      apply hF
      rw [he]
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (F w).toMul.val * (l : G)⁻¹ = (F w).toMul.val
      rw [mem_centralizer_iff.mp hc l l.property,mul_inv_cancel_right]
    · intro hw
      apply mem_centralizer_iff.mpr
      intro l hl
      have hh := (he (⟨l,hl⟩ : Lv L (v : G)) w).symm.trans
        (congrArg F (hw (D.localSixMap v i j hij hp ⟨l,hl⟩)))
      have ha := congrArg (fun x : Additive V => (x.toMul : G)) hh
      change l * (F w).toMul.val * l⁻¹ = (F w).toMul.val at ha
      exact mul_inv_eq_iff_eq_mul.mp ha
  have hmem : (v₀ : G) ∈ Vv L V (v : G) := hFR.le ⟨Multiplicative.ofAdd z,rfl⟩
  have hquot : (Submodule.Quotient.mk (Additive.ofMul v₀) : Vhat L V chosen.normalizes) =
      Submodule.Quotient.mk (Additive.ofMul v) := by
    apply D.coordinates.injective
    exact (hproj z).trans ((extendSix_constant_projection i j hij z rfl).trans hp)
  have hnonsing : D.Nonsingular v₀ := by
    unfold OrthogonalMarking.Nonsingular
    rw [hquot]
    exact hv
  refine ⟨v₀,hmem,nonsingular_ne_one D hnonsing,hnonsing,?_,hquot⟩
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    obtain ⟨w,hw⟩ := hFR.ge hx
    change (F w.toAdd).toMul.val = x at hw
    have hc' := (hfixed w.toAdd).mp (hw.symm ▸ hc)
    have hconst := (core_fixed_iff_constant (by norm_num : 3 ≤ Nat.card (Fin 6)) w.toAdd).mp hc'
    obtain ⟨c,hc⟩ := (mem_constants_iff w.toAdd.val).mp hconst
    have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    have cases := hc01 c
    rcases cases with rfl | rfl
    · have hw0 : w.toAdd = 0 := Subtype.ext (funext hc)
      have hx1 : x = 1 := hw.symm.trans (congrArg (fun a : Additive V => (a.toMul : G))
        (show F w.toAdd = 0 by rw [hw0,map_zero]))
      rw [hx1]
      exact one_mem _
    · have hwz : w.toAdd = z := Subtype.ext (funext hc)
      have hxz : x = (v₀ : G) := hw.symm.trans (congrArg (fun a : Additive V => (a.toMul : G))
        (congrArg F hwz))
      rw [hxz]
      exact mem_zpowers _
  · exact zpowers_le.mpr ⟨hmem,(hfixed z).mpr hzfix⟩

omit [Finite G] in
/-- V normalizes the local residual, so its moved subgroup lies inside it. -/
theorem Vv_le_Lv (chosen : Section02.ChosenModule T L V) (v : V) :
    Vv L V (v : G) ≤ Lv L (v : G) := by
  apply le_normalizer_iff_commutator_le_right.mp
  exact (le_inf (chosen.le_component.trans L.le_normalizer) (V_le_Gv v)).trans
    (Mv_le_normalizer_Lv L (v : G))

omit [Finite G] in
/-- The actual moved module lies in the two-core of the local residual. -/
theorem Vv_le_core_Lv (chosen : Section02.ChosenModule T L V) (v : V) :
    Vv L V (v : G) ≤ (Lv L (v : G)).pCoreIn 2 := by
  let := Vv_elementary chosen.normalizes (v : G)
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    (Vv_le_Lv chosen v) (Lv_normalizes_Vv L V (v : G))

/-- The literal rank-five input to the source exclusion of quasisimple K_v.
The elementary subgroup is V_v itself, not an abstract model subgroup. -/
theorem SourceHypothesis.nonsingular_component_rank
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    Vv L V (v : G) ≤ Kv (v : G) ∧ 5 ≤ primeRank 2 (Kv (v : G)) := by
  obtain ⟨_,_,_,hLK⟩ := D.nonsingular_local_structure H.chosen H.source.quasisimple v hv
  have hVK := (Vv_le_Lv H.chosen v).trans hLK
  let := Vv_elementary H.chosen.normalizes (v : G)
  let : IsElementaryAbelian 2 ((Vv L V (v : G)).subgroupOf (Kv (v : G))) :=
    IsElementaryAbelian.subgroupOf hVK
  refine ⟨hVK,IsElementaryAbelian.primeRank_ge_of_card
    ((Vv L V (v : G)).subgroupOf (Kv (v : G))) ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]
  exact D.nonsingular_moved_card H.chosen v hv

/-- When the original fixed space is trivial, v itself is the local fixed-line
vector. This is the original-projection step in 12.6.17--18. -/
theorem OrthogonalMarking.local_fixed_line_of_fixed_eq_bot
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hz : ZV L V = ⊥) :
    ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (v : G) := by
  obtain ⟨v₀,_,_,_,hf,hq⟩ := D.nonsingular_moved_fixed_line chosen v hv
  have hd := (mem_fixedSeed_iff L V chosen.normalizes
    (Additive.ofMul v₀ - Additive.ofMul v)).mp ((Submodule.Quotient.eq _).mp hq)
  change (v₀ : G) / (v : G) ∈ ZV L V at hd
  rw [hz,mem_bot,div_eq_one] at hd
  rwa [hd] at hf

/-- The block argument's movement of C_{V_v}(L_v) by the canonical K_v forces
a nontrivial original fixed space. K_v centralizes the original v by construction. -/
theorem OrthogonalMarking.fixed_ne_bot_of_local_line_moved
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hm : ¬ ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ centralizer (Kv (v : G) : Set G)) :
    ZV L V ≠ ⊥ := by
  intro hz
  apply hm
  rw [D.local_fixed_line_of_fixed_eq_bot chosen v hv hz]
  apply zpowers_le.mpr
  apply mem_centralizer_iff.mpr
  intro k hk
  exact mem_centralizer_singleton_iff.mp (Kv_le_Gv (v : G) hk)

/-- The central line in the actual local moved module has order two. -/
theorem OrthogonalMarking.nonsingular_moved_fixed_card
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    Nat.card (ZV (Lv L (v : G)) (Vv L V (v : G))) = 2 := by
  obtain ⟨v₀,_,hne,_,he,_⟩ := D.nonsingular_moved_fixed_line chosen v hv
  rw [he,Nat.card_zpowers]
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v₀ : G) v₀.property)
    (fun h => hne (Subtype.ext h))

end CFSG.Quasithin.Chapter12.Section06
