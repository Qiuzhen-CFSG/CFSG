module
public import Theory.LinearAlgebra.QuadraticForm.BinarySixExtensions
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.WeakClosureZero
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Singular extensions on the original conjugate six-spaces

The polar-space theorem bounds the number of singular three-spaces above
an actual two-space by two. Linear ranges of subgroup inclusions transport
literal coranks to dimensions. The original orthogonal marking and
conjugation then give this bound on each unchanged conjugate Vᵍ.

The final theorem combines it with12.6.27, corank-two centralizer control,
the proved A₃ exclusion and nonsingular-point control. Thus the remaining
input to W₁ centralizing V is precisely the A₂ three-extension calculation
on the original actor. This input is explicit; no unconditional W₁ bound
or universal NaturalReduction is asserted here.

Source: Aschbacher--Smith,12.6.28(4), printed p.835, and E.3.34.
-/

public section
open Subgroup Module BinaryPermutation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

/-- Pull the polar two-extension bound through literal subgroup inclusions
and full six-space coordinates. Relative coranks are measured in W. -/
theorem not_three_singular_extensions (W : Subgroup G) [IsElementaryAbelian 2 W]
    (e : Additive W ≃ₗ[ZMod 2] natural (Fin 8))
    (D : Subgroup G) (hDW : D ≤ W) (hD : ChapterE.subgroupCorank W D = 4)
    (E : Fin 3 → Subgroup G)
    (hE : ∀ i, D ≤ E i ∧ E i ≤ W ∧ ChapterE.subgroupCorank W (E i) = 3 ∧
      ∀ x : W, x.val ∈ E i → TerminalOrthogonal.Eight.form (e (Additive.ofMul x)) = 0) :
    ¬ Function.Injective E := by
  classical
  let (B : Subgroup G) : IsElementaryAbelian 2 (B.subgroupOf W) :=
    IsElementaryAbelian.of_injective (B.subgroupOf W).subtype Subtype.val_injective
  let f (B : Subgroup G) : Additive (B.subgroupOf W) →ₗ[ZMod 2] natural (Fin 8) :=
    e.toLinearMap.comp ((B.subgroupOf W).subtype.toAdditive.toZModLinearMap 2)
  let U (B : Subgroup G) := (f B).range
  have fi (B : Subgroup G) : Function.Injective (f B) := by
    intro x y h
    apply Additive.ofMul.injective
    apply Subtype.ext
    exact e.injective h
  have uc (B : Subgroup G) (hBW : B ≤ W) : Nat.card (U B) = Nat.card B := by
    rw [Nat.card_congr (LinearEquiv.ofInjective (f B) (fi B)).toEquiv.symm]
    change Nat.card (B.subgroupOf W) = Nat.card B
    exact Nat.card_congr (subgroupOfEquivOfLe hBW).toEquiv
  have uw (B : Subgroup G) (w : W) :
      e (Additive.ofMul w) ∈ U B ↔ w.val ∈ B := by
    constructor
    · rintro ⟨b,hb⟩
      have hh := e.injective hb
      change b.toMul.val = w at hh
      exact hh ▸ b.toMul.property
    · intro hw
      exact ⟨Additive.ofMul ⟨w,hw⟩,rfl⟩
  have um {B C : Subgroup G} (hBC : B ≤ C) : U B ≤ U C := by
    intro w hw
    obtain ⟨v,rfl⟩ := e.surjective w
    exact (uw C v.toMul).mpr (hBC ((uw B v.toMul).mp hw))
  have ui {B C : Subgroup G} (hBW : B ≤ W) (hCW : C ≤ W) (h : U B = U C) : B = C := by
    apply le_antisymm
    · intro b hb
      exact (uw C ⟨b,hBW hb⟩).mp (h ▸ (uw B ⟨b,hBW hb⟩).mpr hb)
    · intro c hc
      exact (uw B ⟨c,hCW hc⟩).mp (h.symm ▸ (uw C ⟨c,hCW hc⟩).mpr hc)
  have wc : Nat.card W = 64 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [e.finrank_eq,TerminalOrthogonal.Eight.finrank_natural,Nat.card_zmod] at hh
    exact hh
  have dim (B : Subgroup G) (hBW : B ≤ W) (k : ℕ)
      (hk : ChapterE.subgroupCorank W B = k) :
      2 ^ k * 2 ^ finrank (ZMod 2) (U B) = 64 := by
    have hi : B.relIndex W = 2 ^ k := by
      rw [Subgroup.relIndex_eq_two_pow_quotient_finrank]
      rw [ChapterE.subgroupCorank_eq_quotient_finrank] at hk
      rw [hk]
    have hh := relIndex_mul_card_of_le hBW
    rw [hi,wc,←uc B hBW,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact hh
  have ud : finrank (ZMod 2) (U D) = 2 := by
    have hh := dim D hDW 4 hD
    have he : 2^(4+finrank (ZMod 2) (U D)) = 2^6 := by simpa only [pow_add, Nat.reducePow] using hh
    have ht := Nat.pow_right_injective (by decide : 2 ≤ 2) he
    omega
  have ue (i : Fin 3) : finrank (ZMod 2) (U (E i)) = 3 := by
    have hh := dim (E i) (hE i).2.1 3 (hE i).2.2.1
    have he : 2^(3+finrank (ZMod 2) (U (E i))) = 2^6 := by simpa only [pow_add, Nat.reducePow] using hh
    have ht := Nat.pow_right_injective (by decide : 2 ≤ 2) he
    omega
  intro hinj
  apply EightSingularExtensions.not_three TerminalOrthogonal.Eight.form EightGeometry.polar_nondegenerate
    TerminalOrthogonal.Eight.finrank_natural (U D) ud (fun i => U (E i)) _ _
  · intro i
    refine ⟨um (hE i).1,ue i,?_⟩
    intro w hw
    obtain ⟨v,rfl⟩ := e.surjective w
    exact (hE i).2.2.2 v.toMul ((uw (E i) v.toMul).mp hw)
  · intro i j h
    exact hinj (ui (hE i).2.1 (hE j).2.1 h)


/-- The same two-extension bound on each actual conjugate Vᵍ, using the
original orthogonal marking to test singularity before conjugation. -/
theorem OrthogonalMarking.original_not_three_singular_extensions
    {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    (hZ : ZV L V = ⊥) (g : G) (D₀ : Subgroup G)
    (hDW : D₀ ≤ V.map (MulAut.conj g).toMonoidHom)
    (hD : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) D₀ = 4)
    (E : Fin 3 → Subgroup G)
    (hE : ∀ i, D₀ ≤ E i ∧ E i ≤ V.map (MulAut.conj g).toMonoidHom ∧
      ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (E i) = 3 ∧
      ∀ v : V, MulAut.conj g v.val ∈ E i → ¬ D.Nonsingular v) :
    ¬ Function.Injective E := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let c : V ≃* W := V.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let a : Additive W ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofBijective
    (c.symm.toMonoidHom.toAdditive.toZModLinearMap 2) c.symm.toAdditive.bijective
  let e := a.trans (D.fullLinearCoordinates hZ)
  apply not_three_singular_extensions W e D₀ hDW hD E
  intro i
  refine ⟨(hE i).1,(hE i).2.1,(hE i).2.2.1,?_⟩
  intro w hw
  obtain ⟨v,rfl⟩ := c.surjective w
  have hs := (hE i).2.2.2 v hw
  have he : e (Additive.ofMul (c v)) = D.fullLinearCoordinates hZ (Additive.ofMul v) := by
    change D.fullLinearCoordinates hZ (Additive.ofMul (c.symm (c v))) = _
    rw [c.symm_apply_apply]
  rw [he,D.fullLinearCoordinates_apply]
  exact not_ne_iff.mp hs


variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)

include hz hTV hTz hbound hTI hns in
/-- All source geometry needed for W₁, with only the original-actor A₂
three-extension calculation retained explicitly. The polar-space input is
proved here on the actual conjugate module, rather than assumed. -/
theorem SourceHypothesis.original_weakClosure_one_of_three_extensions
    (hthree : ∀ A : Subgroup G, A ≤ normalizer (V : Set G) →
      IsElementaryAbelian 2 A → ¬ A ≤ centralizer (V : Set G) →
      LocalAlternatives.CentralizerRigidity V A 2 →
      ∃ D₀ ≤ A, ChapterE.subgroupCorank A D₀ = 3 ∧
        ∃ E : Fin 3 → Subgroup G, Function.Injective E ∧
          ∀ i, D₀ ≤ E i ∧ E i ≤ A ∧ ChapterE.subgroupCorank (E i) D₀ = 1 ∧
            V ⊓ centralizer (A : Set G) < V ⊓ centralizer (E i : Set G)) :
    ChapterE.indexedWeakClosure V T 1 ≤ centralizer (V : Set G) ∧
      1 < ChapterE.globalW V T := by
  have hR := (S.fixed_free_intersections_of_control D hTV hTI hZ hns).2
  let singular (g : G) (E : Subgroup G) : Prop :=
    ∀ v : V, MulAut.conj g v.val ∈ E → ¬ D.Nonsingular v
  have hsmall (g : G) (A : Subgroup G) (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
      (hAT : A ≤ T) (hcor : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1) :
      A ≤ centralizer (V : Set G) := by
    apply LocalAlternatives.small_corank_conjugate_centralizes V T hTV singular
      ?_ ?_ ?_ hthree ?_ ?_ g A hAW hAT hcor
    · intro x hcomm
      by_contra hi
      exact hcomm (S.original_intersecting_conjugates_commute D hZ z hz hTV hTz hbound hTI hns x hi)
    · intro x B hBW hB
      apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hBW
      rw [ChapterE.globalR_map_equiv]
      exact lt_of_lt_of_le (by exact_mod_cast hB) hR
    · intro B hBN hB hr
      let : IsElementaryAbelian 2 B := hB
      exact S.original_no_three_rigidity D hZ hTV B hBN hr
    · intro x E hEW hE hescape v hv hnsV
      apply hescape
      have hc : Gv v.val ≤ normalizer (V : Set G) :=
        (le_inf (hns v hnsV) le_rfl).trans
          (Mv_le_module_normalizer_of_TI hTI v (nonsingular_ne_one D hnsV))
      have hm := map_mono (f := (MulAut.conj x).toMonoidHom) hc
      rw [Gv,map_centralizer_equiv,Set.image_singleton,map_equiv_normalizer_eq] at hm
      exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)).trans hm
    · intro x D₀ hDW hD₀ E hEs
      exact D.original_not_three_singular_extensions hZ x D₀ hDW hD₀ E hEs
  exact (LocalAlternatives.weak_closures_and_globalW_of_small_corank V T hsmall).2

end CFSG.Quasithin.Chapter12.Section06
