module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianQuadraticSubspaces
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceRadicals
public import Theory.ElementaryAbelian.BinaryRankDifference
public import Theory.Representation.HermitianTensorThree.DualCoreSpan

/-!
# The paired-action step in Hermitian weak closure

Let A be the normalizer of V inside a conjugate Vᵍ. The reverse normalizer
acts quadratically on A. If A has corank less than n in Vᵍ, the transported
Hermitian quadratic bound limits the reverse induced actor to rank 2n+1.
The kernel centralizes A and has rank at most 4n. Thus a dual core of rank
at least 8n contradicts r >= 4n and w < n.

The printed H.4.5(2)/7.5.6 argument calls the displayed hyperplane
nonquadratic. A direct matrix calculation instead makes the plane radical
quadratic there. We use the reverse action and the root-space span bound.
After transporting that bound to the original automizer dual core, the last
theorem proves w >= n from the original weak-closure setup and r >= 4n.

Source: Aschbacher--Smith H.4.5, E.3.28--32 and 7.5.6,
printed pp.237--238,381,701 (refs/quasithin.pdf).
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem rank_eq_finrank (V : Subgroup G) [IsElementaryAbelian 2 V] :
    rank V = Module.finrank (ZMod 2) (Additive V) := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  change Nat.card V = _ at hc
  rw [rank,hc,Nat.card_zmod,Nat.log_pow Nat.one_lt_two]

/-- Quadraticity on a subgroup of corank less than n bounds the induced
Hermitian actor, including its actual centralizer kernel. -/
theorem actor_rank_le_of_quadratic_on_small_corank
    (V : Subgroup G) [IsElementaryAbelian 2 V] (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (V : Set G)) (hBV : B ≤ V)
    (hcor : subgroupCorank V B < n) (hq : ⁅⁅B,A⁆,A⁆ = ⊥) :
    rank (inducedAutomizer V A) ≤ 2*n+1 := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  let f := (inclusion hBV).toAdditive.toZModLinearMap 2
  have hf : Function.Injective f := inclusion_injective hBV
  let W := LinearMap.range f
  have hW : 8*n < Module.finrank (ZMod 2) W := by
    rw [LinearMap.finrank_range_of_inj hf, ← rank_eq_finrank]
    have hrank : rank V = 9*n := (rank_eq_finrank V).trans (e.finrank_eq.trans (finrank_binary n))
    have hc := log_card_sub_log_card_eq_log_relIndex V B hBV
    change rank V - rank B = subgroupCorank V B at hc
    omega
  let : IsElementaryAbelian 2 (inducedAutomizer V A) := inducedAutomizer_elementary V A hAN
  apply actor_rank_le_of_coordinates_on_large_subspace n (automizerRepresentation V)
    e j hj he (inducedAutomizer V A) W hW
  rintro a ⟨a₀,ha₀,rfl⟩ b ⟨b₀,hb₀,rfl⟩ _ ⟨v,rfl⟩
  have happ (x : normalizer (V : Set G)) (u : Additive V) :
      ((automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict x) u).toMul : G) =
        (x : G) * (u.toMul : G) * (x : G)⁻¹ := rfl
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [happ,toMul_sub,div_eq_mul_inv]
  change (a₀ : G) * ((b₀ : G) * (v.toMul : G) * (b₀ : G)⁻¹ * (v.toMul : G)⁻¹) *
    (a₀ : G)⁻¹ = (b₀ : G) * (v.toMul : G) * (b₀ : G)⁻¹ * (v.toMul : G)⁻¹
  have hc : ⁅(b₀ : G),(v.toMul : G)⁆ ∈ centralizer (A : Set G) := by
    apply (commutator_eq_bot_iff_le_centralizer.mp hq)
    rw [commutator_comm B A]
    exact commutator_mem_commutator hb₀ v.toMul.property
  have hh := hc (a₀ : G) ha₀
  simpa only [commutatorElement_def] using (mul_inv_eq_iff_eq_mul.mpr hh)

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- The same bound on the literal conjugate module, using the induced
automizer and module equivalences of ambient conjugation. -/
theorem actor_rank_le_on_conjugate_of_small_corank
    (V : Subgroup G) [IsElementaryAbelian 2 V] (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (g : G) (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hBV : B ≤ V.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B < n)
    (hq : ⁅⁅B,A⁆,A⁆ = ⊥) :
    rank (inducedAutomizer (V.map (MulAut.conj g).toMonoidHom) A) ≤ 2*n+1 := by
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let c := automizerModuleEquiv V (MulAut.conj g)
  let a := automizerMapEquiv V (MulAut.conj g)
  apply actor_rank_le_of_quadratic_on_small_corank _ n (c.symm.trans e)
    (j.comp a.symm.toMonoidHom) (hj.comp a.symm.injective) ?_ A B hAN hBV hcor hq
  intro x v
  have hc : c.symm (automizerRepresentation _ x v) =
      automizerRepresentation V (a.symm x) (c.symm v) := by
    apply c.injective
    rw [c.apply_symm_apply]
    have h := automizerRepresentation_equivariant V (MulAut.conj g) (a.symm x) (c.symm v)
    change c _ = automizerRepresentation _ (a (a.symm x)) (c (c.symm v)) at h
    rw [a.apply_symm_apply,c.apply_symm_apply] at h
    exact h.symm
  exact (congrArg e hc).trans (he (a.symm x) (c.symm v))

omit [Finite G] in
/-- The reverse normalizer acts quadratically on the original offender.
The two elementary ambient subgroups force the double commutator to vanish. -/
theorem reverse_normalizer_quadratic_on_offender
    (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G) :
    ⁅⁅offenderNormalizer V g,
        V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)⁆,
        V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hm : ⁅offenderNormalizer V g,
      V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)⁆ ≤ V :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp inf_le_right)
  exact hm.trans ((le_centralizer V).trans (centralizer_le inf_le_left))

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- The paired original actions contradict a large dual core below the
Hermitian weak-closure threshold. This replaces the nonquadratic-hyperplane
sentence in the printed H.4.5/7.5.6 argument. -/
theorem not_small_offender_of_large_dualCore
    (V : Subgroup G) [IsElementaryAbelian 2 V] (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (g : G) (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (hfix : rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) ≤ 4*n)
    (hspan : 8*n ≤ rank (automizerDualCore V
      (inducedAutomizer V (offenderNormalizer V g)) (3*n))) :
    n ≤ subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) := by
  by_contra! hsmall
  let Vg := V.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer V g
  change subgroupCorank Vg A < n at hsmall
  let U := automizerDualCore V (inducedAutomizer V A) (3*n)
  let : IsElementaryAbelian 2 Vg := IsElementaryAbelian.map _
  have hAV : A ≤ Vg := inf_le_left
  have hUV : U ≤ V := automizerDualCore_le V _ _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  have hUN : U ≤ V ⊓ normalizer (Vg : Set G) := by
    apply automizerDualCore_le_conjugate_normalizer
    apply lt_of_lt_of_le _ hr
    exact_mod_cast (show subgroupCorank Vg A + 3*n < 4*n by omega)
  have hq : ⁅⁅A,U⁆,U⁆ = ⊥ := by
    apply bot_unique
    apply (commutator_mono (commutator_mono le_rfl hUN) hUN).trans
    exact (reverse_normalizer_quadratic_on_offender V g).le
  have hu := actor_rank_le_on_conjugate_of_small_corank V n e j hj he g U A
    (hUN.trans inf_le_right) hAV hsmall hq
  let K := U ⊓ centralizer (Vg : Set G)
  have hK : K ≤ V ⊓ centralizer (A : Set G) :=
    le_inf (inf_le_left.trans hUV) (inf_le_right.trans (centralizer_le hAV))
  have hk : rank K ≤ 4*n := (Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hK) (inclusion_injective hK))).trans hfix
  have hrank := offender_corank_add (W := U) (A := K) bot_le inf_le_left
  have hi := rank_inducedAutomizer Vg U (hUN.trans inf_le_right)
  change _ = subgroupCorank U K at hi
  simp only [subgroupCorank,relIndex_bot_left] at hrank
  change rank U = subgroupCorank U K + rank K at hrank
  change 8*n ≤ rank U at hspan
  change rank (inducedAutomizer Vg U) ≤ 2*n+1 at hu
  have hn := NeZero.pos n
  omega

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- A hypothetical offender below n has dual core of rank less than 8n.
The fixed-space estimate and the reverse-action bound use the literal pair
of conjugate ambient modules. -/
theorem small_offender_dualCore_rank_lt
    (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G)
    (n : ℕ) [NeZero n] (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (g : G) (hOff : IsWOffenderAt V T g) (hw : globalW V T < n) :
    rank (automizerDualCore V (inducedAutomizer V (offenderNormalizer V g)) (3*n)) < 8*n := by
  have hsmall : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) < n := by exact_mod_cast (hOff.2 ▸ hw)
  have hir := hr.trans (lemma_E_3_28 hT h24 hOff).2.1.1
  rw [hOff.2, ← ENat.natCast_add] at hir
  have hir' : 4*n ≤ subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) + rank (inducedAutomizer V (offenderNormalizer V g)) :=
    by exact_mod_cast hir
  let A := offenderNormalizer V g
  let I := inducedAutomizer V A
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ V.map _ from inf_le_left)
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary V A inf_le_right
  let : IsElementaryAbelian 2 (I.map j) := IsElementaryAbelian.map j
  have hI : 3*n ≤ rank I := by dsimp only [I,A]; omega
  have hcod := LargeActors.overgroup_large_elementary_fixedCodim n
    (binaryNormalizer n) le_rfl (I.map j) (by rwa [rank_map_injective j hj])
  rw [← fixedCodim_map_equivariant (automizerRepresentation V)
    (overgroupAction n (binaryNormalizer n)) j e he I] at hcod
  change 5*n ≤ fixedCodim (automizerRepresentation V) (inducedAutomizer V A) at hcod
  rw [fixedCodim_inducedAutomizer V A inf_le_right] at hcod
  have hadd := offender_corank_add (W := V)
    (A := V ⊓ centralizer (A : Set G)) bot_le inf_le_left
  simp only [subgroupCorank,relIndex_bot_left] at hadd
  change rank V = subgroupCorank V (V ⊓ centralizer (A : Set G)) +
    rank (V ⊓ centralizer (A : Set G)) at hadd
  have hdim : rank V = 9*n := (rank_eq_finrank V).trans (e.finrank_eq.trans (finrank_binary n))
  have hfix : rank (V ⊓ centralizer (A : Set G)) ≤ 4*n := by omega
  by_contra! hspan
  exact (not_le_of_gt hsmall)
    (not_small_offender_of_large_dualCore V n e j hj he g hr hfix hspan)

/-- Only the geometric dual-core span remains in the weak-closure argument.
This is a conditional replacement for the printed nonquadratic-hyperplane step. -/
theorem globalW_ge_of_dualCore_span
    (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G)
    (n : ℕ) [NeZero n] (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (hspan : ∀ g : G, IsWOffenderAt V T g → globalW V T < n →
      8*n ≤ rank (automizerDualCore V
        (inducedAutomizer V (offenderNormalizer V g)) (3*n))) :
    (n : ℕ∞) ≤ globalW V T := by
  by_contra! hw
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top hT
    (ne_top_of_lt (hw.trans_le le_top))
  exact (not_le_of_gt (small_offender_dualCore_rank_lt V T n e j hj he hT h24 hr g hg hw))
    (hspan g hg hw)

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- The actual automizer dual core inherits the root-space span bound,
with its original actor quotient and ambient subgroup inclusion. -/
theorem automizerDualCore_rank_ge_of_inner
    (V : Subgroup G) [IsElementaryAbelian 2 V] (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (I : Subgroup (Automizer V)) [IsElementaryAbelian 2 I]
    (hI : I.map ((binaryNormalizer n).subtype.comp j) ≤ binaryImage n) :
    8*n ≤ rank (automizerDualCore V I (3*n)) := by
  let f := (binaryNormalizer n).subtype.comp j
  have hf : Function.Injective f := Subtype.val_injective.comp hj
  let : IsElementaryAbelian 2 (I.map f) := IsElementaryAbelian.map f
  let D := dualGeneratedCore ((Automizer V).subtype.comp I.subtype) (3*n)
  let W₀ : Submodule (ZMod 2) (Additive V) := AddSubgroup.toZModSubmodule 2 D.toAddSubgroup
  let W := W₀.map e.toLinearMap
  have hspan := DualCoreSpan.inner_fixed_span_rank_le n (I.map f) hI W (by
    intro R hR hr X hX
    let fi := f.comp I.subtype
    have hfi : Function.Injective fi := hf.comp Subtype.val_injective
    let S := R.comap fi
    have htop : (⊤ : Subgroup I).map fi = I.map f := by
      rw [←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
    have hm : S.map fi = R := by
      apply map_comap_eq_self
      rwa [MonoidHom.range_eq_map,htop]
    have hs : Nat.log 2 S.index ≤ 3*n := by
      have hidx : R.relIndex (I.map f) = S.index := by
        rw [←hm,←htop,relIndex_map_map_of_injective _ _ hfi,relIndex_top_right]
      rwa [hidx] at hr
    have hfix : (e.symm X).toMul ∈ actionCentralizer
        ((Automizer V).subtype.comp I.subtype) S := by
      intro a ha
      apply Additive.ofMul.injective
      apply e.injective
      have hx : (f a.val) X = X := hX ⟨fi a,ha⟩
      change e (automizerRepresentation V a.val (e.symm X)) = e (e.symm X)
      rw [he,e.apply_symm_apply]
      exact hx
    have hD : (e.symm X).toMul ∈ D :=
      actionCentralizer_le_dualGeneratedCore _ hs hfix
    exact ⟨e.symm X,hD,e.apply_symm_apply X⟩)
  have hd : Module.finrank (ZMod 2) W = rank (automizerDualCore V I (3*n)) := by
    rw [show W = W₀.map e.toLinearMap from rfl,e.finrank_map_eq]
    have hc : Nat.card W₀ = Nat.card D := Nat.card_congr
      { toFun := fun x => ⟨x.val.toMul,x.property⟩
        invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc' := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W₀)
    rw [Nat.card_zmod,hc] at hc'
    change _ = rank (D.map V.subtype)
    rw [rank_map_injective V.subtype Subtype.val_injective,rank,hc',Nat.log_pow Nat.one_lt_two]
  rwa [hd] at hspan

/-- The Hermitian weak-closure bound, with the geometric span premise
discharged on the original pair of conjugate ambient modules. -/
theorem globalW_ge_of_hermitian_coordinates
    (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G)
    (n : ℕ) [NeZero n] (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) :
    (n : ℕ∞) ≤ globalW V T := by
  apply globalW_ge_of_dualCore_span V T n e j hj he hT h24 hr
  intro g hOff hw
  have hsmall : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) < n := by exact_mod_cast (hOff.2 ▸ hw)
  have hir := hr.trans (lemma_E_3_28 hT h24 hOff).2.1.1
  rw [hOff.2, ← ENat.natCast_add] at hir
  have hir' : 4*n ≤ subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) + rank (inducedAutomizer V (offenderNormalizer V g)) :=
    by exact_mod_cast hir
  let A := offenderNormalizer V g
  let I := inducedAutomizer V A
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ V.map _ from inf_le_left)
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary V A inf_le_right
  let f := (binaryNormalizer n).subtype.comp j
  let : IsElementaryAbelian 2 (I.map f) := IsElementaryAbelian.map f
  have hf : Function.Injective f := Subtype.val_injective.comp hj
  have hI : 2*n+1 < rank (I.map f) := by
    rw [rank_map_injective f hf]
    dsimp only [I,A]
    have hn := NeZero.pos n
    omega
  apply automizerDualCore_rank_ge_of_inner V n e j hj he I
  exact large_elementary_le_image n (I.map f)
    (by rintro _ ⟨a,_,rfl⟩; exact (j a).property) hI

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
