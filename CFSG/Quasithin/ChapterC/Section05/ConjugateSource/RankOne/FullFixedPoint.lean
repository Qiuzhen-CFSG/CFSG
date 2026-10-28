module
public import Theory.Representation.SL2OrthogonalCover.FullFixed
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoverModel
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Stellmacher.OmegaOneCenterMap

/-!
# The full-Sylow fixed point in the original natural block

The intrinsic covering representation is the full elementary commutator layer
U(K), with its actual kernel C_U(K). Conjugation by the original normalizing
two-group descends to the marked natural plane. The induced automorphism of
K/O₂(K) gives the twisted SL₂ compatibility, so full-actor orthogonal-cover
lifting supplies a fixed vector outside that kernel. In the reduced C.5 setup,
U(K)≤Baumann(T)≤T turns it into the required Ω₁Z(T) seed.

The fixed-point statement only needs a normalizing two-group; in particular it
applies to the original Sylow of KT, with no extra splitting or geometry premise.
Source: Aschbacher–Smith I.2.3(2), printed p.413, and the first step of C.5.13,
printed p.162. The subsequent normal-closure argument belongs to C.5.13.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
open Subgroup Representation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
open IntrinsicCover
variable {G : Type*} [Group G] [Finite G] {K T : Subgroup G}

private def binaryAutAction {A B : Type*} [Group A] [Group B]
    [IsElementaryAbelian 2 B] (a : A →* MulAut B) :
    Representation (ZMod 2) A (Additive B) where
  toFun g := (a g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro w; change Additive.ofMul (a 1 w.toMul) = w; rw [map_one]; rfl
  map_mul' g h := by apply LinearMap.ext; intro w; change Additive.ofMul (a (g*h) w.toMul) = _; rw [map_mul]; rfl

private def naturalAutAction {A F : Type*} [Group A] [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (a : A →* MulAut (Multiplicative (Fin 2 → F))) :
    Representation (ZMod 2) A (Fin 2 → F) where
  toFun g := (show (Fin 2 → F) →+ (Fin 2 → F) from
    { toFun v := (a g (Multiplicative.ofAdd v)).toAdd
      map_zero' := congrArg Multiplicative.toAdd (a g).map_one
      map_add' v w := congrArg Multiplicative.toAdd ((a g).map_mul
        (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }).toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro w; change (a 1 (Multiplicative.ofAdd w)).toAdd = w; rw [map_one]; rfl
  map_mul' g h := by apply LinearMap.ext; intro w; change (a (g*h) (Multiplicative.ofAdd w)).toAdd = _; rw [map_mul]; rfl

/-- The original normalizing two-group fixes a point outside C_U(K). -/
theorem exists_natural_block_fixed_point {n : ℕ} (hn : IsL2EvenBlock K n)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G)) :
    ∃ u : U K, (u : G) ∈ centralizer (T : Set G) ∧
      (u : G) ∉ centralizer (K : Set G) := by
  obtain ⟨hn,hs,F,_,_,hF,_,α,⟨m⟩,hα⟩ := hn
  let := hs.elementary
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let π := SL2OrthogonalCover.binaryNatural (F := F)
  let σ := IntrinsicCover.action hs m
  let p := IntrinsicCover.projection hs m π hα
  have hp := IntrinsicCover.projection_isCover hs m π hα
  let c : T →* MulAut K := K.normalizerMonoidHom.comp (inclusion hTK)
  let b : T →* MulAut (blockU K) := (MulAut.characteristic (blockU K)).comp c
  let τ := binaryAutAction b
  let a : T →* MulAut (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (MulAut.congr m.quotientIso).toMonoidHom.comp ((quotientAut (pCore 2 K)).comp c)
  have ha (t : T) (k : K) : a t (actorMap m k) = actorMap m (c t k) := by
    change m.quotientIso (quotientAut (pCore 2 K) (c t)
      (m.quotientIso.symm (m.quotientIso (QuotientGroup.mk' _ k)))) = _
    rw [m.quotientIso.symm_apply_apply, quotientAut_apply_mk]
    rfl
  have hτ (t : T) (l : Matrix.SpecialLinearGroup (Fin 2) F)
      (w : Additive (blockU K)) : τ t (σ l w) = σ (a t l) (τ t w) := by
    obtain ⟨k,rfl⟩ := actorMap_surjective m l
    change τ t (IntrinsicCover.action hs m (actorMap m k) w) =
      IntrinsicCover.action hs m (a t (actorMap m k)) (τ t w)
    rw [ha, IntrinsicCover.action_apply, IntrinsicCover.action_apply]
    apply Additive.ofMul.injective
    apply Subtype.ext
    change c t (k * (w.toMul : K) * k⁻¹) =
      c t k * c t (w.toMul : K) * (c t k)⁻¹
    rw [map_mul, map_mul, map_inv]
  obtain ⟨β,hβ⟩ := exists_normalizer_quotient_action (modelProjection m)
    (modelProjection_surjective m) (modelProjection_kernel m)
  let η := naturalAutAction (β.comp (inclusion hTK))
  have hover (t : T) (w : Additive (blockU K)) : p (τ t w) = η t (p w) := by
    have he := hβ (inclusion hTK t) (intrinsicEquiv K w.toMul)
    have hc : normalizerConjugate (inclusion hTK t) (intrinsicEquiv K w.toMul) =
        intrinsicEquiv K (b t w.toMul) := by apply Subtype.ext; rfl
    rw [hc, modelProjection_intrinsic, modelProjection_intrinsic] at he
    exact (congrArg Multiplicative.toAdd he).symm
  have hη (t : T) (l : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      η t (SL2OrthogonalCover.natural l v) =
        SL2OrthogonalCover.natural (a t l) (η t v) := by
    obtain ⟨w,rfl⟩ := hp.1 v
    change η t (π l (p w)) = π (a t l) (η t (p w))
    rw [← p.isIntertwining, ← hover, hτ, p.isIntertwining, hover]
  obtain ⟨w,hw,hfix⟩ := SL2OrthogonalCover.FullFixed.exists_fixed_noncentral
    n hn hF σ p hp τ η a hτ hη hover hT
  refine ⟨intrinsicEquiv K w.toMul, ?_, ?_⟩
  · intro t ht
    have he := congrArg (fun z : Additive (blockU K) => ((z.toMul : K) : G)) (hfix ⟨t,ht⟩)
    change t * ((w.toMul : K) : G) * t⁻¹ = ((w.toMul : K) : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hc
    apply hw
    have he := (modelProjection_kernel m (intrinsicEquiv K w.toMul)).mpr hc
    rw [modelProjection_intrinsic] at he
    exact congrArg Multiplicative.toAdd he

/-- I.2.3(2) supplies the actual omega-center seed used at the start of C.5.13. -/
theorem Setup.natural_omegaCenter_not_le {E : Type*} [Field E]
    (h : Setup T K E) {n : ℕ} (hn : IsL2EvenBlock K n)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G)) :
    ¬ U K ⊓ Stellmacher.omegaOneCenterAmbient T ≤ centralizer (K : Set G) := by
  obtain ⟨u, huT, huK⟩ := exists_natural_block_fixed_point hn hT hTK
  let := h.elementary
  have huΩ : (u : G) ∈ Stellmacher.omegaOneCenterAmbient T := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff T u).mpr
    refine ⟨(h.module_le u.property).1, ?_, huT⟩
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property
  exact fun hc => huK (hc ⟨u.property, huΩ⟩)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
