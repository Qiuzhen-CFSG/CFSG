module
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticLine
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Conjugation

/-!
# Quadratic normalization of the full Sylow fixed-cover seed

The natural fixed space of a full symplectic Sylow is one field line.
Quadraticity turns its setwise stabilization into pointwise fixation;
fixed-point lifting then fixes every vector of its central-cover preimage.
The embedded consumer proves literal subgroup centralization, with both
original action maps and the complete fixed central attachment retained.

Source: MS93 (3.4), first index-two contradiction, printed p.868.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
open Representation.OneCohomology
variable {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

theorem quadratic_fixes_normalized_sylow_cover_seed
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (P : Sylow 2 (L (K := F))) (A : Subgroup (L (K := F)))
    (hq : IsQuadratic (binaryNatural (K := F)) A)
    (hn : ∀ a ∈ A, ∀ w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype),
      σ a w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype)) :
    ∀ a ∈ A, ∀ w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype), σ a w = w := by
  obtain ⟨g,hg⟩ := SylowFlag.exists_marking P
  let N := SylowFlag.movedLine g
  have hdim : Module.finrank F N=1 := SylowFlag.movedLine_finrank g
  have hN : fixed ((binaryNatural (K := F)).comp (P : Subgroup (L (K := F))).subtype) =
      N.restrictScalars (ZMod 2) := by
    rw [hg]
    ext w
    change (∀ a : SylowFlag.movedSylow g, binaryNatural a.val w=w) ↔ w ∈ N
    exact SetLike.ext_iff.mp (SylowFlag.movedLine_fixed g) w
  have hNb : N ≠ ⊥ := by intro hh; rw [hh] at hdim; simp at hdim
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNb
  have hspan : N = F ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hv0
  have hline : ∀ a ∈ A, ∃ c : F, binaryNatural a v = c • v := by
    intro a ha
    obtain ⟨w,hw⟩ := hp.1 v
    have hwfix : w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype) := by
      rw [cover_fixed_preimage p hp,hN]
      change p w ∈ N
      rwa [hw]
    have hh := hn a ha w hwfix
    rw [cover_fixed_preimage p hp,hN] at hh
    change p (σ a w) ∈ N at hh
    rw [p.isIntertwining,hw,hspan] at hh
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
    exact ⟨c,hc.symm⟩
  have hfix : ∀ a ∈ A, ∀ c : F, binaryNatural a (c • v)=c • v := by
    intro a ha c
    have hlin (r : F) (w : Vector F) : binaryNatural a (r • w)=r • binaryNatural a w :=
      map_smul (symplecticDerivedNatural 2 a) r w
    obtain ⟨r,hr⟩ := hline a ha
    have hquadratic := hq a ha a ha v
    have hdisp : binaryNatural a v-v = (r-1) • v := by rw [hr,sub_smul,one_smul]
    rw [hdisp,hlin,hr] at hquadratic
    have hz : ((r-1)*(r-1)) • v=0 := by
      rw [mul_sub,mul_one,sub_smul,mul_smul,hquadratic,sub_self]
    have hr1 : r=1 := sub_eq_zero.mp (mul_self_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv0))
    rw [hlin,hr,hr1,one_smul]
  intro a ha w hw
  apply cover_fixed_of_projection_fixed p hp
  rw [cover_fixed_preimage p hp,hN] at hw
  change p w ∈ N at hw
  rw [hspan] at hw
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
  rw [←hc]
  exact hfix a ha c

end Representation.SymplecticFourOrthogonalCover

namespace Representation.SymplecticFourOrthogonalCover
open Representation.OneCohomology
variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]

theorem quadratic_centralizes_normalized_embedded_sylow_seed
    (U A T : Subgroup G) (j : Multiplicative W →* G)
    (hj : Function.Injective j) (hjU : j.range = U)
    (π : T →* L (K := F)) (P : Sylow 2 (L (K := F)))
    (himage : π.range = (P : Subgroup (L (K := F))))
    (β : A →* L (K := F))
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (hT : ∀ t : T, ∀ w : W, j (Multiplicative.ofAdd (σ (π t) w)) =
      (t:G)*j (Multiplicative.ofAdd w)*(t:G)⁻¹)
    (hA : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w)) =
      (a:G)*j (Multiplicative.ofAdd w)*(a:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hq : IsQuadratic (binaryNatural (K := F)) β.range)
    (hn : A ≤ normalizer ((U ⊓ centralizer (T : Set G) : Subgroup G) : Set G)) :
    A ≤ centralizer (U ⊓ centralizer (T : Set G) : Set G) := by
  have hfixed (w : W) :
      w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype) ↔
      j (Multiplicative.ofAdd w) ∈ U ⊓ centralizer (T : Set G) := by
    constructor
    · intro hw
      refine ⟨hjU ▸ ⟨_,rfl⟩,?_⟩
      intro t ht
      have hm : π ⟨t,ht⟩ ∈ (P : Subgroup (L (K := F))) := himage ▸ ⟨⟨t,ht⟩,rfl⟩
      have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) (hw ⟨π ⟨t,ht⟩,hm⟩)
      change j (Multiplicative.ofAdd (σ (π ⟨t,ht⟩) w)) = j (Multiplicative.ofAdd w) at hh
      rw [hT] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hw s
      obtain ⟨t,ht⟩ := (show (s : L (K := F)) ∈ π.range from himage.symm ▸ s.property)
      apply Multiplicative.ofAdd.injective
      apply hj
      change j (Multiplicative.ofAdd (σ s.val w))=j (Multiplicative.ofAdd w)
      rw [←ht,hT,hw.2 t t.property,mul_inv_cancel_right]
  have hnorm : ∀ a ∈ β.range, ∀ w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype),
      σ a w ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype) := by
    rintro _ ⟨a,rfl⟩ w hw
    apply (hfixed _).mpr
    rw [hA]
    exact (mem_normalizer_iff.mp (hn a.property) _).mp ((hfixed w).mp hw)
  have hfix := quadratic_fixes_normalized_sylow_cover_seed p hp P β.range hq hnorm
  intro a ha y hy
  obtain ⟨w,hw⟩ := (show y ∈ j.range from hjU.symm ▸ hy.1)
  have hwm : w.toAdd ∈ fixed (σ.comp (P : Subgroup (L (K := F))).subtype) := by
    apply (hfixed _).mpr
    change j w ∈ U ⊓ centralizer (T : Set G)
    rwa [hw]
  have hh := congrArg (fun v => j (Multiplicative.ofAdd v))
    (hfix (β ⟨a,ha⟩) ⟨⟨a,ha⟩,rfl⟩ w.toAdd hwm)
  rw [hA] at hh
  change a*j w*a⁻¹=j w at hh
  rw [hw] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end Representation.SymplecticFourOrthogonalCover
