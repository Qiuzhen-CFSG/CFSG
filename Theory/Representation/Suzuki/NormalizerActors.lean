module
public import Theory.Representation.Suzuki.ExchangedActor
public import Theory.Representation.BinaryOffender.InnerInvolutions

/-!
# Small elementary actors on a Suzuki square

A factor-preserving involution in the full linear normalizer of a faithful
irreducible Suzuki square acts by inner automorphisms on both factors.
Schur's lemma then places the involution in the literal linear image.

For a factor exchange with an automorphism twist, changing the marking of
one factor makes it the literal interchange. This leaves the vector space,
operators, fixed codimension and elementary rank unchanged. The checked
exchange estimate then excludes every small elementary actor containing
such an element. Consequently every small elementary normalizer actor is
contained in the original square image. No restriction on the full normalizer
quotient is assumed.

Source: Aschbacher--Smith D.3.7, printed pp.197--199; the final Chapter 10
application uses this with the original nonseparated seed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.Suzuki
open BenderSuzuki.MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A factor-preserving normalizer involution belongs to the actual square image. -/
theorem binary_square_preserving_involution_mem (m : ℕ) (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (a : linearNormalizer ρ) (h2 : a ^ 2 = 1)
    (hpres : a.val ∈ normalizer
      (((⊤ : Subgroup (SuzukiMatrixGroup m)).prod ⊥).map ρ.asGroupHom : Set _)) :
    a.val ∈ actionImage ρ := by
  let S := SuzukiMatrixGroup m
  let : Fact (0 < m) := ⟨hm⟩
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  have hconj (g : S × S) :
      (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  have hdiag : ∃ α β : MulAut S, f a = α.prodCongr β := by
    rcases AutomorphismSquare.normal_form hZ (f a) with h | ⟨α,β,h⟩
    · exact h
    · obtain ⟨x,hx⟩ := exists_ne (1 : S)
      have hg : (e (f a (x,1))).val ∈
          ((⊤ : Subgroup S).prod ⊥).map ρ.asGroupHom := by
        rw [hconj]
        exact (mem_normalizer_iff.mp hpres _).mp ⟨(x,1),⟨mem_top _,rfl⟩,rfl⟩
      obtain ⟨y,hy,he⟩ := hg
      have hxy : y = f a (x,1) := e.injective (Subtype.ext he)
      have hb : β x = 1 := by
        have hh := mem_bot.mp hy.2
        rw [hxy,h] at hh
        exact hh
      exact (hx (β.injective (hb.trans β.map_one.symm))).elim
  obtain ⟨α,β,hdiag⟩ := hdiag
  have hp : (f a) ^ 2 = 1 := by rw [←map_pow,h2,map_one]
  have hα : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun (hdiag ▸ hp) (x,1))
  have hβ : β ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun (hdiag ▸ hp) (1,x))
  obtain ⟨x,hx,_⟩ := BenderSuzuki.ZD.suzuki_involutoryAut_inner_and_twoRank m hm α hα
  obtain ⟨y,hy,_⟩ := BenderSuzuki.ZD.suzuki_involutoryAut_inner_and_twoRank m hm β hβ
  have hfinner : f a = MulAut.conj (x,y) := by rw [hdiag,hx,hy]; rfl
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  let : IsIrreducible (τ.comp (actionImage ρ).subtype) := imageRepresentation_isIrreducible ρ hi
  exact involution_mem_of_inner τ (actionImage ρ) (fun _ _ h => Units.ext h) a
    (congrArg Subtype.val h2) ⟨e (x,y),by
      apply MulEquiv.ext
      intro z
      obtain ⟨g,rfl⟩ := e.surjective z
      have hh : e (f a g) = (actionImage ρ).normalizerMonoidHom a (e g) :=
        e.apply_symm_apply _
      rw [hfinner] at hh
      exact hh.symm.trans (by simp only [MulAut.conj_apply,map_mul,map_inv])⟩

/-- Factor preservation places an elementary actor in the actual square image. -/
theorem binary_square_preserving_actor_le (m : ℕ) (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (hpres : ∀ a ∈ A, a.val ∈ normalizer
      (((⊤ : Subgroup (SuzukiMatrixGroup m)).prod ⊥).map ρ.asGroupHom : Set _)) :
    A ≤ (actionImage ρ).subgroupOf (linearNormalizer ρ) := by
  intro a ha
  exact binary_square_preserving_involution_mem m hm ρ hi hf a
    (elemPow_eq_one_of_isElementaryAbelian a ha) (hpres a ha)
end Representation.Suzuki

namespace Representation.Suzuki
open BenderSuzuki.MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The exchange exclusion is unchanged by a twist of the factor marking. -/
theorem binary_square_twisted_exchange_strict_bound (m : ℕ) (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A) (α : MulAut (SuzukiMatrixGroup m))
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v)) :
    2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  let δ := α.prodCongr (MulEquiv.refl (SuzukiMatrixGroup m))
  let σ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V :=
    ρ.comp δ.toMonoidHom
  have himage : actionImage σ = actionImage ρ := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨δ g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := δ.surjective g
      exact ⟨g,Units.ext rfl⟩
  have hn : linearNormalizer ρ ≤ linearNormalizer σ := by
    unfold linearNormalizer
    rw [himage]
  let j := inclusion hn
  have hj : Function.Injective j := inclusion_injective hn
  let C := A.map j
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map j
  have hiσ : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff δ.toMonoidHom δ.surjective ρ).mpr hi
  have hfσ : Function.Injective σ := hf.comp δ.injective
  have hs : ∀ g v, normalizerRepresentation σ (j a) (σ g v) =
      σ (g.2,g.1) (normalizerRepresentation σ (j a) v) := by
    rintro ⟨x,y⟩ v
    have hh := hswap (α x,y) v
    change normalizerRepresentation ρ a (ρ (α x,y) v) =
      ρ (α y,x) (normalizerRepresentation ρ a v)
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hb := binary_square_exchanged_actor_strict_bound m hm σ hiσ hfσ C (j a)
    (mem_map_of_mem j ha) hs
  have hcod : fixedCodim (normalizerRepresentation σ) C =
      fixedCodim (normalizerRepresentation ρ) A :=
    (fixedCodim_map_equivariant (normalizerRepresentation ρ) (normalizerRepresentation σ)
      j (LinearEquiv.refl _ _) (fun _ _ => rfl) A).symm
  rw [hcod,show rank C = rank A from rank_map_injective j hj A] at hb
  exact hb
end Representation.Suzuki

namespace Representation.Suzuki
open BenderSuzuki.MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every elementary actor of ratio at most two lies in the actual square image. -/
theorem binary_square_small_actor_le_image (m : ℕ) (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (normalizerRepresentation ρ) A ≤ 2 * rank A) :
    A ≤ (actionImage ρ).subgroupOf (linearNormalizer ρ) := by
  let S := SuzukiMatrixGroup m
  let : Fact (0 < m) := ⟨hm⟩
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  intro a ha
  have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hconj (g : S × S) :
      (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply _)
  rcases AutomorphismSquare.normal_form hZ (f a) with ⟨α,β,hdiag⟩ | ⟨α,β,hswap⟩
  · apply binary_square_preserving_involution_mem m hm ρ hi hf a h2
    let J := ((⊤ : Subgroup S).prod ⊥).map ρ.asGroupHom
    have hJ : J ≤ actionImage ρ := by rintro _ ⟨g,_,rfl⟩; exact ⟨g,rfl⟩
    have hmem (g : S × S) : (e g).val ∈ J ↔ g.2 = 1 := by
      constructor
      · rintro ⟨k,hk,hkg⟩
        have he : k = g := e.injective (Subtype.ext hkg)
        exact he ▸ mem_bot.mp hk.2
      · intro hg
        exact ⟨g,⟨mem_top _,hg⟩,rfl⟩
    apply mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      obtain ⟨g,rfl⟩ := hJ hz
      change (e g).val ∈ J at hz
      change a.val * (e g).val * a.val⁻¹ ∈ J
      rw [←hconj,hdiag]
      apply (hmem _).mpr
      change β g.2 = 1
      rw [(hmem g).mp hz,β.map_one]
    · intro hz
      have hz' : z ∈ actionImage ρ := (mem_normalizer_iff.mp a.property z).mpr (hJ hz)
      obtain ⟨g,rfl⟩ := hz'
      change a.val * (e g).val * a.val⁻¹ ∈ J at hz
      rw [←hconj,hdiag] at hz
      apply (hmem g).mpr
      exact β.injective (((hmem _).mp hz).trans β.map_one.symm)
  · have hp : (f a) ^ 2 = 1 := by rw [←map_pow,h2,map_one]
    have hba (x : S) : β (α x) = x :=
      congrArg Prod.snd (DFunLike.congr_fun (hswap ▸ hp) (1,x))
    have hβ : β = α.symm := by
      apply MulEquiv.ext
      intro x
      obtain ⟨x,rfl⟩ := α.surjective x
      exact (hba x).trans (α.symm_apply_apply x).symm
    have hex : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
        ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v) := by
      intro g v
      have hh := congrArg (fun x : (Module.End (ZMod 2) V)ˣ => x.val
        (normalizerRepresentation ρ a v)) (hconj g).symm
      rw [hswap,hβ] at hh
      change a.val.val (ρ g ((a.val⁻¹).val (a.val.val v))) =
        ρ (α g.2,α.symm g.1) (a.val.val v) at hh
      have hv : (a.val⁻¹).val (a.val.val v) = v := by
        change ((a.val⁻¹).val * a.val.val) v = v
        rw [←Units.val_mul,inv_mul_cancel,Units.val_one]
        rfl
      rwa [hv] at hh
    exact ((not_lt_of_ge hsmall)
      (binary_square_twisted_exchange_strict_bound m hm ρ hi hf A a ha α hex)).elim
end Representation.Suzuki
