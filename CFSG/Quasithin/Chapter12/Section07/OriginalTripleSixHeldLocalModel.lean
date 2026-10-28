module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldNormalizer

/-!
# The full original local action in the Held branch

The prescribed original K-action extends to the entire maximal two-local.
Its kernel is exactly O2(M)=U, and its image is the even triple cover or the
full hexacode group. The quotient isomorphism and the action equation retain
this kernel, the same original U, and the prescribed component marking.
Source: Aschbacher--Smith12.7.2(1) and12.7.7, printed pp.839 and841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal whole local quotient and its action in the original coordinates. -/
theorem original_tripleSix_held_local_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let M := normalizer (K : Set G)
    ∃ f : M →* HexAutomorphisms,
      f.ker = pCore 2 M ∧
      (f.range = hexSign.ker ∨ f.range = ⊤) ∧
      (∀ k : K, f (inclusion K.le_normalizer k) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (∀ (m : M) (u : U),
        ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
          (Hexacode.action (f m) (tripleSixPointCoordinates D a u).toAdd)) : G) =
          (m : G) * (u : G) * (m : G)⁻¹) ∧
      (Nonempty ((M ⧸ pCore 2 M) ≃* HexEvenAutomorphisms) ∨
        Nonempty ((M ⧸ pCore 2 M) ≃* HexAutomorphisms)) := by
  obtain ⟨_,_,hM,hN,hC⟩ := original_tripleSix_held_core_recovery
    h structural D a t ht heven hB hcenter e
  obtain ⟨f0,hf0,hk0,himage,hact⟩ := original_tripleSix_full_automizer h structural D a
  let M := normalizer (K : Set G)
  let N := normalizer (U : Set G)
  let en : M ≃* N := MulEquiv.subgroupCongr hN.symm
  let q : M →* Automizer U := U.normalizerMonoidHom.rangeRestrict.comp en.toMonoidHom
  have hq : Function.Surjective q :=
    U.normalizerMonoidHom.rangeRestrict_surjective.comp en.surjective
  let f := f0.comp q
  have hker : f.ker = pCore 2 M := by
    have he : pCore 2 M = U.subgroupOf M := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le (D.le_component.trans K.le_normalizer)]
      exact hM
    rw [he,MonoidHom.ker_comp_of_injective _ _ hf0]
    ext m
    change q m = 1 ↔ (m : G) ∈ U
    rw [show q m = U.normalizerMonoidHom.rangeRestrict (en m) from rfl,
      ←MonoidHom.mem_ker,MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker]
    change (m : G) ∈ centralizer (U : Set G) ↔ (m : G) ∈ U
    rw [hC]
  have hcontains : hexSign.ker ≤ f.range := by
    rw [←himage]
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨m,rfl⟩ := hq y
    exact ⟨m,rfl⟩
  have htwo : hexSign.ker.index = 2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hexSign_surjective,card_top]
    simp [Nat.card_eq_fintype_card]
  have hcases : f.range = hexSign.ker ∨ f.range = ⊤ := by
    have hd : f.range.index ∣ 2 := htwo ▸ index_dvd_of_le hcontains
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo'
    · exact Or.inr (index_eq_one.mp hone)
    · left
      have hi := relIndex_mul_index hcontains
      rw [htwo,htwo'] at hi
      have hone : hexSign.ker.relIndex f.range = 1 := by omega
      exact le_antisymm (relIndex_eq_one.mp hone) hcontains
  refine ⟨f,hker,hcases,?_,?_,?_⟩
  · intro k
    exact hk0 k
  · intro m u
    have hh := hact (q m) u
    have he : (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
        (Hexacode.action (f m) (tripleSixPointCoordinates D a u).toAdd)) =
        (q m).val u := by
      apply (tripleSixPointCoordinates D a).injective
      rw [(tripleSixPointCoordinates D a).apply_symm_apply]
      exact (congrArg Multiplicative.ofAdd hh).symm
    rw [he]
    rfl
  · let eqr : (M ⧸ pCore 2 M) ≃* f.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange f)
    rcases hcases with heven | hfull
    · exact Or.inl ⟨eqr.trans (MulEquiv.subgroupCongr heven)⟩
    · exact Or.inr ⟨eqr.trans ((MulEquiv.subgroupCongr hfull).trans (topEquiv))⟩

end CFSG.Quasithin.Chapter12.Section07
