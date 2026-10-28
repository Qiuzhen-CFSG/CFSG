module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticCoverFixed
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticImage

/-!
# Original-actor transport for the symplectic cover exclusion

An isomorphism of the original actor with the full symplectic group and an
intertwining linear equivalence retain the given action and natural-cover
projection. Over a nonbinary field the full symplectic group equals its derived
group. Reindexing through this proved equality gives the genuine derived
natural cover used by the orthogonal model.

The original Sylow and local subgroup map through the same actor isomorphism.
Local placement supplies the field-four point or plane case, while injectivity
identifies the literal two-cores. Reindexing leaves the original vector space,
its local commutator span and its global fixed space unchanged. The model
exclusion therefore applies to the original fully moved subspace.

Source: Aschbacher--Smith 9.4.1, printed p.735/PDF p.752 of
`refs/quasithin.pdf`, the natural Sp₄(4) cover branch. The inputs are the three
fields of an actual action equivalence, without importing Chapter B's source
case structure into Chapter A.
-/

public section

open Subgroup Theory.SpecificGroups.SymplecticFour
open Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {C F X W : Type*} [Group C] [Finite C]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) C X} {τ : Representation (ZMod 2) C W}

/-- A fully moved subspace fixed by the actual local core contains no global
fixed vector, after retaining the original actor and natural-cover map. -/
theorem symplectic_five_section_original_cover_moved_disjoint {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (eG : C ≃* Sp F) (eV : X ≃ₗ[ZMod 2] Natural (K := F))
    (he : ∀ c x, eV (σ c x) =
      restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2) (eG c) (eV x))
    (S : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (p : τ.IntertwiningMap σ) (hp : IsCover p)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace τ (B.pCoreIn 2))
    (hm : subspaceCommutator τ A B = A) : Disjoint A (fixed τ) := by
  have hgt : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n))
  have hder := Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hgt
  let a : C ≃* L (K := F) := {
    toFun c := ⟨eG c, by rw [hder]; trivial⟩
    invFun l := eG.symm l.val
    left_inv c := eG.symm_apply_apply c
    right_inv l := Subtype.ext (eG.apply_symm_apply l.val)
    map_mul' c d := Subtype.ext (eG.map_mul c d) }
  let α : Representation (ZMod 2) (L (K := F)) W := τ.comp a.symm.toMonoidHom
  let q : α.IntertwiningMap (binaryNatural (K := F)) :=
    (eV.toLinearMap.comp p.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro l w
      change eV (p (τ (eG.symm l.val) w)) =
        restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2) l.val (eV (p w))
      rw [p.isIntertwining, he, eG.apply_symm_apply])
  have hq : IsCover q := by
    refine ⟨eV.surjective.comp hp.1, ?_, ?_⟩
    · intro w hw l
      change eV (p w) = 0 at hw
      exact hp.2.1 (eV.map_eq_zero_iff.mp hw) (a.symm l)
    · apply top_unique
      rw [← hp.2.2]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨c,w⟩,rfl⟩
      have ha : α (a c) w = τ c w := by
        change τ (a.symm (a c)) w = τ c w
        rw [a.symm_apply_apply]
      change τ c w-w ∈ Coinvariants.ker α
      rw [← ha]
      exact Submodule.subset_span ⟨(a c,w),rfl⟩
  have hks : Group.IsSolvable eG.toMonoidHom.ker := by
    rw [eG.toMonoidHom.ker_eq_bot_iff.mpr eG.injective]
    infer_instance
  have hki : Function.Injective (eG.toMonoidHom.subgroupMap B) := by
    intro b c h
    apply Subtype.ext
    exact eG.injective (congrArg Subtype.val h)
  have hk : IsPGroup 2 (eG.toMonoidHom.subgroupMap B).ker := by
    rw [(eG.toMonoidHom.subgroupMap B).ker_eq_bot_iff.mpr hki]
    exact IsPGroup.of_subsingleton 2 _
  have hproper' : B.map eG.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    apply Subgroup.map_injective (f := eG.toMonoidHom) eG.injective
    rw [ht, map_top_of_surjective _ eG.surjective]
  obtain ⟨h4,g,hg⟩ := symplectic_five_section_image hF hn eG.toMonoidHom eG.surjective
    hks S B hB hk hproper' e
  have hmap : (B.map a.toMonoidHom).map (commutator (Sp F)).subtype =
      B.map eG.toMonoidHom := by
    rw [map_map]
    rfl
  have hA' : A ≤ fixedSpace α ((B.map a.toMonoidHom).pCoreIn 2) := by
    intro w hw ⟨b,hb⟩
    rw [← map_pCoreIn_of_injective 2 B _ a.injective] at hb
    obtain ⟨c,hc,rfl⟩ := hb
    change τ (a.symm (a c)) w = w
    rw [a.symm_apply_apply]
    exact hA hw ⟨c,hc⟩
  have hm' : subspaceCommutator α A (B.map a.toMonoidHom) = subspaceCommutator τ A B := by
    unfold subspaceCommutator
    congr 1
    ext v
    constructor
    · rintro ⟨_,⟨b,hb,rfl⟩,w,hw,rfl⟩
      refine ⟨b,hb,w,hw,?_⟩
      change τ (a.symm (a b)) w-w = τ b w-w
      rw [a.symm_apply_apply]
    · rintro ⟨b,hb,w,hw,rfl⟩
      refine ⟨a b,mem_map_of_mem a.toMonoidHom hb,w,hw,?_⟩
      change τ b w-w = τ (a.symm (a b)) w-w
      rw [a.symm_apply_apply]
  have hfixed : fixed α = fixed τ := by
    ext w
    constructor
    · intro hw c
      have hh := hw (a c)
      change τ (a.symm (a c)) w = w at hh
      simpa only [a.symm_apply_apply] using hh
    · intro hw l
      exact hw (a.symm l)
  have hd := ParabolicFixed.cover_moved_subspace_disjoint h4 q hq (B.map a.toMonoidHom)
    g (by simpa only [hmap] using hg) A hA' (hm'.trans hm)
  simpa only [hfixed] using hd
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
