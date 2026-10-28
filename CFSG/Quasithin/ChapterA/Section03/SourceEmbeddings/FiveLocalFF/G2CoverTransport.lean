module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2Image
public import Theory.Representation.G2OrthogonalCover.ParabolicFixed

/-!
# The original G₂ natural-cover action at a local A₅ section

The actual actor isomorphism and natural-module coordinates transport a given
central cover to the full G₂ model. Its original full Sylow and proper local
C-component determine a conjugate parabolic residual. Injectivity identifies
the exact two-cores, while the original moved subspace and fixed vectors are
unchanged by reindexing the actor.

The concrete Cayley-cover calculation therefore excludes a globally fixed
vector in every fully moved subspace centralized by that local two-core.
The cover projection is retained throughout, including its central kernel.

Source: Aschbacher--Smith, 9.4.1, printed p.735/PDF p.752 of the combined
1 March 2004 manuscript, the natural G₂(4) cover branch.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.Natural
open Representation Representation.OneCohomology Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
variable {C F X W : Type*} [Group C] [Finite C]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) C X} {τ : Representation (ZMod 2) C W}

/-- The literal original cover and local A₅ section exclude every globally
fixed vector from a fully moved subspace fixed by the local two-core. -/
theorem five_section_original_cover_moved_disjoint {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (eG : C ≃* Model F) (eV : X ≃ₗ[ZMod 2] Space F)
    (he : ∀ c x, eV (σ c x) =
      restrictScalars (k := ZMod 2) (g2Natural F) (eG c) (eV x))
    (S : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (p : τ.IntertwiningMap σ) (hp : IsCover p)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace τ (B.pCoreIn 2))
    (hm : subspaceCommutator τ A B = A) : Disjoint A (fixed τ) := by
  have hgt : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n))
  let α : Representation (ZMod 2) (Model F) W := τ.comp eG.symm.toMonoidHom
  let q : α.IntertwiningMap (OrthogonalCover.ParabolicFixed.fullBinaryNatural F) :=
    (eV.toLinearMap.comp p.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro l w
      change eV (p (τ (eG.symm l) w)) =
        restrictScalars (k := ZMod 2) (g2Natural F) l (eV (p w))
      rw [p.isIntertwining, he, eG.apply_symm_apply])
  have hq : IsCover q := by
    refine ⟨eV.surjective.comp hp.1, ?_, ?_⟩
    · intro w hw l
      change eV (p w) = 0 at hw
      exact hp.2.1 (eV.map_eq_zero_iff.mp hw) (eG.symm l)
    · apply top_unique
      rw [← hp.2.2]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨c,w⟩,rfl⟩
      have ha : α (eG c) w = τ c w := by
        change τ (eG.symm (eG c)) w = τ c w
        rw [eG.symm_apply_apply]
      change τ c w-w ∈ Coinvariants.ker α
      rw [← ha]
      exact Submodule.subset_span ⟨(eG c,w),rfl⟩
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
  obtain ⟨_,g,hg⟩ := five_section_image hgt eG.toMonoidHom eG.surjective
    hks S B hB hk hproper' e
  have hA' : A ≤ fixedSpace α ((B.map eG.toMonoidHom).pCoreIn 2) := by
    intro w hw ⟨b,hb⟩
    rw [← map_pCoreIn_of_injective 2 B _ eG.injective] at hb
    obtain ⟨c,hc,rfl⟩ := hb
    change τ (eG.symm (eG c)) w = w
    rw [eG.symm_apply_apply]
    exact hA hw ⟨c,hc⟩
  have hm' : subspaceCommutator α A (B.map eG.toMonoidHom) = subspaceCommutator τ A B := by
    unfold subspaceCommutator
    congr 1
    ext v
    constructor
    · rintro ⟨_,⟨b,hb,rfl⟩,w,hw,rfl⟩
      refine ⟨b,hb,w,hw,?_⟩
      change τ (eG.symm (eG b)) w-w = τ b w-w
      rw [eG.symm_apply_apply]
    · rintro ⟨b,hb,w,hw,rfl⟩
      refine ⟨eG b,mem_map_of_mem _ hb,w,hw,?_⟩
      change τ b w-w = τ (eG.symm (eG b)) w-w
      rw [eG.symm_apply_apply]
  have hd := OrthogonalCover.ParabolicFixed.cover_moved_subspace_disjoint
    F q hgt hq (B.map eG.toMonoidHom) g hg A hA' (hm'.trans hm)
  apply Submodule.disjoint_def.mpr
  intro w hw hf
  exact Submodule.disjoint_def.mp hd w hw (fun g => hf (eG.symm g))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
