module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.Sieve

/-!
# The rank-two seed in proper quotients

The paragraph preceding 13.8.22 uses generation by the H-translates of Ṽ₃
and irreducibility of its L₁-action. The restricted quotient map is a nonzero
intertwiner and therefore injective. Its range is the literal image V̂₃;
this identifies the two seeds equivariantly and preserves the rank two and
local invariance. Maximality of the denominator separately gives an
irreducible quotient of the original representation.

These results concern the actual subrepresentation and quotient; the source
application must identify the representation with Ũ_H and supply its earlier
generation and L₁-action identities. No dimension-one interpretation of the
word “line” is made.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21–24, printed pp.957–959, PDF pp.974–976 (1 March 2004 manuscript).
-/

@[expose] public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E) (L : Subgroup H)

/-- Generation by the actual translates of the seed. -/
def SeedGenerates (V : Submodule (ZMod 2) E) : Prop :=
  Submodule.span (ZMod 2) {w | ∃ g : H, ∃ v ∈ V, ρ g v = w} = ⊤

/-- The image of the seed in the literal quotient, with its restricted action. -/
def quotientSeed (W : Subrepresentation ρ) (V : Subrepresentation (ρ.comp L.subtype)) :
    Subrepresentation (W.quotientRepresentation.comp L.subtype) where
  toSubmodule := V.toSubmodule.map W.toSubmodule.mkQ
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, V.apply_mem_toSubmodule g hv, rfl⟩

/-- An irreducible generating seed meets every proper invariant denominator trivially. -/
theorem seed_quotient_injective
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule) :
    Function.Injective (W.toSubmodule.mkQ.domRestrict V.toSubmodule) := by
  let f : IntertwiningMap V.toRepresentation
      (W.quotientRepresentation.comp L.subtype) := {
    toLinearMap := W.toSubmodule.mkQ.domRestrict V.toSubmodule
    isIntertwining' g := by ext v; rfl }
  rcases IsIrreducible.injective_or_eq_zero f with hf | hf
  · exact hf
  · exfalso
    apply hW
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, v, hv, rfl⟩
    apply W.apply_mem_toSubmodule g
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    exact DFunLike.congr_fun hf ⟨v, hv⟩

/-- The quotient map gives an equivariant identification of the actual seeds. -/
noncomputable def seedQuotientEquiv
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule) :
    V.toSubmodule ≃ₗ[ZMod 2] (quotientSeed ρ L W V).toSubmodule := by
  let f : V.toSubmodule →ₗ[ZMod 2] (quotientSeed ρ L W V).toSubmodule :=
    { toFun := fun v => ⟨W.toSubmodule.mkQ v, ⟨v, v.property, rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  exact LinearEquiv.ofBijective f
    ⟨fun x y h => seed_quotient_injective ρ L W hW V hgen (congrArg Subtype.val h),
      fun ⟨q, v, hv, hq⟩ => ⟨⟨v, hv⟩, Subtype.ext hq⟩⟩

theorem seedQuotientEquiv_equivariant
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule) (g : L) (v : V.toSubmodule) :
    seedQuotientEquiv ρ L W hW V hgen (V.toRepresentation g v) =
      (quotientSeed ρ L W V).toRepresentation g
        (seedQuotientEquiv ρ L W hW V hgen v) := rfl

/-- In particular the source rank is two in the quotient as well. -/
theorem quotientSeed_finrank
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule)
    (hdim : Module.finrank (ZMod 2) V.toSubmodule = 2) :
    Module.finrank (ZMod 2) (quotientSeed ρ L W V).toSubmodule = 2 :=
  (seedQuotientEquiv ρ L W hW V hgen).finrank_eq.symm.trans hdim

/-- Invariance under the whole local subgroup survives in the actual image. -/
theorem quotientSeed_stable (W : Subrepresentation ρ)
    (V : Subrepresentation (ρ.comp L.subtype)) (P : Subgroup H)
    (hP : P ≤ subspaceStabilizer ρ V.toSubmodule) :
    P ≤ subspaceStabilizer W.quotientRepresentation (quotientSeed ρ L W V).toSubmodule := by
  apply le_subspaceStabilizer
  rintro g hg _ ⟨v, hv, rfl⟩
  exact ⟨ρ g v, (hP hg v).mpr hv, rfl⟩

/-- The local irreducible action survives on the seed image as well. -/
theorem quotientSeed_irreducible
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule) :
    IsIrreducible (quotientSeed ρ L W V).toRepresentation := by
  let e := seedQuotientEquiv ρ L W hW V hgen
  let : Nontrivial V.toSubmodule := Subrepresentation.irreducible_module_nontrivial V.toRepresentation
  let : Nontrivial (quotientSeed ρ L W V).toSubmodule := e.symm.toEquiv.nontrivial
  refine ⟨?_⟩
  intro S
  let R : Subrepresentation V.toRepresentation := {
    toSubmodule := S.toSubmodule.comap e.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change e (V.toRepresentation g v) ∈ S
      rw [seedQuotientEquiv_equivariant]
      exact S.apply_mem_toSubmodule g hv }
  rcases eq_bot_or_eq_top R with hR | hR
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro v hv
    obtain ⟨w, rfl⟩ := e.surjective v
    have hw : w ∈ R := hv
    rw [hR] at hw
    change e w = 0
    rw [show w = 0 from hw, map_zero]
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := e.surjective v
    exact (show w ∈ R from hR.symm ▸ Submodule.mem_top)

/-- Maximality gives irreducibility of this literal quotient representation. -/
theorem quotient_irreducible (W : Subrepresentation ρ) (hW : IsCoatom W) :
    W.quotientRepresentation.IsIrreducible := by
  have hn : W.toSubmodule ≠ ⊤ := fun he => hW.1 (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (E ⧸ W.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap W.toSubmodule.mkQ
    apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule g hv }
  have hWT : W ≤ T := by
    intro v hv
    change W.toSubmodule.mkQ v ∈ S
    have hz : W.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.toSubmodule.zero_mem
  rcases eq_or_lt_of_le hWT with he | hlt
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro q hq
    obtain ⟨v, rfl⟩ := W.toSubmodule.mkQ_surjective q
    exact (Submodule.Quotient.mk_eq_zero _).mpr (show v ∈ W from he.symm ▸ hq)
  · right
    have ht : T = ⊤ := hW.2 T hlt
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro q _
    obtain ⟨v, rfl⟩ := W.toSubmodule.mkQ_surjective q
    exact (show v ∈ T from ht.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from by trivial))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
