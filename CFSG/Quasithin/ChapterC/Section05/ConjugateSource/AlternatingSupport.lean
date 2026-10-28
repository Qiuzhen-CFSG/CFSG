module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FixedPlane
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel

/-!
# Applying the transvection subgroup to the original alternating-five blocks

The intrinsic fixed kernel in an A₅ block module is trivial. Thus the
embedded module is disjoint from every group commuting with its block.
The preceding marked S-action gives its fixed plane order four. If R
permutes two commuting A₅ blocks, the transvection subgroup fixes the first
block and its characteristic module. Its invariance under the original
conjugator then gives normality of the right-conjugate module as well.

Only preceding C.5.3–4 block and marked-action data are used here. In
particular R is allowed to interchange the blocks. Source: Aschbacher–Smith,
C.5.6, printed p.157.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

/-- The original embedded block module, before taking any quotient. -/
def sourceModule (K : Subgroup G) : Subgroup G := (blockU K).map K.subtype

/-- The trivial fixed kernel gives disjointness from every commuting block. -/
theorem alternatingModule_disjoint_of_commuting
    (K L : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hcomm : L ≤ centralizer (K : Set G)) : Disjoint (sourceModule K) L := by
  apply disjoint_def.mpr
  intro u hu hL
  obtain ⟨v, hv, rfl⟩ := hu
  have hc : v ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hcomm hL k k.property)
  have hf : (⟨v, hv⟩ : blockU K) ∈ blockFixed K := hc
  rw [hK.blockFixed_eq_bot, mem_bot] at hf
  exact congrArg (fun z : blockU K => ((z : K) : G)) hf

/-- The actual two-block A₅ data force R⁺ to normalize both U₁ and U₁ˣ.
The marking is exactly the preceding C.5.4(3) action of S on the full U₁. -/
theorem alternating_transvection_normalizes_modules [Finite G]
    (R K₁ K₂ : Subgroup G) (hK : IsAlternatingBlock K₁ 5)
    (hcomm : K₂ ≤ centralizer (K₁ : Set G))
    (hUS : sourceModule K₁ ≤ ChapterB.baumann R)
    (hperm : ∀ r ∈ R, K₁.map (MulAut.conj r).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj r).toMonoidHom = K₂)
    (a : ChapterB.baumann R →* Equiv.Perm (Fin 5))
    (e : sourceModule K₁ ≃* Multiplicative (core (Fin 5)))
    (himage : a.range = ChapterB.Offenders.D 5)
    (he : ∀ (s : ChapterB.baumann R) (u : sourceModule K₁),
      (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 5) (a s) (e u).toAdd)) : G) =
        (s : G) * (u : G) * (s : G)⁻¹)
    (x : G) (hx : x ∈ normalizer (R : Set G)) :
    transvectionRadical R ≤ normalizer (K₁ : Set G) ∧
    transvectionRadical R ≤ normalizer (sourceModule K₁ : Set G) ∧
    transvectionRadical R ≤
      normalizer ((sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  have hU : IsElementaryAbelian 2 (sourceModule K₁) := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map K₁.subtype
  have hfixed := marked_fixed_plane_card (ChapterB.baumann R) (sourceModule K₁) a e himage he
  have hnorm := transvectionRadical_normalizes_first_block R K₁ K₂ (sourceModule K₁)
    hUS (map_subtype_le _) hU hfixed
    (alternatingModule_disjoint_of_commuting K₁ K₂ hK hcomm) hperm
  have hmod : transvectionRadical R ≤ normalizer (sourceModule K₁ : Set G) :=
    hnorm.trans (normalizer_le_normalizer_characteristic_image K₁ (blockU K₁))
  exact ⟨hnorm, hmod, transvectionRadical_normalizes_right_conjugate R _ x hx hmod⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
