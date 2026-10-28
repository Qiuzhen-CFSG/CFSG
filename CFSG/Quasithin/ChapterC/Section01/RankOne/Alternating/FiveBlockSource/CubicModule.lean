module
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.Single
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Source
/-!
# The actual natural support of the selected cubic

Solvable FF classification gives a natural SL₂(2) factor. If the faithful
actor has six elements, that factor is the whole actor, so the residual
moves a binary plane. The resulting natural quotient and its fixed kernel
are constructed on the original module and transported through its literal
centralizer quotient. B.6.10 then supplies Baumann Sylow and alpha splitting.
Source: Aschbacher–Smith C.1.21(4), C.1.23(1), printed pp.129–130.
-/
public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

theorem cubic_ff_moved_finrank (ρ : Representation (ZMod 2) D W)
    (hfaith : Function.Injective ρ) (hsolv : Group.IsSolvable D)
    (hcore : pCore 2 D = ⊥) (hcard : Nat.card D = 6) (hff : IsFFModule ρ) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (pResidual 2 D)) = 2 := by
  obtain ⟨d⟩ := ChapterB.solvableFFStructure_nonempty ρ hsolv hcore hfaith hff
  let a := d.toSolvableFFFactors
  let i : Fin a.count := ⟨0,a.count_pos⟩
  have hi : Nat.card (a.factor i) = 6 := by
    rw [Nat.card_congr (a.factorModel i).toEquiv]
    exact ChapterB.Glauberman.BlockConstruction.PairRecognition.sl_card
  have he : a.factor i = ⊤ := eq_top_of_card_eq _ (hi.trans hcard.symm)
  have ho : offenderSubgroup ρ = ⊤ := top_unique (he ▸ a.factor_le_offenderSubgroup i)
  have hr : pResidual 2 D ≤ offenderSubgroup ρ := ho ▸ le_top
  rw [a.residual_moved_eq hfaith hr,ho,←he]
  exact a.support_finrank i

/-- The original solvable six-element action determines the whole binary natural
quotient, including its exact residual-fixed kernel. -/
theorem cubic_ff_natural_quotient (ρ : Representation (ZMod 2) D W)
    (hfaith : Function.Injective ρ) (hsolv : Group.IsSolvable D)
    (hcore : pCore 2 D = ⊥) (hcard : Nat.card D = 6) (hff : IsFFModule ρ) :
    ∃ (a : D ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (f : W →ₗ[ZMod 2] (Fin 2 → ZMod 2)), Function.Surjective f ∧
      (∀ g v, f (ρ g v) = (a g).val.mulVec (f v)) ∧
      f.ker = fixedSpace ρ (pResidual 2 D) := by
  obtain ⟨d⟩ := ChapterB.solvableFFStructure_nonempty ρ hsolv hcore hfaith hff
  let b := d.toSolvableFFFactors
  have ht (i : Fin b.count) : b.factor i = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_congr (b.factorModel i).toEquiv,hcard]
    exact ChapterB.Glauberman.BlockConstruction.PairRecognition.sl_card
  have hc : b.count = 1 := by
    by_contra hn
    have hp := b.count_pos
    have htwo : 1 < b.count := by omega
    have he := b.factor_injective ((ht ⟨0,hp⟩).trans (ht ⟨1,htwo⟩).symm)
    have hf := congrArg Fin.val he
    simp at hf
  have ho : offenderSubgroup ρ = ⊤ :=
    top_unique ((ht ⟨0,b.count_pos⟩) ▸ b.factor_le_offenderSubgroup ⟨0,b.count_pos⟩)
  have hr : pResidual 2 D ≤ offenderSubgroup ρ := ho ▸ le_top
  let a := MulEquiv.ofBijective (b.singleAmbientHom hc)
    ⟨b.singleAmbientHom_injective hfaith hcore hr hc,b.singleAmbientHom_surjective hc⟩
  refine ⟨a,b.singleQuotientMap hfaith hr hc,b.singleQuotientMap_surjective hfaith hr hc,?_,
    b.singleQuotientMap_ker hfaith hr hc⟩
  intro g v
  rw [b.singleQuotientMap_equivariant]
  exact (b.singleAmbientHom_action hc g _).symm

variable {G : Type*} [Group G] [Finite G]
/-- The original reduced action has its actual four-element residual support. -/
theorem cubic_thompson_moved_card (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (T : Sylow 2 G) (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hsolv : Group.IsSolvable D) (hcore : pCore 2 D = ⊥) (hcard : Nat.card D = 6) :
    Nat.card (⁅U,pResidual 2 G⁆ : Subgroup G) = 4 := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hff : IsFFModule ρ := by
    obtain hh | hh := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hh.1)).elim
    · exact hh.2.1
  have hf := NormalElementaryQuotient.representation_injective U q hq hker
  have hd := cubic_ff_moved_finrank ρ hf hsolv hcore hcard hff
  let : IsElementaryAbelian 2 (⁅U,pResidual 2 G⁆ : Subgroup G) :=
    IsElementaryAbelian.of_le (commutator_le_left _ _)
  have he := NormalElementaryQuotient.movedEquiv U q hq hker (pResidual 2 G)
  have hc : Module.finrank (ZMod 2) (Additive (⁅U,pResidual 2 G⁆ : Subgroup G)) = 2 := by
    rw [he.finrank_eq,map_pResidual_of_surjective 2 q hq]
    exact hd
  change Nat.card (Additive (⁅U,pResidual 2 G⁆ : Subgroup G)) = 4
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hc]
  norm_num
/-- Construct the canonical full SL₂(2) marking, preserving the original
normal subgroup and the centralizer quotient map. -/
theorem cubic_thompson_natural_quotient (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (T : Sylow 2 G) (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hsolv : Group.IsSolvable D) (hcore : pCore 2 D = ⊥) (hcard : Nat.card D = 6) :
    ∃ q₀ : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      ∃ (hq₀ : Function.Surjective q₀) (hk₀ : q₀.ker = centralizer (U : Set G)),
      ∃ f : Additive U →ₗ[ZMod 2] (Fin 2 → ZMod 2), Function.Surjective f ∧
        (∀ g v, f (NormalElementaryQuotient.representation U q₀ hq₀ hk₀ g v) =
          SL2NaturalOffenders.NoStrong.natural g (f v)) ∧
        f.ker = fixedSpace (NormalElementaryQuotient.representation U q₀ hq₀ hk₀)
          ((pResidual 2 G).map q₀) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hff : IsFFModule ρ := by
    obtain hh | hh := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hh.1)).elim
    · exact hh.2.1
  obtain ⟨a,f,hf,he,hk⟩ := cubic_ff_natural_quotient ρ
    (NormalElementaryQuotient.representation_injective U q hq hker) hsolv hcore hcard hff
  let q₀ := a.toMonoidHom.comp q
  have hq₀ : Function.Surjective q₀ := a.surjective.comp hq
  have hk₀ : q₀.ker = centralizer (U : Set G) := by
    rw [MonoidHom.ker_comp_of_injective q a.toMonoidHom a.injective,hker]
  let ρ₀ := NormalElementaryQuotient.representation U q₀ hq₀ hk₀
  have hρ (g : G) (v : Additive U) : ρ₀ (q₀ g) v = ρ (q g) v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U q₀ hq₀ hk₀ g v).trans
      (NormalElementaryQuotient.representation_apply U q hq hker g v).symm
  refine ⟨q₀,hq₀,hk₀,f,hf,?_,?_⟩
  · intro g v
    obtain ⟨g,rfl⟩ := hq₀ g
    change f (ρ₀ (q₀ g) v) = (a (q g)).val.mulVec (f v)
    rw [hρ,he]
  · rw [hk,←map_pResidual_of_surjective 2 q hq]
    ext v
    rw [NormalElementaryQuotient.mem_fixedSpace_image,
      NormalElementaryQuotient.mem_fixedSpace_image]

/-- The selected cubic route supplies B.6.10's actual marking internally. -/
theorem cubic_baumann_sylow_and_alpha (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Theory.GroupTheory.IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hsolv : Group.IsSolvable D) (hcore : pCore 2 D = ⊥) (hcard : Nat.card D = 6) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (pResidual 2 G ⊔ ChapterB.baumann (T : Subgroup G)) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  obtain ⟨q₀,hq₀,hk₀,f,hf,he,hk⟩ := cubic_thompson_natural_quotient U q hq hker T hJ hsolv hcore hcard
  exact ChapterB.RankOneBaumann.natural_baumann_sylow_and_alpha T hP U hU hJ q₀ hq₀ hk₀ f hf he hk

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
