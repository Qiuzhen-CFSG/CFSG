module
public import Theory.Representation.QuadraticFourGroup.BorelFixed
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.QuadraticSource.SmallMover
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.GroupGeometry

/-!
# The moving actor in the original exchanged module calculation

An elementary quadratic actor moving a component supplies a moving
four-group when its rank is at least two. Its centralizer on the component
is trivial because it centralizes its own conjugation action and is faithful
on the whole component orbit. An actor of order two uses the perfect norm
diagonal and the small-displacement construction instead.

The genuine GLS2 25.14 theorem now identifies every nontrivial irreducible
section on the actual component orbit as a natural tensor. A literal Sylow
normalizer fixes no vector in this tensor. Applied to I/C_I(K₀), this gives
the exact fixed-space calculation used in 15.3.65; no splitting or stability
of I under the Sylow actor is required.

Source: Aschbacher–Smith, D.3.7, printed pp.197–199, moving case, and
15.3.65, printed p.1152. Component-preserving actors remain a separate case.
-/


public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Representation.QuadraticFourGroup
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}

theorem moving_fourGroup (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hρ : Function.Injective ρ) (hK : IsComponent D K)
    [IsElementaryAbelian 2 A] (hAT : A ≤ T)
    (hq : IsQuadratic ρ A) (hc : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hm : ¬A ≤ normalizer (K : Set D)) (hcard : 2 < Nat.card A) :
    ∃ (F : Subgroup D) (a : D), Hypotheses ρ K F a ∧ componentOrbit K F = K₀ := by
  classical
  let _ := Fintype.ofFinite A
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hm
  have hane : a ≠ 1 := fun h => han (h ▸ (normalizer (K : Set D)).one_mem)
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hane
  obtain ⟨b,hb1,hba⟩ := ENat.exists_ne_ne_of_three_le
    (α := A) (by rw [ENat.card_eq_coe_fintype_card,← Nat.card_eq_fintype_card]; exact_mod_cast (by omega : 3 ≤ Nat.card A))
    (1 : A) ⟨a,ha⟩
  have hbne : (b : D) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbo : orderOf (b : D) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (b : D) b.property) hbne
  let F := closure ({a,(b : D)} : Set D)
  have hFA : F ≤ A := (closure_le _).mpr (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact b.property)
  have haf : a ∈ F := subset_closure (by simp)
  have hfour : IsKleinFour F := isKleinFour_closure_pair_of_orderOf a b ho hbo
    (fun hh => hba (Subtype.ext hh.symm))
    (show a * (b : D) = (b : D) * a from congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) b))
  let : IsElementaryAbelian 2 F :=
    IsElementaryAbelian.of_injective (inclusion hFA) (inclusion_injective hFA)
  have horbit : componentOrbit K F = K₀ := by
    apply le_antisymm
      (iSup_conjugates_le_of_le_normalizer K F K₀ geo.component_le (hFA.trans (hAT.trans hTK)))
    have hp := geo.pair a (hAT ha) han
    rw [← hp.1,← hp.2.2.2.1]
    exact sup_le (le_componentOrbit K F)
      (le_iSup (fun f : F => K.map (MulAut.conj (f : D)).toMonoidHom) ⟨a,haf⟩)
  have hcent : F ⊓ centralizer (K : Set D) = ⊥ := by
    let Z := F ⊓ centralizer (K : Set D)
    have hAZ : A ≤ centralizer (Z : Set D) := by
      intro x hx z hz
      exact congrArg Subtype.val (mul_comm (⟨z,hFA hz.1⟩ : A) ⟨x,hx⟩)
    have hKZ : K ≤ centralizer (Z : Set D) :=
      le_centralizer_iff.mp inf_le_right
    have hOZ : componentOrbit K F ≤ centralizer (Z : Set D) :=
      iSup_conjugates_le_of_le_normalizer K F (centralizer (Z : Set D)) hKZ
        ((hFA.trans hAZ).trans (centralizer (Z : Set D)).le_normalizer)
    have hZK : Z ≤ centralizer (K₀ : Set D) := by
      rw [← horbit]
      exact le_centralizer_iff.mp hOZ
    apply le_bot_iff.mp
    rw [← hc]
    exact le_inf (inf_le_left.trans hFA) hZK
  refine ⟨F,a,⟨hρ,hK,inferInstance,hfour.card_four,haf,ho,?_,?_,hcent⟩,horbit⟩
  · exact fun h => han (mem_normalizer_iff_map_conj_eq.mpr h)
  · intro b hb v
    exact hq b (hFA hb) a ha v

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Representation.QuadraticFourGroup
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}

theorem irreducibleSection_fixedSpace_eq_bot_of_fourGroup
    {F : Subgroup D} {a : D} (h : Hypotheses ρ K F a)
    (he : componentOrbit K F = K₀)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) K₀ W)
    (hs : IsIrreducibleSection (ρ.comp K₀.subtype) σ) (hn : ¬σ.IsTrivial)
    (hB : ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀) :
    fixedSpace σ (B.subgroupOf K₀) = ⊥ := by
  subst K₀
  obtain ⟨M⟩ := ChapterB.ComponentNormalization.QuadraticSource.twoFactorModel h
  have ht := ChapterB.ComponentNormalization.QuadraticSource.naturalTensorSection h M σ hs hn
  let : Group.IsPerfect (componentOrbit K F) := h.orbit_properties.1
  let : Group.IsPerfect (Factor M.n) := Group.IsPerfect.ofSurjective
    (f := (MonoidHom.fst _ _).comp M.projection) (by
      intro x
      obtain ⟨y,hy⟩ := M.projection_surjective (x,1)
      exact ⟨y,congrArg Prod.fst hy⟩)
  obtain ⟨P,hP⟩ := hB
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  exact ht.sylowNormalizer_fixed_eq_zero M.one_lt M.projection_surjective P w
    (fun x hx => hw ⟨x,hP ▸ hx⟩)

theorem central_fixedSpace_eq_bot_of_fourGroup
    {F : Subgroup D} {a : D} (h : Hypotheses ρ K F a)
    (he : componentOrbit K F = K₀) {I : Submodule (ZMod 2) V}
    (hi : IsIrrPlus ρ K₀ I)
    (hB : ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀) :
    fixedSpace (centralQuotientRepresentation ρ K₀ I hi.choose)
      (B.subgroupOf K₀) = ⊥ :=
  irreducibleSection_fixedSpace_eq_bot_of_fourGroup ρ h he _
    (hi.centralQuotient_isIrreducibleSection ρ hi.choose)
    (hi.centralQuotient_not_isTrivial ρ hi.choose) hB

theorem moving_fourGroup_of_small_ratio
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hρ : Function.Injective ρ) (hK : IsComponent D K) [IsSimpleGroup K]
    [IsElementaryAbelian 2 A] (hAT : A ≤ T)
    (hq : IsQuadratic ρ A) (hc : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hm : ¬A ≤ normalizer (K : Set D))
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    : ∃ (F : Subgroup D) (a : D), Hypotheses ρ K F a ∧ componentOrbit K F = K₀ := by
  by_cases hlarge : 2 < Nat.card A
  · obtain ⟨F,a,hF,he⟩ := moving_fourGroup ρ geo hTK hρ hK hAT hq hc hm hlarge
    exact ⟨F,a,hF,he⟩
  · have hnon : A ≠ ⊥ := fun he => hm (he ▸ bot_le)
    let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hnon
    have htwo : Nat.card A = 2 := by have := Finite.one_lt_card (α := A); omega
    have hr : rank A = 1 := by norm_num [rank,htwo]
    obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hm
    have hao : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha)
      (fun he => han (he ▸ (normalizer (K : Set D)).one_mem))
    have hda : fixedCodim ρ (zpowers a) ≤ 2 :=
      (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr ha)).trans (by simpa [hr] using hd)
    obtain ⟨F,hF,hFle⟩ :=
      ChapterB.ComponentNormalization.QuadraticSource.small_mover_fourGroup ρ hρ hK hao han hda
    have hp := geo.pair a (hAT ha) han
    have hpair : K ⊔ K.map (MulAut.conj a).toMonoidHom = K₀ := by
      change K ⊔ K.conjBy a = K₀
      rw [hp.2.2.2.1]
      exact hp.1
    have he : componentOrbit K F = K₀ := by
      apply le_antisymm
      · apply iSup_conjugates_le_of_le_normalizer K F K₀ geo.component_le
        apply hFle.trans
        rw [hpair]
        exact sup_le K₀.le_normalizer (zpowers_le.mpr (hTK (hAT ha)))
      · rw [← hpair]
        exact sup_le (le_componentOrbit K F)
          (le_iSup (fun f : F => K.map (MulAut.conj (f : D)).toMonoidHom) ⟨a,hF.mem⟩)
    exact ⟨F,a,hF,he⟩

theorem moving_central_fixedSpace_eq_bot
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hρ : Function.Injective ρ) (hK : IsComponent D K) [IsSimpleGroup K]
    [IsElementaryAbelian 2 A] (hAT : A ≤ T)
    (hq : IsQuadratic ρ A) (hc : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hm : ¬A ≤ normalizer (K : Set D))
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    {I : Submodule (ZMod 2) V} (hi : IsIrrPlus ρ K₀ I)
    (hB : ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀) :
    fixedSpace (centralQuotientRepresentation ρ K₀ I hi.choose)
      (B.subgroupOf K₀) = ⊥ := by
  obtain ⟨F,a,hF,he⟩ := moving_fourGroup_of_small_ratio ρ geo hTK hρ hK hAT hq hc hm hd
  exact central_fixedSpace_eq_bot_of_fourGroup ρ hF he hi hB

theorem moving_fixedSpace_le
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hρ : Function.Injective ρ) (hK : IsComponent D K) [IsSimpleGroup K]
    [IsElementaryAbelian 2 A] (hAT : A ≤ T)
    (hq : IsQuadratic ρ A) (hc : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hm : ¬A ≤ normalizer (K : Set D))
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    {I : Submodule (ZMod 2) V} (hi : IsIrrPlus ρ K₀ I)
    (hB : ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  have hzero := moving_central_fixedSpace_eq_bot ρ geo hTK hρ hK hAT hq hc hm hd hi hB
  rintro v ⟨hvi,hvB⟩
  have hvq : Submodule.Quotient.mk (⟨v,hvi⟩ : I) ∈
      fixedSpace (centralQuotientRepresentation ρ K₀ I hi.choose) (B.subgroupOf K₀) := by
    intro b
    change Submodule.Quotient.mk (⟨ρ (b : K₀) v,(hi.choose (b : K₀).property v).2 hvi⟩ : I) =
      Submodule.Quotient.mk (⟨v,hvi⟩ : I)
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (hvB ⟨(b : K₀),b.property⟩)
  rw [hzero,Submodule.mem_bot] at hvq
  exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K₀).comap I.subtype)).mp hvq

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
