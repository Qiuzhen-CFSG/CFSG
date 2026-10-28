module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.CentralSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Centralizer
public import Theory.SpecificGroups.BinaryComponentFixers
public import Theory.SpecificGroups.Triality.ElementarySylowFixers
public import Stellmacher.OmegaOneCenterMap

/-!
# Ordinary Lie models on the literal component quotient

The two normalizer presentations are identified with their kernels and
Sylow images intact. Intrinsic elementary Sylow-fixer bounds for the actual
binary linear, G₂(2)′, Tits and genuine triality carriers bound the omega
center of N_S(L)'s image. The original central seed has nontrivial image,
so this omega center has order two, before any residual-escape argument.

Once the earlier parabolic argument gives escape of O^{3′}(M ∩ L), the
ordinary-component centralizer comparison supplies the literal equality
in 15.1.22(4),(7). No later cubic escape or exchanged-source premise is used.
Source: Aschbacher--Smith, printed p.1099, (**) and the ordinary Lie cases.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup.NormalizerAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private def normalizerEquiv (d : CaseIComponentData T M Mc V) :
    d.componentNormalizer ≃* normalizer (d.L.subgroupOf d.G1 : Set d.G1) where
  toFun x := ⟨⟨x,x.property.1⟩, le_normalizer_comap d.G1.subtype x.property.2⟩
  invFun x := ⟨x.val.val,x.val.property,by
    have hh := le_normalizer_map d.G1.subtype (mem_map_of_mem d.G1.subtype x.property)
    have hm : (d.L.subgroupOf d.G1).map d.G1.subtype = d.L :=
      map_subgroupOf_eq_of_le d.L_component.1
    rwa [hm] at hh⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem normalizerEquiv_kernel (d : CaseIComponentData T M Mc V) :
    d.componentKernel.map d.normalizerEquiv.toMonoidHom = C (d.L.subgroupOf d.G1) := by
  ext x
  rw [mem_map_equiv]
  change (x.val.val ∈ centralizer (d.L : Set G)) ↔
    x.val ∈ centralizer (d.L.subgroupOf d.G1 : Set d.G1)
  constructor
  · intro hc y hy
    exact Subtype.ext (hc y hy)
  · intro hc y hy
    exact congrArg Subtype.val (hc ⟨y,d.L_component.1 hy⟩ hy)

private noncomputable def plusEquiv (d : CaseIComponentData T M Mc V) :
    d.ComponentPlus ≃* NormalizerAction.Star (d.L.subgroupOf d.G1) :=
  QuotientGroup.congr _ _ d.normalizerEquiv d.normalizerEquiv_kernel

private theorem plusEquiv_mk (d : CaseIComponentData T M Mc V) (x : d.componentNormalizer) :
    d.plusEquiv (d.plusMap x) = quotient (d.L.subgroupOf d.G1) (d.normalizerEquiv x) := rfl

private theorem plusEquiv_sylow (d : CaseIComponentData T M Mc V) :
    (d.plus d.sylowNormalizer).map d.plusEquiv.toMonoidHom =
      sylowImage (d.L.subgroupOf d.G1) (d.S.subgroupOf d.G1) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨d.normalizerEquiv y,hy.1,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    refine ⟨d.plusMap (d.normalizerEquiv.symm y),?_,rfl⟩
    exact ⟨d.normalizerEquiv.symm y,⟨hy,(d.normalizerEquiv.symm y).property.2⟩,rfl⟩

/-- The two presentations of the literal normalizer-action omega center have the same order. -/
theorem ordinary_plusOmega_card (d : CaseIComponentData T M Mc V) :
    Nat.card d.plusOmega = Nat.card (omega₁ (center
      (sylowImage (d.L.subgroupOf d.G1) (d.S.subgroupOf d.G1))) (p := 2)) := by
  have he := omegaOneCenterAmbient_map_injective d.plusEquiv.toMonoidHom
    d.plusEquiv.injective (d.plus d.sylowNormalizer)
  rw [d.plusEquiv_sylow] at he
  have hh := congrArg (fun A : Subgroup (NormalizerAction.Star
    (d.L.subgroupOf d.G1)) => Nat.card A) he.symm
  have hcard : Nat.card ((omegaOneCenterAmbient (d.plus d.sylowNormalizer)).map
      d.plusEquiv.toMonoidHom) = Nat.card d.plusOmega :=
    card_map_of_injective (f := d.plusEquiv.toMonoidHom) d.plusEquiv.injective
  rw [hcard] at hh
  change Nat.card d.plusOmega = Nat.card (((omega₁ (center
    (sylowImage (d.L.subgroupOf d.G1) (d.S.subgroupOf d.G1))) (p := 2)).map
      (center (sylowImage (d.L.subgroupOf d.G1) (d.S.subgroupOf d.G1))).subtype).map
        (sylowImage (d.L.subgroupOf d.G1) (d.S.subgroupOf d.G1)).subtype) at hh
  simpa only [card_map_of_injective (sylowImage (d.L.subgroupOf d.G1)
      (d.S.subgroupOf d.G1)).subtype_injective,
    card_map_of_injective (center (sylowImage (d.L.subgroupOf d.G1)
      (d.S.subgroupOf d.G1))).subtype_injective] using hh

private noncomputable def quotientOfModel
    (d : CaseIComponentData T M Mc V) (hc : center d.L = pCore 2 d.L)
    {X : Type*} [Group X] (e : d.L ≃* X) (hx : center X = ⊥) :
    (d.L ⧸ pCore 2 d.L) ≃* X := by
  have hL : center d.L = ⊥ := by
    apply bot_unique
    intro x hxc
    have he := (centerCongr e ⟨x,hxc⟩).property
    change e x ∈ center X at he
    rw [hx, mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  exact ((QuotientGroup.quotientMulEquivOfEq (hc.symm.trans hL)).trans
    QuotientGroup.quotientBot).trans e

open Section03 ChapterA.Section05To06
variable {p : ℕ} {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- A centerless model controls the actual omega center and, after earlier residual escape, its centralizer. -/
theorem PreExclusionSource.ordinary_model_control
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : d.L ≃* X) (hX : center X = ⊥)
    (hfix : ∀ (Q : Sylow 2 X) (B : Subgroup (MulAut X)),
      IsElementaryAbelian 2 B → (∀ b ∈ B, ∀ x ∈ Q, b x = x) → Nat.card B ≤ 2) :
    Nat.card d.plusOmega = 2 ∧
      (¬ d.localThreeResidual ≤ d.ML → d.OrdinaryCentralizerIdentity) := by
  have o := s.ordinary hL
  let eQ := quotientOfModel d o.center_eq e hX
  have hb : Nat.card d.plusOmega ≤ 2 := by
    rw [d.ordinary_plusOmega_card]
    exact d.ordinary_omega_bound_of_model hL o.center_eq s.component_sylow eQ hfix
  have hZ1 := d.marked_le_sylow h hTM
  have hne : d.plusOmega ≠ ⊥ := by
    intro he
    exact d.central_seed_plus_ne_bot hu hZ1 o.central_normalizes
      (bot_unique (he ▸ d.central_seed_plus_le_omega hZ1 o.central_normalizes))
  have hc : Nat.card d.plusOmega = 2 := by
    have hh := (one_lt_card_iff_ne_bot _).mpr hne
    omega
  refine ⟨hc, ?_⟩
  intro hout
  apply d.ordinary_residual_centralizer_of_model hTM hu hL o.center_eq o.center_two
    o.central_normalizes s.component_sylow hZ1 eQ hfix
  intro hR
  exact hout (le_inf hR d.localThreeResidual_le_component)

open Theory.SpecificGroups.BinaryComponentResidual

/-- The actual G₂(2)′, Tits and genuine binary triality models discharge both model inputs. -/
theorem PreExclusionSource.binaryRankTwo_model_control
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L) :
    Nat.card d.plusOmega = 2 ∧
      (¬ d.localThreeResidual ≤ d.ML → d.OrdinaryCentralizerIdentity) := by
  unfold OrdinaryBinaryRankTwo at hm
  rcases hm with hm | hm | hm <;> obtain ⟨e⟩ := hm
  · exact s.ordinary_model_control (h := h) hTM hu hL e g2.1
      (fun Q B hB hfix => @g2_fixers Q B hB hfix)
  · exact s.ordinary_model_control (h := h) hTM hu hL (e.trans Tits.parrottFiniteImageEquiv)
      tits_facts.1 (fun Q B _ hfix => tits_fixers Q B hfix)
  · exact s.ordinary_model_control (h := h) hTM hu hL e
      (Triality.Standard.binaryCarrier_center_eq_bot 1 Nat.zero_lt_one)
      (fun Q B hB hfix =>
        @Triality.Standard.binary_two_elementary_sylow_fixer_card_le_two Q B hB hfix)

/-- The actual SL₄(2) and SL₅(2) models discharge both model inputs. -/
theorem PreExclusionSource.linear_model_control
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Nat.card d.plusOmega = 2 ∧
      (¬ d.localThreeResidual ≤ d.ML → d.OrdinaryCentralizerIdentity) := by
  exact s.ordinary_model_control (h := h) hTM hu hL e (linear hn).1
    (fun Q B _ hfix => linear_fixers hn Q B hfix)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
