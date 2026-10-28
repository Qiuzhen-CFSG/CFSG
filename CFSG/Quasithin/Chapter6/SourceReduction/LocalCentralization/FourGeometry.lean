module
public import Theory.GroupTheory.ReducedNormal.FourGeometry
public import Theory.GroupTheory.FixedSupplementCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.OmegaAction
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.HallPlane

/-!
# Four-dimensional geometry of the literal local Cartan configuration

The original residual has an A₅ quotient, so five divides its order.
Restriction to the actual Sylow join puts the omega commutator in the
reduced-action setting. A quintic operator eliminates its residual-fixed
space, and normal A₇ self-normalization identifies the entire local action.
The given omega-span splitting then identifies the residual-fixed and
component-fixed subgroups of the original omega-center.

Source: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

namespace LocalCartanWitness
omit [Finite G] in
/-- Five divides the actual ambient residual of the witnessed local subgroup. -/
theorem five_dvd_residual {T : Sylow 2 G} {H A Y X D : Subgroup G}
    (d : LocalCartanWitness T H A Y X D) : 5 ∣ Nat.card (residual H) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := d.residual_linear
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hc : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hh : 5 ∣ Nat.card (pResidual 2 H) :=
    (by decide : 5 ∣ 60).trans (hc ▸ card_quotient_dvd_card (pCore 2 (pResidual 2 H)))
  rwa [card_map_of_injective H.subtype_injective]
end LocalCartanWitness

namespace LocalA7Configuration
variable {T : Sylow 2 G} {L W H A Y X D K : Subgroup G} {n : ℕ}

/-- In the four-dimensional alternative the original residual has no fixed
vector, and the whole Sylow join has literal two-core quotient A₇. -/
private theorem four_geometry_and_fixed_line (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2 := by
  let M := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let R := (residual H).subgroupOf M
  have hRK := d.residual_le.trans a.contains
  have hRM : residual H ≤ M := hRK.trans le_sup_left
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer a.sylow_normalizes)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 K)
    (subgroupOfEquivOfLe (show K ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)))
  let := LocalOmega.quotient_quasisimple a.maximal.1 (Or.inl a.quotient)
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : e b ∈ center (K ⧸ pCore 2 K) := MulEquivClass.apply_mem_center e hb
    rw [LocalOmega.quotient_center a.maximal.1 (Or.inl a.quotient)] at hh
    exact e.injective (by simpa only [mem_bot,map_one] using hh)
  have hcard : Nat.card U = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv).trans hc
  have hnon : U ≠ ⊥ := by
    intro he
    have hh : Nat.card U = 1 := he ▸ card_bot
    omega
  have hmove : ⁅U,B⁆ ≠ ⊥ := by
    have he : ⁅U,B⁆ = U := by
      apply map_injective M.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le a.reduced.1,
        map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),
        LocalOmega.full_movement (h.qtke.evenCharacteristic T) a.maximal.1 a.sylow_normalizes]
    rwa [he]
  have hfive : 5 ∣ Nat.card R := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv]
    exact d.five_dvd_residual
  have hfixed := four_reduced_fixed_eq_bot U B R hr hz hmove hcard (comap_mono hRK) hfive
  have hquot : IsPGroup 2 (M ⧸ B) := by
    apply isPGroup_quotient_of_sup_eq_top B ((T : Subgroup G).subgroupOf M)
      T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show K ≤ M from le_sup_left) (show (T : Subgroup G) ≤ M from le_sup_right)]
    exact subgroupOf_self M
  refine ⟨?_,four_reduced_alternatingSeven_quotient U B hr hz hmove hcard
    (e.trans a.quotient.some) hquot,?_⟩
  · apply bot_unique
    intro x hx
    have hh : (⟨x,a.reduced.1 hx.1⟩ : M) ∈ U ⊓ centralizer (R : Set M) := by
      refine ⟨hx.1,?_⟩
      intro r hrr
      apply Subtype.ext
      exact hx.2 r hrr
    exact congrArg Subtype.val (mem_bot.mp (hfixed.le hh))
  · let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
    have hline := four_reduced_alternatingSeven_sylow_fixed_card U B hr hz hmove hcard
      (e.trans a.quotient.some) P
    let := a.reduced.2.1
    have hUT : localOmegaModule T K ≤ (T : Subgroup G) :=
      (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans
        (LocalOmega.span_elementary_le_sylow T K (h.qtke.evenCharacteristic T)
          a.maximal.1 a.sylow_normalizes).2
    have hmap : (U ⊓ centralizer ((P : Subgroup M) : Set M)).map M.subtype =
        omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K := by
      ext x
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hUT hx.1,
          elemPow_eq_one_of_isElementaryAbelian (p := 2)
            (A := localOmegaModule T K) x.val hx.1,?_⟩,hx.1⟩
        intro t ht
        exact congrArg Subtype.val
          (hx.2 (⟨t,(show (T : Subgroup G) ≤ M from le_sup_right) ht⟩ : M) ht)
      · intro hx
        refine ⟨⟨x,a.reduced.1 hx.2⟩,⟨hx.2,?_⟩,rfl⟩
        intro t ht
        apply Subtype.ext
        exact ((mem_omegaOneCenterAmbient_iff _ _).mp hx.1).2.2 t ht
    rw [←hmap,card_map_of_injective M.subtype_injective]
    exact hline

/-- Residual fixed-space vanishing and the whole local quotient, with the
original public action and quotient conventions. -/
theorem four_geometry (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨hf,hq,_⟩ := four_geometry_and_fixed_line a h d hc
  exact ⟨hf,hq⟩

/-- The fixed line is the intersection with the original omega-center. -/
theorem four_omega_intersection_card_two (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2 :=
  (four_geometry_and_fixed_line a h d hc).2.2

/-- The residual and its A₇ overcomponent have the same fixed subgroup
on the actual omega-center in the four-dimensional alternative. -/
theorem four_omega_fixed_eq (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (K : Set G)
  have hn : F ≤ normalizer (localOmegaModule T K : Set G) :=
    inf_le_left.trans ((show Z ≤ (T : Subgroup G) from fun z hz => (mem_omegaOneCenterAmbient_iff _ _).mp hz |>.1).trans
      (le_sup_right.trans (reduced_normalizes a.reduced)))
  have hFR : F ≤ centralizer (residual H : Set G) :=
    inf_le_right.trans (centralizer_le (d.residual_le.trans a.contains))
  have hfix : (F ⊔ localOmegaModule T K) ⊓ centralizer (residual H : Set G) = F := by
    rw [inf_centralizer_sup_of_centralizing F (localOmegaModule T K) (residual H) hn hFR,
      (a.four_geometry h d hc).1,sup_bot_eq]
  apply le_antisymm
  · intro z hz
    apply hfix.le
    refine ⟨?_,hz.2⟩
    rw [sup_comm,←a.span_eq]
    exact le_conjugateSpanBy Z K hz.1
  · exact inf_le_inf_left Z (centralizer_le (d.residual_le.trans a.contains))
end LocalA7Configuration
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
