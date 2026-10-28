module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionComponents
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Natural quotient bounds and the second local marking

For the constructed w, O₂(C_G(w)) is the literal W=⟨w⟩. The original
Sylow subgroup of order 128 therefore maps to a Sylow subgroup of order
64 in C_G(w)/W, whose two-core is trivial. Subnormality identifies the
kernel on every ordinary component with its intrinsic two-core. Its
quotient embeds by the original inclusion and quotient map, so its order
cannot be divisible by 128.

The already proved O₂(C_G(w)) ∩ I₂ = 1 makes the restriction to
C_{I₂}(w) injective. Its image has order 96 and a normal C₄ × C₄ kernel
with quotient S₃. Pulling this kernel back gives exactly the original
C_R(w), preserving the second local marking used in recognition.
All source applications retain the original z, T and constructed w.

Source: Aschbacher--Smith 14.3.22, printed p.999; refs/quasithin.pdf.
The actual G₂(2) quotient recognition remains with qt-e-14322-core-collapse.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

omit [Finite G] in
/-- The intrinsic core is the actual marked kernel, not just an isomorphic cyclic group. -/
theorem twoCore_eq_markedKernel {w : G}
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w) :
    pCore 2 (ResidualFusion.C w) = ResidualFusion.W w := by
  apply map_injective (ResidualFusion.C w).subtype_injective
  change (ResidualFusion.C w).pCoreIn 2 =
    (zpowers (ResidualFusion.point w)).map (ResidualFusion.C w).subtype
  rw [MonoidHom.map_zpowers]
  exact hcore

/-- The natural quotient sends the original Sylow subgroup of order 128 to one of order 64. -/
theorem quotient_sylow_card {w : G} (hw : orderOf w = 2)
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    (S : Sylow 2 (ResidualFusion.C w)) (hS : Nat.card S = 128) :
    Nat.card (S.mapSurjective (f := QuotientGroup.mk' (ResidualFusion.W w))
      (QuotientGroup.mk'_surjective _)) = 64 := by
  let C := ResidualFusion.C w
  let W := ResidualFusion.W w
  let q := QuotientGroup.mk' W
  have hWS : W ≤ (S : Subgroup C) := by
    change ResidualFusion.W w ≤ (S : Subgroup C)
    rw [←twoCore_eq_markedKernel hcore]
    exact pCore_isPGroup.le_sylow_of_normal S
  have hWc : Nat.card W = 2 := by
    change Nat.card (zpowers (ResidualFusion.point w)) = 2
    rw [Nat.card_zpowers, ←orderOf_coe]
    exact hw
  have hh := (W.subgroupOf (S : Subgroup C)).index_mul_card
  have hrel : W.relIndex (S : Subgroup C) = Nat.card ((S : Subgroup C).map q) := by
    simpa only [q, QuotientGroup.ker_mk'] using (relIndex_ker (S : Subgroup C) q)
  change W.relIndex (S : Subgroup C) * Nat.card (W.subgroupOf (S : Subgroup C)) = Nat.card S at hh
  rw [hrel, Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv, hWc, hS] at hh
  change Nat.card ((S : Subgroup C).map q) = 64
  omega

/-- There is no factor 128 in the order of the literal opposite quotient. -/
theorem quotient_not_128_dvd {w : G} (hw : orderOf w = 2)
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    (S : Sylow 2 (ResidualFusion.C w)) (hS : Nat.card S = 128) :
    ¬128 ∣ Nat.card (ResidualFusion.C w ⧸ ResidualFusion.W w) := by
  intro hd
  have hh := (S.mapSurjective (f := QuotientGroup.mk' (ResidualFusion.W w))
    (QuotientGroup.mk'_surjective _)).pow_dvd_card_of_pow_dvd_card (n := 7) hd
  rw [quotient_sylow_card hw hcore S hS] at hh
  norm_num at hh

/-- The quotient has trivial two-core at the literal marked kernel. -/
theorem quotient_twoCore_eq_bot {w : G}
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w) :
    pCore 2 (ResidualFusion.C w ⧸ ResidualFusion.W w) = ⊥ := by
  rw [←pCore_map_iso 2 (QuotientGroup.quotientMulEquivOfEq
    (twoCore_eq_markedKernel hcore)),
    pCore_quotient_pCore_eq_bot, Subgroup.map_bot]

/-- The kernel on an actual component is its intrinsic two-core. -/
theorem component_quotient_kernel {w : G}
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    {D : Subgroup (ResidualFusion.C w)} (hD : IsComponent (ResidualFusion.C w) D) :
    ((QuotientGroup.mk' (ResidualFusion.W w)).comp D.subtype).ker = pCore 2 D := by
  rw [←MonoidHom.comap_ker, QuotientGroup.ker_mk', ←twoCore_eq_markedKernel hcore]
  exact (pCore_subnormal_eq_comap 2 hD.1).symm

/-- The induced map keeps the original component inclusion and quotient map. -/
noncomputable def componentQuotientMap {w : G}
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    {D : Subgroup (ResidualFusion.C w)} (hD : IsComponent (ResidualFusion.C w) D) :
    (D ⧸ pCore 2 D) →* (ResidualFusion.C w ⧸ ResidualFusion.W w) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (ResidualFusion.W w)).comp D.subtype)
    (component_quotient_kernel hcore hD).symm.le

/-- Compatibility with the original component inclusion and the natural quotient map. -/
theorem componentQuotientMap_mk {w : G}
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    {D : Subgroup (ResidualFusion.C w)} (hD : IsComponent (ResidualFusion.C w) D)
    (x : D) :
    componentQuotientMap hcore hD (QuotientGroup.mk' (pCore 2 D) x) =
      QuotientGroup.mk' (ResidualFusion.W w) (x : ResidualFusion.C w) := rfl

theorem componentQuotientMap_injective {w : G}
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    {D : Subgroup (ResidualFusion.C w)} (hD : IsComponent (ResidualFusion.C w) D) :
    Function.Injective (componentQuotientMap hcore hD) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (component_quotient_kernel hcore hD).symm

/-- Every actual component quotient inherits the strict two-part bound. -/
theorem component_quotient_not_128_dvd {w : G} (hw : orderOf w = 2)
    (hcore : (ResidualFusion.C w).pCoreIn 2 = zpowers w)
    (S : Sylow 2 (ResidualFusion.C w)) (hS : Nat.card S = 128)
    {D : Subgroup (ResidualFusion.C w)} (hD : IsComponent (ResidualFusion.C w) D) :
    ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  intro hd
  exact quotient_not_128_dvd hw hcore S hS (hd.trans
    (card_dvd_of_injective (componentQuotientMap hcore hD)
      (componentQuotientMap_injective hcore hD)))

omit [Finite G] in
/-- The original parabolic centralizer quotient has its literal homocyclic kernel. -/
theorem LocalGeometry.parabolic_centralizer_structure
    {F : InvariantFlag T V 2} {L : Subgroup G} {z w : G}
    (h : LocalGeometry F L z w) :
    ∃ π : (F.I₂ L ⊓ ResidualFusion.C w : Subgroup G) →* Equiv.Perm (Fin 3),
      Function.Surjective π ∧
      π.ker = ((F.I₂ L).pCoreIn 2).subgroupOf (F.I₂ L ⊓ ResidualFusion.C w) ∧
      Nonempty (π.ker ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
      Nat.card (F.I₂ L ⊓ ResidualFusion.C w : Subgroup G) = 96 := by
  let I := F.I₂ L
  let J := I ⊓ ResidualFusion.C w
  let R := I.pCoreIn 2
  obtain ⟨π, hπ, hk⟩ := h.parabolic_quotient
  have hsub : R.subgroupOf J = (R ⊓ ResidualFusion.C w).subgroupOf J := by
    ext x
    exact ⟨fun hx => ⟨hx, x.property.2⟩, And.left⟩
  have hle : R ⊓ ResidualFusion.C w ≤ J := inf_le_inf_right _ (pCoreIn_le 2 I)
  let ek : π.ker ≃* (R ⊓ ResidualFusion.C w : Subgroup G) :=
    (MulEquiv.subgroupCongr hk).trans
      ((MulEquiv.subgroupCongr hsub).trans (subgroupOfEquivOfLe hle))
  let em := ek.trans h.core_centralizer_model.some
  have hkc : Nat.card π.ker = 16 := by
    rw [Nat.card_congr em.toEquiv, Nat.card_prod]
    change Nat.card (ZMod 4) * Nat.card (ZMod 4) = 16
    norm_num
  have hqc : Nat.card (J ⧸ π.ker) = 6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc : Nat.card J = 96 := by
    rw [card_eq_card_quotient_mul_card_subgroup π.ker, hqc, hkc]
  exact ⟨π, hπ, hk, ⟨em⟩, hc⟩

/-- Restriction of the natural centralizer quotient map to C_{I₂}(w). -/
noncomputable def parabolicQuotientMap
    (F : InvariantFlag T V 2) (L : Subgroup G) (w : G) :
    (F.I₂ L ⊓ ResidualFusion.C w : Subgroup G) →*
      (ResidualFusion.C w ⧸ ResidualFusion.W w) :=
  (QuotientGroup.mk' (ResidualFusion.W w)).comp (inclusion inf_le_right)

open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s


/-- Apply the quotient bound to each component of the literal constructed opposite centralizer. -/
theorem source_triple_component_quotient_bound
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) :
    ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  obtain ⟨S, _, _, hSc, _⟩ := source_triple_component_catalogue
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  exact component_quotient_not_128_dvd
    (source_triple_local_geometry
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
    (source_triple_twoCore_eq
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself) S hSc hD

/-- The original parabolic centralizer embeds through the natural W quotient. -/
theorem source_triple_parabolicQuotientMap_injective
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    Function.Injective (parabolicQuotientMap F (sourceResidual M Mc) (tripleProduct d a)) := by
  let w := tripleProduct d a
  let C := ResidualFusion.C w
  let I := F.I₂ (sourceResidual M Mc)
  let J := I ⊓ C
  let f := parabolicQuotientMap F (sourceResidual M Mc) w
  have hcore := source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hdis := (source_triple_twoCore_parabolic_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).1
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hk : inclusion (show J ≤ C from inf_le_right) x ∈ ResidualFusion.W w :=
    (QuotientGroup.eq_one_iff _).mp hx
  rw [←twoCore_eq_markedKernel hcore] at hk
  have hxN : (x : G) ∈ C.pCoreIn 2 := mem_map_of_mem C.subtype hk
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp
    (hdis ▸ (show (x : G) ∈ C.pCoreIn 2 ⊓ I from ⟨hxN, x.property.1⟩))))

/-- The second local marking inside the actual quotient: order 96, with
normal C₄ × C₄ kernel and symmetric-three quotient. -/
theorem source_triple_quotient_parabolic_structure
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let f := parabolicQuotientMap F (sourceResidual M Mc) (tripleProduct d a)
    Function.Injective f ∧ Nat.card f.range = 96 ∧
      ∃ π : f.range →* Equiv.Perm (Fin 3), Function.Surjective π ∧
        Nonempty (π.ker ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
        π.ker.comap f.rangeRestrict =
          ((F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf
            (F.I₂ (sourceResidual M Mc) ⊓ ResidualFusion.C (tripleProduct d a)) := by
  intro f
  have hf := source_triple_parabolicQuotientMap_injective
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let ef := MonoidHom.ofInjective hf
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨π, hπ, hkπ, ⟨ek⟩, hcJ⟩ := hlocal.parabolic_centralizer_structure
  have hc : Nat.card f.range = 96 := (Nat.card_congr ef.symm.toEquiv).trans hcJ
  let ρ := π.comp ef.symm.toMonoidHom
  have hk : ρ.ker = π.ker.map ef.toMonoidHom := MonoidHom.ker_comp_mulEquiv π ef.symm
  refine ⟨hf, hc, ρ, hπ.comp ef.symm.surjective,
    ⟨((MulEquiv.subgroupCongr hk).trans (ef.subgroupMap π.ker).symm).trans ek⟩, ?_⟩
  rw [←hkπ]
  ext x
  change π (ef.symm (ef x)) = 1 ↔ π x = 1
  rw [ef.symm_apply_apply]

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
