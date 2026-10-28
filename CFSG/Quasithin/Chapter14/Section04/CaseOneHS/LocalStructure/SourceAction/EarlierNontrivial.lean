module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.EarlierGeometry
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity
public import Theory.Representation.NormalSimpleSeed

/-!
# Nontriviality of the earlier conjugate-center action

For the original nonextraspecial rank-three flag, Z(U)^g has nontrivial
image in H/C_H(U/Z(U)), before any centerlessness assumption.

If its image were trivial, 12.8.10 gives Z(U) = Z(I₂) × V₁ and
[L,Z(I₂)] = 1. Uniqueness forces the normal closure J of L₁ in H into
H intersect M. Thus J preserves V/V₁ and centralizes Z(U). Its seed
V/V₁ is simple and nontrivial for L₁, hence for J, and its H-orbit spans
U/V₁. Clifford semisimplicity gives C_(U/V₁)(J) = 0, contradicting
Z(U)/V₁ nontrivial. The normality of L₁ itself is unnecessary.

The actual G.10 actor then has at least half the dimension. This proves
the center conclusion of 14.3.12(3) for a small actor and removes that
branch in the nonextraspecial 14.3.24 consumer. The full marked alternatives
and their later exclusions remain unproved; this module assumes neither
those alternatives nor the later natural action. Import this extension
directly, as EarlierGeometry lies above the lower SourceAction umbrella.

Source: Aschbacher--Smith, 12.8.13(4), 14.3.12(3), and 14.3.24,
printed pp.855--856,993,1000.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped MonoidAlgebra
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem center_split_of_trivial_image (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hzero : F.terminalDot (conjugate F.ZU g) = ⊥) :
    (F.ZU = Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      Disjoint (Chapter12.Section08.centerIn (F.I₂ L)) (F.Vi 1) ∧
      ∃ e : Chapter12.Section08.centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
        ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
    ⁅L, Chapter12.Section08.centerIn (F.I₂ L)⁆ = ⊥ := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  apply h.localKernel_center_product ⟨structural, unique, alternatives⟩ F hne g hgP hgH
  have hker := (source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  intro z hz
  have hzH := F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
    (F.conjugate_ZU_le_X g hz)
  have hzq : QuotientGroup.mk' F.terminalHatAction.ker ⟨z, hzH⟩ = 1 := by
    apply mem_bot.mp
    rw [← hzero]
    exact ⟨⟨z, hzH⟩, hz, rfl⟩
  have hk : (⟨z, hzH⟩ : F.H) ∈ F.uhatAction.ker :=
    (QuotientGroup.eq_one_iff _).mp hzq
  have hzE : z ∈ F.E g := by
    rw [← hker, F.mem_xHatKernel]
    exact ⟨F.conjugate_ZU_le_X g hz, (F.mem_uhatAction_ker_iff _).mp hk⟩
  exact hzE.1.1

private theorem closure_location_of_trivial_image (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hzero : F.terminalDot (conjugate F.ZU g) = ⊥) :
    Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥ ∧
      normalizer (Chapter12.Section08.centerIn (F.I₂ L) : Set G) ≤ normalizer (L : Set G) ∧
      conjugateSpanBy (F.Li L 1) F.H ≤
        F.H ⊓ centralizer (F.ZU : Set G) ⊓ normalizer (L : Set G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let D := Chapter12.Section08.centerIn (F.I₂ L)
  obtain ⟨⟨hsplit, _, _⟩, hLD⟩ := center_split_of_trivial_image d earlier hq chosen
    structural alternatives F hne g hgP hgH hzero
  have hD : D ≠ ⊥ := by
    intro he
    exact hZ (by simpa only [show Chapter12.Section08.centerIn (F.I₂ L) = ⊥ from he,
      bot_sup_eq] using hsplit)
  have hDT : D ≤ (T : Subgroup G) :=
    (hsplit ▸ (le_sup_left : D ≤ D ⊔ F.Vi 1)).trans
      ((map_subtype_le (center F.U)).trans
        (source_closure_le_sylow d earlier hq chosen structural alternatives F))
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hND : normalizer (D : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hLN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique structural unique).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hLN⟩)
    · exact T.isPGroup'.to_le hDT
    · exact hD
    · exact sup_le ((commutator_eq_bot_iff_le_centralizer.mp hLD).trans
        (Subgroup.centralizer_le_normalizer _)) ((F.binary_sylow_le_P L).trans
          ((le_normalizer_conjugateSpanBy F.U (F.P L)).trans
            (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L)))))
  have hLC : F.Li L 1 ≤ centralizer (F.ZU : Set G) := by
    apply le_centralizer_iff.mp
    rw [hsplit]
    apply sup_le
    · exact le_centralizer_iff.mp (((F.Li_le L 1).trans inf_le_left).trans
        (commutator_eq_bot_iff_le_centralizer.mp hLD))
    · exact le_centralizer_iff.mp (((F.Li_le L 1).trans inf_le_right).trans
        (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hJC : conjugateSpanBy (F.Li L 1) F.H ≤ centralizer (F.ZU : Set G) :=
    conjugateSpanBy_le hLC (F.H_normalizes_ZU.trans (normalizer_le_normalizer_centralizer _))
  have hDC : D ≤ F.ZU := hsplit ▸ le_sup_left
  refine ⟨hD, hND, le_inf (le_inf (conjugateSpanBy_le_self
    ((F.Li_le L 1).trans inf_le_right)) hJC) ?_⟩
  exact hJC.trans ((centralizer_le hDC).trans
    ((Subgroup.centralizer_le_normalizer _).trans hND))


omit [Finite G] in
private theorem seed_moved [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 (F.tilde V)]
    (hLV : L ≤ normalizer (V : Set G)) (D : F.NaturalSeedMarking L hLV) :
    ∃ k v, F.localSeedRepresentation L hLV k v ≠ v := by
  by_contra! hfix
  let v := D.coordinates.symm (![1, 0] : Fin 2 → ZMod 2)
  have hw : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hw' : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  obtain ⟨a, ha⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hw hw'
  obtain ⟨q, hq⟩ := D.quotientEquiv.surjective a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  have he := D.equivariant k v
  rw [hfix, hq] at he
  simp only [v, LinearEquiv.apply_symm_apply] at he
  have hh := congrFun (he.trans ha) 0
  norm_num at hh

private theorem closure_fixed_center_le_point (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hloc : conjugateSpanBy (F.Li L 1) F.H ≤
      F.H ⊓ centralizer (F.ZU : Set G) ⊓ normalizer (L : Set G)) :
    F.ZU ≤ F.Vi 1 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.tilde_elementary_of_point htwo hphi
  let := F.localKernel_tilde_seed_elementary
  let : IsElementaryAbelian 2 (F.tilde (F.UH F.H)) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.tilde F.U))
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let J := conjugateSpanBy (F.Li L 1) F.H
  have hJH : J ≤ F.H := hloc.trans (inf_le_left.trans inf_le_left)
  let N := J.subgroupOf F.H
  let : N.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he, card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer d earlier hq chosen ⟨structural, unique, alternatives⟩
    (F.Vi 1) F.H hpoint (F.le_seed 1) le_rfl
  have hJV : J ≤ normalizer (V : Set G) := by
    intro j hj
    exact ((hm ▸ (show j ∈ F.H ⊓ normalizer (L : Set G) from
      ⟨hJH hj,(hloc hj).2⟩))).2
  let ρ := F.localSpanRepresentation F.H le_rfl
  let σ := F.localSeedRepresentation L chosen.normalizes
  let ι := F.localSeedInclusion F.H
  let τ := ρ.comp N.subtype
  have hKJ : F.Li L 1 ≤ J := le_conjugateSpanBy _ _
  let kN : F.Li L 1 →* N := {
    toFun k := ⟨⟨k, hJH (hKJ k.property)⟩, hKJ k.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hι (k : F.Li L 1) (v : Additive (F.tilde V)) :
      ι (σ k v) = τ (kN k) (ι v) :=
    F.localSeedInclusion_equivariant L F.H chosen.normalizes le_rfl
      ((F.Li_le L 1).trans inf_le_right) k v
  let S : Subrepresentation τ := {
    toSubmodule := LinearMap.range ι
    apply_mem_toSubmodule a _ hv := by
      obtain ⟨v,rfl⟩ := hv
      let w := F.tildeAction J V hJH hJV ⟨a.val.val, a.property⟩ v.toMul
      refine ⟨Additive.ofMul w, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl }
  obtain ⟨k, v, hmv⟩ := seed_moved F chosen.normalizes D
  have hmove : ∃ n : N, ∃ v : S, S.toRepresentation n v ≠ v := by
    refine ⟨kN k, ⟨ι v, ⟨v,rfl⟩⟩, ?_⟩
    intro he
    have hh : τ (kN k) (ι v) = ι v := congrArg Subtype.val he
    rw [← hι] at hh
    exact hmv (F.localSeedInclusion_injective F.H hh)
  have hsimple : IsIrreducible σ :=
    (irreducible_iff_isSimpleModule_asModule σ).mpr (D.seed_simple (by decide))
  have hs : IsIrreducible S.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom S).mpr
    rw [isAtom_iff_le_of_ge]
    refine ⟨?_, ?_⟩
    · intro he
      have hzero (w : S) : w.val = 0 := by
        have he' : S.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule he
        exact (show w.val ∈ (⊥ : Submodule (ZMod 2) (Additive (F.tilde (F.UH F.H)))) from
          he' ▸ w.property)
      obtain ⟨a,w,hm⟩ := hmove
      exact hm (Subtype.ext ((hzero _).trans (hzero _).symm))
    · intro R hR hRS
      let A : Subrepresentation σ := {
        toSubmodule := R.toSubmodule.comap ι
        apply_mem_toSubmodule k _ hv := by
          change ι (σ k _) ∈ R
          rw [hι]
          exact R.apply_mem_toSubmodule _ hv }
      have hA : A ≠ ⊥ := by
        intro he
        apply hR
        apply bot_unique
        intro w hw
        obtain ⟨v,rfl⟩ := hRS hw
        have hv : v ∈ A := hw
        rw [he] at hv
        change v = 0 at hv
        rw [hv, map_zero]
        exact (⊥ : Subrepresentation τ).toSubmodule.zero_mem
      have ha : A = ⊤ := (hsimple.eq_bot_or_eq_top A).resolve_left hA
      rintro w ⟨v,rfl⟩
      exact (show v ∈ A from ha ▸ Submodule.mem_top)
  have hgen : ∀ R : Subrepresentation ρ, S.toSubmodule ≤ R.toSubmodule → R = ⊤ := by
    intro R hR
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← F.localSeed_orbit_span F.H le_rfl]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,v,rfl⟩
    exact R.apply_mem_toSubmodule a (hR ⟨v,rfl⟩)
  have hf := fixedSpace_eq_bot_of_normal_simple_seed ρ N S hs hmove hgen
  intro z hz
  let u : F.U := ⟨z, (map_subtype_le (center F.U)) hz⟩
  let v := Additive.ofMul (F.tildeMap F.U F.U_le_H u)
  have hv : v ∈ BinaryOffender.fixedSpace τ ⊤ := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change F.tildeProjection a.val.val * F.tildeProjection ⟨z,F.U_le_H u.property⟩ *
      (F.tildeProjection a.val.val)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg F.tildeProjection
    apply Subtype.ext
    change (a.val.val:G) * z * (a.val.val:G)⁻¹ = z
    have hc := (hloc a.val.property).1.2 z hz
    change z * (a.val.val:G) = (a.val.val:G) * z at hc
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [hf] at hv
  have he : F.tildeMap F.U F.U_le_H u = 1 := congrArg Additive.toMul hv
  have hk : u ∈ (F.tildeMap F.U F.U_le_H).ker := he
  rwa [F.tildeMap_U_ker] at hk



/-- Earlier nontriviality of the literal conjugate-center action. -/
theorem source_earlier_conjugate_center_ne_bot (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  let := chosen.elementary
  intro hzero
  have hloc := (closure_location_of_trivial_image d earlier hq chosen structural alternatives F hne hZ
    g hgP hgH hzero).2.2
  exact hZ (le_antisymm
    (closure_fixed_center_le_point d earlier hq chosen structural alternatives F hne hloc)
    (F.point_le_ZU (by decide)))

/-- The original nonextraspecial flag supplies the large-actor inequality in 14.3.24. -/
theorem source_earlier_dimension_le_twice_actor (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Module.finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) :=
  source_dimension_le_twice_actor_of_dot_center_ne_bot d earlier hq chosen structural alternatives
    F g hne hgP hgH
    (source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives F hne hZ g hgP hgH)

/-- The original dotted conjugate center is trivial exactly in the extraspecial branch. -/
theorem source_earlier_conjugate_center_eq_bot_iff (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) = ⊥ ↔ F.ZU = F.Vi 1 := by
  constructor
  · intro hz
    by_contra hZ
    exact source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH hz
  · exact fun hZ => CaseOneLarge.source_terminal_conjugate_center F d earlier hq chosen
      structural alternatives hne hZ g hgP hgH

/-- Source 14.3.12(3)'s center conclusion on the original rank-three flag. -/
theorem source_earlier_center_eq_point_of_small_actor (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hne : ¬ IsMulCommutative F.U) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hsmall : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) : F.ZU = F.Vi 1 := by
  by_contra hZ
  have hlarge := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  let := chosen.elementary
  obtain ⟨htwo,hphi,hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have hd := (quotient_dimension F htwo hphi hvc).1
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
