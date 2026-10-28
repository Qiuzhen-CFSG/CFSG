module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalBlockConjugacy
public import Theory.Representation.BinaryPermutation.EightCoreLine

/-!
# The original weight-two commutator line

An order-two commutator of R_v on the original V has weight two in its
augmentation-core marking: each R_v element preserves the L-orbits, so
the rank-one model lemma applies to a moving element. The original A6
point residual fixes only one nonzero quotient vector. Consequently at
a weight-two point this commutator is the literal point line.

For the aligned block pair, the escaping conjugator fixes the line.
The source preferred-choice condition therefore forces the original
point to have weight two as well. Its line is the commutator, so the
conjugator fixes the point. Since it carries K_v to L, the point would
be L-fixed, contradicting its nonsingular projection. The full original
V, its constant line and its quotient map are retained throughout.

Source: Aschbacher--Smith 12.6.16(2), printed pp.826--827, combined
manuscript of 1 March 2004. The preferred-choice and alignment premises
are discharged at the actual consumer in PreferredBlock.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the original augmentation module, an order-two R_v commutator is
exactly a weight-two line. The full central cover is retained. -/
theorem SourceHypothesis.nonsingular_commutator_weight_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hc : Nat.card (⁅V,Rv T L (v : G)⁆ : Subgroup G) = 2) :
    ∃ u : V, u ≠ 1 ∧ ⁅V,Rv T L (v : G)⁆ = zpowers (u : G) ∧
      wordWeight (E (Additive.ofMul u)).val = 2 := by
  classical
  let R₀ := Rv T L (v : G)
  let W := ⁅V,R₀⁆
  have hRJ : R₀ ≤ LT T L := (pCoreIn_le 2 _).trans inf_le_left
  have hn : R₀ ≤ normalizer (V : Set G) := hRJ.trans (sup_le H.chosen.normalizes hTV)
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hn
  obtain ⟨u₀,hu₀,hunique⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hc
  let u : V := ⟨u₀,hWV u₀.property⟩
  have hu : u ≠ 1 := fun h => hu₀ (Subtype.ext (congrArg (fun x : V => (x : G)) h))
  have hline : W = zpowers (u : G) := by
    apply le_antisymm _ (zpowers_le.mpr u₀.property)
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ (zpowers (u : G)).one_mem
    have he : x = (u : G) := congrArg Subtype.val
      (hunique ⟨x,hx⟩ (fun h => hx1 (congrArg Subtype.val h)))
    rw [he]
    exact mem_zpowers (u : G)
  let σ := seedRepresentation R₀ V hn
  have hnontrivial : ∃ r : R₀, ∃ x : Additive V, σ r x ≠ x := by
    by_contra! hfix
    have hcent : R₀ ≤ centralizer (V : Set G) := by
      intro r hr x hx
      have he := congrArg (fun y : Additive V => (y.toMul : G))
        (hfix ⟨r,hr⟩ (Additive.ofMul (⟨x,hx⟩ : V)))
      change r*x*r⁻¹ = x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hb : W = ⊥ := by
      change ⁅V,R₀⁆ = ⊥
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hmem : (u₀ : G) ∈ (⊥ : Subgroup G) := hb.le u₀.property
    exact hu₀ (Subtype.ext (mem_bot.mp hmem))
  obtain ⟨r,x,hx⟩ := hnontrivial
  let f : core (Fin 8) →ₗ[ZMod 2] core (Fin 8) :=
    E.toLinearMap.comp ((σ r).comp E.symm.toLinearMap)
  have hf (y) : f (E y) = E (σ r y) := by
    change E (σ r (E.symm (E y))) = _
    rw [E.symm_apply_apply]
  have hmove (y) : f y - y = 0 ∨ f y - y = E (Additive.ofMul u) := by
    obtain ⟨y,rfl⟩ := E.surjective y
    rw [hf,←map_sub]
    have hd : ((σ r y - y).toMul : G) ∈ W := by
      change (r : G) * (y.toMul : G) * (r : G)⁻¹ / (y.toMul : G) ∈ W
      rw [div_eq_mul_inv]
      change ⁅(r : G),(y.toMul : G)⁆ ∈ W
      change ⁅(r : G),(y.toMul : G)⁆ ∈ ⁅V,R₀⁆
      rw [commutator_comm]
      exact commutator_mem_commutator r.property y.toMul.property
    by_cases hz : σ r y - y = 0
    · exact Or.inl (by rw [hz,map_zero])
    · right
      have he := hunique ⟨_,hd⟩ (fun h => hz
        (Additive.toMul.injective (Subtype.ext (congrArg (fun x : W => (x : G)) h))))
      apply congrArg E
      exact Additive.toMul.injective (Subtype.ext (congrArg (fun x : W => (x : G)) he))
  have hp (i j : Fin 8) (hij : i ≠ j) : wordWeight (f (pair i j)).val = 2 := by
    let y := E.symm (pair i j)
    obtain ⟨l,hl⟩ := D.normalizer_orbit_control H.chosen r
      ((sup_le L.le_normalizer H.chosen.sylow_normalizes_component) (hRJ r.property))
      (hn r.property) y.toMul
    have he : σ r y = seedRepresentation L V H.chosen.normalizes l y :=
      Additive.toMul.injective (Subtype.ext hl)
    change wordWeight (E (σ r y)).val = 2
    rw [he,hE]
    change wordWeight (representation (Fin 8) (D.actorMap l).val (E y).val) = 2
    rw [wordWeight_permute]
    change wordWeight (E (E.symm (pair i j))).val = 2
    rw [E.apply_symm_apply]
    exact EightCoreLine.pair_weight i j hij
  refine ⟨u,hu,hline,?_⟩
  apply EightCoreLine.weight_two_of_line_displacements f _
    (fun h => hu (Additive.ofMul.injective (E.injective (h.trans E.map_zero.symm)) )) hmove hp
  exact ⟨E x,fun h => hx (E.injective ((hf x).symm.trans h))⟩


/-- The point residual fixes just one nonzero vector in the original orthogonal quotient. -/
theorem OrthogonalMarking.nonsingular_fixed_projection
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (u : V) (hu : D.Nonsingular u)
    (hfix : (u : G) ∈ centralizer (Lv L (v : G) : Set G)) :
    D.coordinates (Submodule.Quotient.mk (Additive.ofMul u)) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)) := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  let ρ := alternatingNaturalRepresentation (Fin 8)
  let F := fixedSpace ρ (pointFixer i j)
  let f := D.coordinates.toLinearMap.comp (fixedSeed L V chosen.normalizes).toSubmodule.mkQ
  have hmem (x : V) (hx : (x : G) ∈ centralizer (Lv L (v : G) : Set G)) :
      f (Additive.ofMul x) ∈ F := by
    intro a
    obtain ⟨l,rfl⟩ := D.localPairMap_surjective v i j hij hp a
    have he := D.equivariant (inclusion (Lv_le_L L (v : G)) l)
      (Submodule.Quotient.mk (Additive.ofMul x))
    have hh : seedRepresentation L V chosen.normalizes
        (inclusion (Lv_le_L L (v : G)) l) (Additive.ofMul x) = Additive.ofMul x := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (x : G) * (l : G)⁻¹ = x
      rw [mem_centralizer_iff.mp hx l l.property,mul_inv_cancel_right]
    change D.coordinates (Submodule.Quotient.mk (seedRepresentation L V chosen.normalizes
      (inclusion (Lv_le_L L (v : G)) l) (Additive.ofMul x))) = _ at he
    rw [hh] at he
    exact he.symm
  have hF : Nat.card F = 2 := by
    have hd := pointFixer_fixedCodim i j hij
    have hs := Submodule.finrank_quotient_add_finrank F
    have hn := finrank_natural_even (Fin 8) (by decide)
    have hdim : Module.finrank (ZMod 2) F = 1 := by
      change Module.finrank (ZMod 2) (natural (Fin 8) ⧸ F) = 5 at hd
      change Module.finrank (ZMod 2) (natural (Fin 8)) = 6 at hn
      omega
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim,pow_one]
  let a : F := ⟨f (Additive.ofMul u),hmem u hfix⟩
  let b : F := ⟨f (Additive.ofMul v),hmem v (fun l hl =>
    mem_centralizer_singleton_iff.mp (Lv_le_Gv L (v : G) hl))⟩
  have hne (x : V) (hx : D.Nonsingular x) : f (Additive.ofMul x) ≠ 0 := by
    intro hh
    apply hx
    change TerminalOrthogonal.Eight.form (f (Additive.ofMul x)) = 0
    rw [hh,map_zero]
  have ha : a ≠ 0 := fun h => hne u hu (congrArg Subtype.val h)
  have hb : b ≠ 0 := fun h => hne v hv (congrArg Subtype.val h)
  exact congrArg Subtype.val (((Nat.card_eq_two_iff' (0 : F)).mp hF).unique ha hb)

/-- At a weight-two point, the literal order-two commutator is the point line. -/
theorem SourceHypothesis.nonsingular_commutator_eq_point_of_weight_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (v : V) (hv : D.Nonsingular v) (hweight : wordWeight (E (Additive.ofMul v)).val = 2)
    (hc : Nat.card (⁅V,Rv T L (v : G)⁆ : Subgroup G) = 2) :
    ⁅V,Rv T L (v : G)⁆ = zpowers (v : G) := by
  obtain ⟨u,hu,hline,hw⟩ := H.nonsingular_commutator_weight_two D hTV E hE v hc
  have hnR : Lv L (v : G) ≤ normalizer (Rv T L (v : G) : Set G) :=
    (show Lv L (v : G) ≤ LT T L ⊓ Gv (v : G) from
      le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _)).trans
      ((LT T L ⊓ Gv (v : G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hn : Lv L (v : G) ≤ normalizer (↑(⁅V,Rv T L (v : G)⁆ : Subgroup G) : Set G) :=
    by
      intro l hl
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (H.chosen.normalizes (Lv_le_L L _ hl)),
        mem_normalizer_iff_map_conj_eq.mp (hnR hl)]
  have hcL := hn.trans (normalizer_le_centralizer_of_card_two _ hc)
  have huf : (u : G) ∈ centralizer (Lv L (v : G) : Set G) :=
    le_centralizer_iff.mp hcL (hline.symm ▸ mem_zpowers (u : G))
  have hus : D.Nonsingular u := by
    change TerminalOrthogonal.Eight.form (D.coordinates (Submodule.Quotient.mk (Additive.ofMul u))) ≠ 0
    rw [←hproj,(EightGeometry.nonsingular_core_iff _).mpr (Or.inl hw)]
    exact one_ne_zero
  have he := D.nonsingular_fixed_projection H.chosen v hv u hus huf
  rw [←hproj,←hproj] at he
  have huv : u = v := Additive.ofMul.injective (E.injective
    (EightCoreLine.weight_two_projection_injective _ _ hw hweight he))
  rwa [huv] at hline


/-- The aligned-block contradiction in 12.6.16(2). The preferred-choice
condition refers to weight two in the full original core, including its center. -/
theorem SourceHypothesis.nonsingular_aligned_block_contradiction_of_preferred
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hshort : ChapterC.IsShort L)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Kv (v : G) ≤ M L)
    (hpref : ∀ u : V, wordWeight (E (Additive.ofMul u)).val = 2 →
      ¬ Gv (u : G) ≤ M L → wordWeight (E (Additive.ofMul v)).val = 2)
    (hlt : Q T L < Rv T L (v : G))
    (g : G) (hg : g ∉ M L)
    (hK : (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L)
    (hR : (Rv T L (v : G)).map (MulAut.conj g).toMonoidHom = Rv T L (v : G)) : False := by
  obtain ⟨_,hc,hfix⟩ := H.nonsingular_aligned_block_commutator_line D hTV hshort v hv he hlt g hK hR
  obtain ⟨u,_,hu,hwu⟩ := H.nonsingular_commutator_weight_two D hTV E hE v hc
  have hgu : g ∈ Gv (u : G) := mem_centralizer_singleton_iff.mpr
    (hfix u (hu.symm ▸ mem_zpowers (u : G))).symm
  have hwv := hpref u hwu (fun h => hg (h hgu))
  have hline := H.nonsingular_commutator_eq_point_of_weight_two D hTV E hE hproj v hv hwv hc
  have hgv : MulAut.conj g (v : G) = (v : G) := by
    change g*(v : G)*g⁻¹ = v
    rw [←hfix v (hline.symm ▸ mem_zpowers (v : G)),mul_inv_cancel_right]
  have hmap : (Gv (v : G)).map (MulAut.conj g).toMonoidHom = Gv (v : G) := by
    change (centralizer ({(v : G)} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({(v : G)} : Set G)
    rw [map_pointCentralizer,hgv]
  have hLG : L ≤ Gv (v : G) := by
    rw [←hK,←hmap]
    exact map_mono (Kv_le_Gv _)
  apply nonsingular_not_mem_ZV D hv
  exact ⟨v.property,fun l hl => mem_centralizer_singleton_iff.mp (hLG hl)⟩

end CFSG.Quasithin.Chapter12.Section06
