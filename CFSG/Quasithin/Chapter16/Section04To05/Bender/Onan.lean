module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction.Order21
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Orbit
public import Theory.Representation.GoldschmidtONan.Consequences

/-!
# The Goldschmidt–O'Nan step in the Bender branch

The normalizer acts on the actual elementary abelian subgroup V through its
faithful automorphism image. Subgroup-to-subspace conversion identifies the
fixed space with Ω₁(T_C), and every linear displacement lies in [V,X]. Thus
the constructed regular cyclic actor supplies transitivity. Tight embedding
supplies the TI condition, and the stabilizer condition gives precisely the
relative normality required by Definition 14.1.

The moving conjugator excludes the singleton orbit. The image of the given
ambient Sylow fixes Ω₁(T_C), so its orbit is odd. This excludes both remaining
nonexceptional alternatives. The exceptional dimensions give |Ω₁(T_C)| = 2,
|V| = 8, and an actual nonabelian action image of order 21.

Only the exact four-case conclusion of GLS96 C.14.2 is an external premise;
no Goldschmidt–O'Nan input, exceptional cardinality or irreducibility is assumed.
The geometry is constructed by `GeometryConstruction` in the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194; GLS, Number 2, C.14.1–14.2,
`refs/KGroup/GLS2/ChapterC.tex`. Conjugation is left conjugation.
-/

@[expose] public section

open Subgroup
open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Representation.GoldschmidtONan
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G]

private noncomputable def binarySpace (V C : Subgroup G) [IsElementaryAbelian 2 V] :
    Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 ((C.subgroupOf V).toAddSubgroup)

private theorem binarySpace_injective {V C D : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) (hD : D ≤ V)
    (he : binarySpace V C = binarySpace V D) : C = D := by
  ext c
  constructor
  · intro hc
    have hm : Additive.ofMul (⟨c, hC hc⟩ : V) ∈ binarySpace V D := he ▸ hc
    exact hm
  · intro hd
    have hm : Additive.ofMul (⟨c, hD hd⟩ : V) ∈ binarySpace V C := he.symm ▸ hd
    exact hm

@[simp] private theorem binarySpace_bot (V : Subgroup G) [IsElementaryAbelian 2 V] :
    binarySpace V ⊥ = ⊥ := by
  ext v
  change (v.toMul : G) = 1 ↔ v = 0
  exact ⟨fun h => congrArg Additive.ofMul (Subtype.ext h), fun h => by simp [h]⟩

private theorem binarySpace_map {V C : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) (m : normalizer (V : Set G)) :
    (binarySpace V C).map (normalizerRepresentation V (V.normalizerMonoidHom.rangeRestrict m)) =
      binarySpace V (C.conjBy m) := by
  ext v
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨(w.toMul : G), hw, congrArg (fun w : Additive V => (w.toMul : G)) he⟩
  · rintro ⟨w, hw, he⟩
    refine ⟨Additive.ofMul (⟨w, hC hw⟩ : V), hw, ?_⟩
    exact congrArg Additive.ofMul (Subtype.ext he)

private theorem binarySpace_map_eq_iff {V C D : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) (hD : D ≤ V) (m : normalizer (V : Set G)) :
    (binarySpace V C).map (normalizerRepresentation V (V.normalizerMonoidHom.rangeRestrict m)) =
      binarySpace V D ↔ C.conjBy m = D := by
  rw [binarySpace_map hC]
  have hCV : C.conjBy m ≤ V :=
    (map_mono hC).trans_eq (mem_normalizer_iff_map_conj_eq.mp m.property)
  exact ⟨binarySpace_injective hCV hD, fun h => congrArg (fun D => binarySpace V D) h⟩

private theorem binarySpace_disjoint {V C D : Subgroup G} [IsElementaryAbelian 2 V]
    (hd : Disjoint C D) : Disjoint (binarySpace V C) (binarySpace V D) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro v hv
  exact congrArg Additive.ofMul (Subtype.ext (disjoint_def.mp hd hv.1 hv.2))

private theorem binarySpace_card {V C : Subgroup G} [IsElementaryAbelian 2 V]
    (hC : C ≤ V) : Nat.card (binarySpace V C) = Nat.card C := by
  exact Nat.card_congr {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun c => ⟨Additive.ofMul ⟨c, hC c.property⟩, c.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem fixedSpace_inducedActor {V X : Subgroup G} [IsElementaryAbelian 2 V]
    (hX : X ≤ normalizer (V : Set G)) :
    fixedSpace (normalizerRepresentation V) (inducedActor V X) =
      binarySpace V (V ⊓ centralizer (X : Set G)) := by
  ext v
  constructor
  · intro hv
    refine ⟨v.toMul.property, ?_⟩
    intro x hx
    have he := hv ⟨V.normalizerMonoidHom.rangeRestrict ⟨x, hX hx⟩,
      ⟨⟨x, hX hx⟩, hx, rfl⟩⟩
    have he' := congrArg (fun w : Additive V => (w.toMul : G)) he
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro hv
    rintro ⟨a, ⟨m, hm, rfl⟩⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hv.2 m hm)

private theorem displacementSpan_le_commutator {V X : Subgroup G} [IsElementaryAbelian 2 V] :
    displacementSpan (normalizerRepresentation V) (inducedActor V X) ⊤ ≤
      binarySpace V ⁅V, X⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨x, hx, rfl⟩, v, _, rfl⟩
  change ((x : G) * (v.toMul : G) * (x : G)⁻¹) / (v.toMul : G) ∈ ⁅V, X⁆
  rw [div_eq_mul_inv]
  rw [commutator_comm V X]
  exact commutator_mem_commutator hx v.toMul.property

variable [Finite G]

private theorem conjugates_disjoint_of_tight {V K : Subgroup G}
    (hK : Theory.GroupTheory.IsTightlyEmbedded K) (hV : IsPGroup 2 V)
    (a b : normalizer (V : Set G)) :
    (V ⊓ K).conjBy a = (V ⊓ K).conjBy b ∨
      Disjoint ((V ⊓ K).conjBy a) ((V ⊓ K).conjBy b) := by
  rcases tight_intersection_TI hK hV
    ((normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).inv_mem a.property)
      b.property) with he | hd
  · left
    have hh := congrArg (fun H : Subgroup G => H.conjBy (a : G)) he
    simpa only [conjBy_conjBy, mul_inv_cancel_left] using hh.symm
  · right
    apply disjoint_iff.mpr
    have hh := congrArg (fun H : Subgroup G => H.map (MulAut.conj (a : G)).toMonoidHom)
      hd.eq_bot
    rw [map_inf _ _ _ (MulAut.conj (a : G)).injective, Subgroup.map_bot] at hh
    change (V ⊓ K).conjBy a ⊓ ((V ⊓ K).conjBy ((a : G)⁻¹ * b)).conjBy a = ⊥ at hh
    simpa only [conjBy_conjBy, mul_inv_cancel_left] using hh

/-- Verify all clauses of GLS96 Definition 14.1 on the faithful image of N_G(V).
The actor remains normal only in the stabilizer of its actual fixed subspace. -/
theorem Geometry.onanInput {T : Sylow 2 G} {z : G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) (h : StandardSetup T z L) :
    let := d.elementary
    GoldschmidtONan.Input (normalizerRepresentation (benderSpace T L))
      (inducedActor (benderSpace T L) d.actor) := by
  let := d.elementary
  let V := benderSpace T L
  let C := omegaOneAmbient (commutingSylow T L)
  let Y := inducedActor V d.actor
  let ρ := normalizerRepresentation V
  have hC : C ≤ V := le_sup_left
  have hfixed : fixedSpace ρ Y = binarySpace V C :=
    (fixedSpace_inducedActor d.actor_normalizes).trans (congrArg (fun D => binarySpace V D) d.fixed_eq)
  have hpow : 2 ≤ 2 ^ n := by
    have hn := d.degree
    have hp := Nat.lt_two_pow_self (n := n)
    omega
  refine {
    faithful := normalizerRepresentation_faithful V
    nontrivial := ?_
    cyclic := ?_
    odd := ?_
    transitive := ?_
    fixed_nontrivial := ?_
    ti := ?_
    normal_in_stabilizer := ?_ }
  · apply (Subgroup.one_lt_card_iff_ne_bot _).mp
    rw [d.inducedActor_card]
    have hn := d.degree
    have hp := Nat.lt_two_pow_self (n := n)
    omega
  · let := d.actor_cyclic
    let : IsCyclic (d.actor.subgroupOf (normalizer (V : Set G))) :=
      (subgroupOfEquivOfLe d.actor_normalizes).isCyclic.mpr inferInstance
    exact isCyclic_of_surjective _ (V.normalizerMonoidHom.rangeRestrict.subgroupMap_surjective
      (d.actor.subgroupOf (normalizer (V : Set G))))
  · rw [d.inducedActor_card]
    apply (Nat.odd_sub' (by omega : 1 ≤ 2 ^ n)).mpr
    simp only [odd_one, true_iff]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := d.degree; omega))
  · intro v hv hv0 w hw hw0
    have hvM := displacementSpan_le_commutator hv
    have hwM := displacementSpan_le_commutator hw
    have hv1 : (v.toMul : G) ≠ 1 := fun hh => hv0 (congrArg Additive.ofMul (Subtype.ext hh))
    have hw1 : (w.toMul : G) ≠ 1 := fun hh => hw0 (congrArg Additive.ofMul (Subtype.ext hh))
    obtain ⟨x, hx, _⟩ := d.regular v.toMul hvM hv1 w.toMul hwM hw1
    refine ⟨⟨V.normalizerMonoidHom.rangeRestrict ⟨x, d.actor_normalizes x.property⟩,
      ⟨⟨x, d.actor_normalizes x.property⟩, x.property, rfl⟩⟩, ?_⟩
    exact congrArg Additive.ofMul (Subtype.ext hx)
  · rw [hfixed]
    intro he
    apply commuting_omega_nontrivial h
    exact binarySpace_injective hC bot_le (he.trans (binarySpace_bot V).symm)
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    obtain ⟨a, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
    obtain ⟨b, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective b
    rw [hfixed] at hne ⊢
    dsimp only at hne ⊢
    rw [binarySpace_map hC, binarySpace_map hC] at hne ⊢
    have ht := conjugates_disjoint_of_tight h.tight
      (T.isPGroup'.of_injective (inclusion (benderSpace_le_sylow T L)) (inclusion_injective _)) a b
    rw [← d.fixed_intersection] at ht
    rcases ht with he | hd
    · exact False.elim (hne (congrArg (fun D => binarySpace V D) he))
    · exact binarySpace_disjoint hd
  · intro a ha
    obtain ⟨a, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
    rw [hfixed] at ha
    exact d.actor_normal_in_stabilizer a (mem_normalizer_iff_map_conj_eq.mpr
      ((binarySpace_map_eq_iff hC hC a).mp ha))


/-- The orbit of the actual fixed subspace is odd because the supplied Sylow
normalizes its corresponding subgroup. -/
theorem Geometry.fixedOrbit_odd {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) :
    let := d.elementary
    Odd (Nat.card (fixedOrbit (normalizerRepresentation (benderSpace T L))
      (inducedActor (benderSpace T L) d.actor))) := by
  let := d.elementary
  let V := benderSpace T L
  let C := omegaOneAmbient (commutingSylow T L)
  let A := ActionImage V
  let Y := inducedActor V d.actor
  let ρ := normalizerRepresentation V
  let F := fixedSpace ρ Y
  let : MulAction A (Submodule (ZMod 2) (Additive V)) := {
    smul a W := W.map (ρ a)
    one_smul W := by
      change W.map (ρ 1) = W
      rw [map_one]; exact Submodule.map_id W
    mul_smul a b W := by
      change W.map (ρ (a * b)) = (W.map (ρ b)).map (ρ a)
      rw [← Submodule.map_comp, map_mul]; rfl }
  have horbit : MulAction.orbit A F = fixedOrbit ρ Y := by
    ext W
    rw [MulAction.mem_orbit_iff]
    rfl
  have hfixed : F = binarySpace V C := by
    rw [show F = fixedSpace ρ Y from rfl, fixedSpace_inducedActor d.actor_normalizes]
    rw [d.fixed_eq]
  obtain ⟨S, hS⟩ := sylow_inducedActor V T d.sylow_normalizes
  have hstab : (S : Subgroup A) ≤ MulAction.stabilizer A F := by
    rintro a ha
    rw [hS] at ha
    obtain ⟨t, ht, rfl⟩ := ha
    change F.map (ρ (V.normalizerMonoidHom.rangeRestrict t)) = F
    rw [hfixed, binarySpace_map_eq_iff (show C ≤ V from le_sup_left) le_sup_left]
    exact mem_normalizer_iff_map_conj_eq.mp (d.sylow_fixes ht)
  change Odd (Nat.card (fixedOrbit ρ Y))
  rw [Nat.card_coe_set_eq, ← horbit]
  exact orbit_odd_of_sylow_fixed S F hstab

private theorem cardinal_binary {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- All Definition 14.1 hypotheses are constructed, and the first three
conclusions of Proposition 14.2 are excluded. Only the exact four-case
conclusion is an external input. -/
theorem Geometry.exceptional_cardinalities {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (halt : let := d.elementary
      Alternatives (normalizerRepresentation (benderSpace T L))
        (inducedActor (benderSpace T L) d.actor)) :
    Nat.card (omegaOneAmbient (commutingSylow T L)) = 2 ∧
      Nat.card (benderSpace T L) = 8 ∧
      Nat.card (ActionImage (benderSpace T L)) = 21 ∧
      ¬ ∀ a b : ActionImage (benderSpace T L), a * b = b * a := by
  let := d.elementary
  let V := benderSpace T L
  let C := omegaOneAmbient (commutingSylow T L)
  let Y := inducedActor V d.actor
  let ρ := normalizerRepresentation V
  have hC : C ≤ V := le_sup_left
  have hfixed : fixedSpace ρ Y = binarySpace V C := by
    rw [fixedSpace_inducedActor d.actor_normalizes, d.fixed_eq]
  have hi : GoldschmidtONan.Input ρ Y := d.onanInput h
  have ho : Odd (Nat.card (fixedOrbit ρ Y)) := d.fixedOrbit_odd
  rcases halt with hs | hs | hs | he
  · have hh := hs.2 (V.normalizerMonoidHom.rangeRestrict ⟨d.mover, d.mover_normalizes⟩)
    rw [hfixed] at hh
    exact False.elim (moving_commuting_omega h hfaith d.mover_eq.symm
      (mem_normalizer_iff_map_conj_eq.mpr
        ((binarySpace_map_eq_iff hC hC _).mp hh)))
  · have hc : Nat.card (fixedOrbit ρ Y) = 2 := by
      rw [hs.1, Nat.card_coe_set_eq, Set.ncard_pair hi.fixed_ne_moved]
    rw [hc] at ho
    exact False.elim ((by decide : ¬ Odd (2 : ℕ)) ho)
  · have hc := hs.1
    rw [cardinal_binary (E := displacementSpan ρ Y ⊤)] at hc
    rw [hc] at ho
    exact False.elim ((Nat.not_even_iff_odd.mpr ho)
      (even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hi.moved_dimension_gt_one; omega))))
  · refine ⟨?_, ?_, he.2.2⟩
    · have hc := cardinal_binary (E := fixedSpace ρ Y)
      rw [he.1, pow_one, hfixed, binarySpace_card hC] at hc
      exact hc
    · have hc := cardinal_binary (E := Additive V)
      rw [he.2.1] at hc
      exact hc


end CFSG.Quasithin.Chapter16.Intersections.Bender
