module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SeedCoordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.CriticalSeeds
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction

/-!
# Common-line exclusion and doubled weak-closure escape

The full critical commutator has order 2^(4n). Restriction to each original
natural seed successively takes its square root, giving a common commutator
of order 2^n. Its actors belong to the original L-induced automizer, so a
nonzero displacement supplies a full field line; the order forces equality.
The same calculation after inverse conjugation makes it a field line on
both sides. Transitivity in the original L aligns those lines with the
supplied source line. The proved 11.3.4(4) normalizer bound then forces the
seeds to coincide, contrary to their noncommutation.

This excludes the actual F.7.11 pair, proves weak-closure escape for V_M,
and yields k=2n with the preceding generation bound. The reciprocal source
consumer now retains only the strict r-bound from the doubled geometry.
The invariant flag is matched on the literal chosen quotient. The earlier
rank-one recognition retains its owner qt-d-1222-shadow-rankone-recognition.
No parameter upper bound k≤n is asserted until the strict r-bound is proved.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SeedCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

omit [Finite G] in
/-- Conjugating a critical pair back reverses its two factors. -/
theorem inverse_pair (W : Subgroup G) (g : G)
    (hne : ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ ≤ W ⊓ W.map (MulAut.conj g).toMonoidHom) :
    ⁅W,W.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅W,W.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤ W ⊓ W.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hc : (W.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = W := by
    simpa only [inv_inv] using offender_map_conj_inverse W g⁻¹
  constructor
  · intro hz
    have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) hz
    rw [map_commutator,hc,Subgroup.map_bot,commutator_comm] at hh
    exact hne hh
  · have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcomm
    rw [map_commutator,offender_map_conj_inverse,
      Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      offender_map_conj_inverse,commutator_comm,inf_comm] at hh
    exact hh

private theorem square_root {a n : ℕ} (h : a^2 = 2^(2*n)) : a = 2^n := by
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  change a^2 = (2^n)^2
  rw [h,←pow_mul,Nat.mul_comm n 2]

/-- Restriction from the full module to its original seed halves the
critical commutator dimension. -/
theorem mixed_commutator_card (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    Nat.card (⁅V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ : Subgroup G) =
      2^(2*S.field.degree) := by
  have hn := le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  have hh := commutator_card_square d hn
    (CriticalAction.pair_normalizes_seeds d g hne hcomm).1
    (CriticalAction.conjugate_inducedAutomizer_le d g hn hne)
  rw [commutator_comm _ (fullModule L V),CriticalAction.pair_commutator_card d g hne hcomm,
    commutator_comm _ V] at hh
  apply square_root
  simpa only [←Nat.mul_assoc,show 2*2=4 from rfl] using hh.symm

/-- A second restriction, on the reciprocal original seed, gives exactly
one field degree. Both occurrences use the literal original conjugation. -/
theorem seed_commutator_card (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    Nat.card (⁅V,V.map (MulAut.conj g).toMonoidHom⁆ : Subgroup G) = 2^S.field.degree := by
  obtain ⟨hne',hcomm'⟩ := inverse_pair (fullModule L V) g hne hcomm
  have hn := le_normalizer_iff_commutator_le_left.mpr (hcomm'.trans inf_le_left)
  have hs : V.map (MulAut.conj g⁻¹).toMonoidHom ≤
      (fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom := map_mono seed_le_fullModule
  have hI : inducedAutomizer (fullModule L V) (V.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      inducedAutomizer (fullModule L V) L :=
    (map_mono (comap_mono hs)).trans (CriticalAction.conjugate_inducedAutomizer_le d g⁻¹ hn hne')
  have hh := commutator_card_square d (hs.trans hn)
    (hs.trans (CriticalAction.pair_normalizes_seeds d g⁻¹ hne' hcomm').1) hI
  have hc : (V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = V := by
    simpa only [inv_inv] using offender_map_conj_inverse V g⁻¹
  have hmap (B : Subgroup G) :
      Nat.card (⁅V.map (MulAut.conj g⁻¹).toMonoidHom,B⁆ : Subgroup G) =
        Nat.card (⁅V,B.map (MulAut.conj g).toMonoidHom⁆ : Subgroup G) := by
    rw [←card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := ⁅V.map (MulAut.conj g⁻¹).toMonoidHom,B⁆)
      (MulAut.conj g).injective,map_commutator,hc]
  rw [hmap,hmap,mixed_commutator_card d g hne hcomm] at hh
  exact square_root hh.symm


private theorem projection_commutator
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {A : Subgroup G} (hAL : A ≤ normalizer (L : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (a : A) (v : V) :
    ((LocalGeometry.Coordinates.sl3 m).projection
      (V.normalizerMonoidHom (inclusion hAV a) v * v⁻¹)).toAdd =
        (LocalGeometry.Coordinates.sl3 m).conjugationAction hAL hAV a
          ((LocalGeometry.Coordinates.sl3 m).projection v).toAdd -
          ((LocalGeometry.Coordinates.sl3 m).projection v).toAdd := by
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
  rw [← (LocalGeometry.Coordinates.sl3 m).conjugationAction_projection]

/-- The original quotient detects a field line in any nonzero commutator
of size at most q whose action comes from L. -/
theorem commutator_line (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {A : Subgroup G} (hAW : A ≤ normalizer (fullModule L V : Set G))
    (hAV : A ≤ normalizer (V : Set G))
    (hI : inducedAutomizer (fullModule L V) A ≤ inducedAutomizer (fullModule L V) L)
    (hne : ⁅A,V⁆ ≠ ⊥) (hcard : Nat.card (⁅A,V⁆ : Subgroup G) ≤ 2^S.field.degree) :
    ∃ U : Submodule S.field.Carrier (Fin 3 → S.field.Carrier),
      Module.finrank S.field.Carrier U = 1 ∧
        (LocalGeometry.Coordinates.sl3 m).preimage U = ⁅A,V⁆ := by
  let b := LocalGeometry.Coordinates.sl3 m
  let hAL := hAW.trans (fullModule_normalizer d).le
  let ρ := b.conjugationAction hAL hAV
  have hi := (projection_bijective d m).injective
  obtain ⟨a,x,hx⟩ : ∃ a : A, ∃ x : b.Space, ρ a x ≠ x := by
    by_contra! hz
    apply hne
    apply bot_unique
    apply commutator_le.mpr
    intro a ha v hv
    let a' : A := ⟨a,ha⟩
    let v' : V := ⟨v,hv⟩
    let z : V := V.normalizerMonoidHom (inclusion hAV a') v' * v'⁻¹
    have he : z = 1 := by
      apply hi
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (b.projection z).toAdd = 0
      rw [projection_commutator m hAL hAV,hz,sub_self]
    exact mem_bot.mpr (congrArg Subtype.val he)
  let w := ρ a x - x
  have hw : w ≠ 0 := sub_ne_zero.mpr hx
  let U := Submodule.span S.field.Carrier {w}
  have hdim : Module.finrank S.field.Carrier U = 1 := finrank_span_singleton hw
  have hle : b.preimage U ≤ ⁅A,V⁆ := by
    intro v hv
    let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp ((b.mem_preimage U v').mp hv)
    obtain ⟨y,hy⟩ := b.projection_surjective (Multiplicative.ofAdd (r • x))
    let z : V := V.normalizerMonoidHom (inclusion hAV a) y * y⁻¹
    have he : z = v' := by
      apply hi
      apply Multiplicative.toAdd.injective
      change (b.projection z).toAdd = (b.projection v').toAdd
      rw [projection_commutator m hAL hAV,hy]
      change ρ a (r • x) - r • x = (b.projection v').toAdd
      rw [action_linear d m hAW hAV hI,←smul_sub]
      exact hr
    have hz : (z : G) ∈ ⁅A,V⁆ := commutator_mem_commutator a.property y.property
    rwa [he] at hz
  refine ⟨U,hdim,Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Closure.Nonabelian.card_preimage b (seed_fixed_trivial d),hdim,pow_one]
  exact hcard

/-- The commutator of the original critical seeds is an actual field line,
not only a subgroup with the same order. -/
theorem seed_commutator_line (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    ∃ U : Submodule S.field.Carrier (Fin 3 → S.field.Carrier),
      Module.finrank S.field.Carrier U = 1 ∧
        (LocalGeometry.Coordinates.sl3 m).preimage U = ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ := by
  have hn := le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  have hs : V.map (MulAut.conj g).toMonoidHom ≤
      (fullModule L V).map (MulAut.conj g).toMonoidHom := map_mono seed_le_fullModule
  have hI : inducedAutomizer (fullModule L V) (V.map (MulAut.conj g).toMonoidHom) ≤
      inducedAutomizer (fullModule L V) L :=
    (map_mono (comap_mono hs)).trans (CriticalAction.conjugate_inducedAutomizer_le d g hn hne)
  have hnV := hs.trans (CriticalAction.pair_normalizes_seeds d g hne hcomm).1
  have he := CriticalAction.pair_seed_commutator_ne_bot d g hne hcomm
  have hc := seed_commutator_card d g hne hcomm
  rw [commutator_comm V] at he hc ⊢
  exact commutator_line d m (hs.trans hn) hnV hI he hc.le

end SeedCoordinates
namespace CriticalLine
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Common-line alignment excludes the critical pair using the normalizer
of the original source line. Both corrections lie in the original L. -/
theorem pair_commutes (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (P : Submodule S.field.Carrier (Fin 3 → S.field.Carrier))
    (hP : Module.finrank S.field.Carrier P = 1)
    (hN : normalizer ((LocalGeometry.Coordinates.sl3 m).preimage P : Set G) ≤
      normalizer (V : Set G)) (g : G)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  by_contra hne
  let b := LocalGeometry.Coordinates.sl3 m
  obtain ⟨Q,hQ,heQ⟩ := SeedCoordinates.seed_commutator_line d m g hne hcomm
  obtain ⟨hne',hcomm'⟩ := SeedCoordinates.inverse_pair (fullModule L V) g hne hcomm
  obtain ⟨R,hR,heR⟩ := SeedCoordinates.seed_commutator_line d m g⁻¹ hne' hcomm'
  obtain ⟨l,hl⟩ := LocalGeometry.SL3.PlaneAction.field_lines_transitive D S m P Q hP hQ
  obtain ⟨k,hk⟩ := LocalGeometry.SL3.PlaneAction.field_lines_transitive D S m P R hP hR
  change (b.preimage P).map (MulAut.conj (l:G)).toMonoidHom = b.preimage Q at hl
  change (b.preimage P).map (MulAut.conj (k:G)).toMonoidHom = b.preimage R at hk
  rw [heQ] at hl
  rw [heR] at hk
  have hc : (V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = V := by
    simpa only [inv_inv] using offender_map_conj_inverse V g⁻¹
  have ha : ((l:G)⁻¹*g*(k:G)) ∈ normalizer (b.preimage P : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (b.preimage P).map (MulAut.conj ((l:G)⁻¹*g*(k:G))).toMonoidHom =
          (((b.preimage P).map (MulAut.conj (k:G)).toMonoidHom).map
            (MulAut.conj g).toMonoidHom).map (MulAut.conj (l:G)⁻¹).toMonoidHom := by
        rw [offender_map_conj_map,offender_map_conj_map,mul_assoc]
      _ = b.preimage P := by
        rw [hk,map_commutator,hc,commutator_comm,←hl,offender_map_conj_inverse]
  have hg : g ∈ normalizer (V : Set G) := by
    have he : g = (l:G)*((l:G)⁻¹*g*(k:G))*(k:G)⁻¹ := by group
    rw [he]
    exact (normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).mul_mem (D.normalizes l.property) (hN ha))
      ((normalizer (V : Set G)).inv_mem (D.normalizes k.property))
  apply CriticalAction.pair_seed_commutator_ne_bot d g hne hcomm
  have hgV : V.map (MulAut.conj g).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp hg
  rw [hgV]
  let := D.elementary
  exact commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer

end CriticalLine

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Source weak-closure escape for the full doubled module. The flag is the
original source flag, identified on the literal chosen quotient. The normalizer
bound is discharged by 11.3.4(4), and the critical pair by common-line alignment. -/
theorem source_weak_escape (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hpoint : (LocalGeometry.Coordinates.sl3 m).binarySubspace (f.space 0) = U₁) :
    ¬ indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2 := by
  have hN := line_normalizer_le_of_counterexample h p hc
    (Or.inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)
  have hp : (LocalGeometry.Coordinates.sl3 m).preimage (f.space 0) =
      D.centralQuotientPreimage U₁ := congrArg D.centralQuotientPreimage hpoint
  rw [←hp] at hN
  apply weak_escape_of_pair_centralization h d
  intro g _ hcomm
  exact CriticalLine.pair_commutes d m (f.space 0) (f.dimension 0) hN g hcomm

/-- With the proved doubled escape and s-value, E.3.20 and the preceding
upper bound force the original generation parameter to be 2n. -/
theorem source_parameter_eq_twice (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hpoint : (LocalGeometry.Coordinates.sl3 m).binarySubspace (f.space 0) = U₁)
    (hu : generationParameter H ≤ 2*S.field.degree) :
    generationParameter H = 2*S.field.degree :=
  parameter_eq_twice h d (source_weak_escape h p hc d m f hpoint)
    (LocalMinimum.globalS_eq d) hu

/-- The source reciprocal contradiction now needs only the strict r-bound
from this doubled branch. The original weak-closure premise is discharged. -/
theorem source_contradiction_of_r (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hpoint : (LocalGeometry.Coordinates.sl3 m).binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H) (hu : generationParameter H ≤ 2*S.field.degree)
    (hr : (2*S.field.degree : ℕ∞) < globalR (fullModule L V)) : False :=
  source_contradiction_of_escape_and_r h p hc d r hu
    (source_weak_escape h p hc d m f hpoint) hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
