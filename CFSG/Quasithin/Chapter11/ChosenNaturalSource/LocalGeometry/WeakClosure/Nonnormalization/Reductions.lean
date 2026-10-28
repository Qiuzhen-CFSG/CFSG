module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.CriticalPair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Fusion and rank reductions for the original 11.2.4

The abelian normalizer span prevents a noncommuting conjugate from aligning
its marked first preimage. A small corank gives the normalization needed for
the root calculation. Sylow conjugacy and the unique relative noncentral
component give the point orbit under the plane normalizer. The original
Sylow centralizer equals O₂(LT), so even commuting conjugates lie in R₂.
Generation by centralizers of corank at most 2n then gives the bound on r.

The small-action predicate uses the original quotient by C_V(L). The image
comparison below proves its equivalence with a join with the whole kernel;
no complement or splitting of a symplectic central extension is selected.
The small-action exclusion must be uniform over all conjugates in T, since
the subsequent parabolic argument changes the conjugate inside R₂.

The final assembly and its actual critical-pair application are conditional.
Root recognition, the parabolic calculation, and the normalized-pair plane
alignment remain explicit geometric obligations. They must be proved before
these declarations establish source 11.2.4 or 11.2.5. The exact preceding
numerical, component and Sylow fixed-space outputs are also explicit.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 11.2.4--5,
printed pp.769--770, using 11.1.3 and 11.2.2, printed pp.765,767--768.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE


namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
variable {G : Type*} [Group G] {V U : Subgroup G}

/-- Alignment of the actual first preimage contradicts noncentrality. -/
theorem conjugate_centralizes_of_point_alignment
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (U : Set G)) V))
    (g x : G) (hx : x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hU : (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom = U) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hn : x * g ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U.map (MulAut.conj (x * g)).toMonoidHom = U
    rwa [← offender_map_conj_map]
  have he : V.map (MulAut.conj (x * g)).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom := by
    rw [← offender_map_conj_map]
    exact mem_normalizer_iff_map_conj_eq.mp hx
  apply bot_unique
  rw [← he]
  exact (commutator_mono (Source.le_conjugateSpan _ _)
    (Source.conjugate_le_span hn)).trans (commutator_self_eq_bot_iff.mpr hab).le

/-- Correct a point conjugator by an element of the original seed normalizer. -/
theorem conjugate_centralizes_of_point_orbit
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (U : Set G)) V))
    (g l : G) (hl : l ∈ normalizer (V : Set G))
    (hU : U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj l).toMonoidHom) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hc : (U.map (MulAut.conj l).toMonoidHom).map
      (MulAut.conj l⁻¹).toMonoidHom = U := by
    rw [offender_map_conj_map, inv_mul_cancel]
    have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [he, map_id]
  have hn : l⁻¹ * g ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U.map (MulAut.conj (l⁻¹ * g)).toMonoidHom = U
    rw [← offender_map_conj_map, hU, hc]
  have hz : ⁅V, V.map (MulAut.conj (l⁻¹ * g)).toMonoidHom⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono (Source.le_conjugateSpan _ _)
      (Source.conjugate_le_span hn)).trans (commutator_self_eq_bot_iff.mpr hab).le
  apply (map_eq_bot_iff_of_injective _ (f := (MulAut.conj l⁻¹).toMonoidHom)
    (MulAut.conj l⁻¹).injective).mp
  have hlV : V.map (MulAut.conj l⁻¹).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hl)
  rw [map_commutator, hlV, offender_map_conj_map]
  exact hz

/-- Noncentrality of the generated weak closure has an actual conjugate witness. -/
theorem exists_noncentral_conjugate {T : Subgroup G}
    (hne : ⁅V, Source.weakClosureZero T V⁆ ≠ ⊥) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  classical
  by_contra h
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  apply sSup_le
  rintro A ⟨g, rfl, hg⟩
  have hz : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    by_contra hn
    exact h ⟨g, hg, hn⟩
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)

/-- A subgroup of a conjugate with corank below r has controlled centralizer. -/
theorem small_centralizer_normalizes (g : G) {B : Subgroup G} {n : ℕ}
    (hr : (n : ℕ∞) < globalR V)
    (hBA : B ≤ V.map (MulAut.conj g).toMonoidHom)
    (hb : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B ≤ n) :
    centralizer (B : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply centralizer_le_normalizer_of_corank_lt_globalR hBA
  rw [globalR_map_equiv]
  exact lt_of_le_of_lt (by exact_mod_cast hb) hr

/-- Centralizer generation converts non-normalization into a bound on r. -/
theorem globalR_le_of_centralizer_span (g : G) {n : ℕ}
    (hspan : V ≤ ⨆ (B : Subgroup G) (_ : B ≤ V.map (MulAut.conj g).toMonoidHom)
        (_ : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B ≤ n),
        V ⊓ centralizer (B : Set G))
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    globalR V ≤ n := by
  by_contra hr
  apply hn
  apply hspan.trans
  refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hB => ?_
  exact inf_le_right.trans (small_centralizer_normalizes g (lt_of_not_ge hr) hBA hB)

variable [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original centralizer in T lies in either local radical. -/
theorem sylow_centralizer_le_Ri {c : Coordinates D S.field} (f : InvariantFlag c)
    (i : Fin 2) : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ f.Ri i := by
  rw [seed_sylow_centralizer D S]
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G)))
  · have hT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
      rw [← seed_sylow_centralizer D S]
      exact inf_le_left
    exact hT.trans le_sup_right
  · have hsub : f.Li i ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
      sup_le_sup ((localResidual_le _).trans inf_le_left) le_rfl
    exact hsub.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- Commuting conjugates need no root calculation in the radical bound. -/
theorem weakClosure_le_Ri_of_noncentral_conjugates {c : Coordinates D S.field}
    (f : InvariantFlag c) (i : Fin 2)
    (h : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      V.map (MulAut.conj g).toMonoidHom ≤ f.Ri i) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri i := by
  apply sSup_le
  rintro A ⟨g, rfl, hg⟩
  by_cases hc : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥
  · exact (le_inf hg (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc))).trans (sylow_centralizer_le_Ri D S f i)
  · exact h g hg hc

/-- The exact G₂ clause of 11.2.2(5) excludes that marking under noncentrality. -/
theorem not_g2_of_noncentral_zero
    (hG2 : Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) →
      Source.weakClosureZero (T : Subgroup G) V ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hne : ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥) :
    ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) := by
  intro hm
  apply hne
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mpr ((hG2 hm).trans inf_le_right))

/-- The extra SL₃ assumption removes precisely the exceptional equality in
11.2.2(3), after the G₂ row has been excluded. -/
theorem strict_globalR_of_sl3_condition {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hr : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) :
    (S.field.degree : ℕ∞) < globalR V := by
  rcases hr with hr | ⟨hm, _, hc⟩
  · exact hr
  · exact (hc (hSL3 hm)).elim

variable {D S}

/-- The small symmetric-action configuration of the first claim in 11.2.4.
The join with C_V(L) expresses equality after the *original* quotient map;
it does not assert that the central extension splits. -/
structure SmallSymmetricAction {c : Coordinates D S.field} (f : InvariantFlag c)
    (A W : Subgroup G) : Prop where
  le_seed : W ≤ V
  quotient_line : ⁅W, A⁆ ⊔ (V ⊓ centralizer (L : Set G)) = f.Vi 0
  actor_corank : subgroupCorank A (A ⊓ centralizer (W : Set G)) = S.field.degree
  vector_corank : subgroupCorank W (W ⊓ centralizer (A : Set G)) = S.field.degree

/-- Uniform exclusion is essential: the parabolic argument replaces A by
L₂-conjugates inside R₂, which need not preserve the distinguished first line. -/
@[expose] def NoSmallActions {c : Coordinates D S.field} (f : InvariantFlag c) : Prop :=
  ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
    ∀ W, ¬ SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W

/-- The actual centralizer generation used to deduce 11.2.4(3) from (2). -/
@[expose] def CentralizerSpan (V A : Subgroup G) (n : ℕ) : Prop :=
  V ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : subgroupCorank A B ≤ n),
    V ⊓ centralizer (B : Set G)

/-- Align a marked preimage by an element of the original conjugate's normalizer.
This is an output of root/plane geometry, with literal ambient conjugators. -/
@[expose] def Alignment (U V : Subgroup G) (g : G) : Prop :=
  ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom = U

/-- Outputs of the parabolic offender calculation in the middle of 11.2.4.
This is an output specification, not an assumed source theorem. -/
structure ParabolicGeometry {c : Coordinates D S.field} (f : InvariantFlag c)
    (A : Subgroup G) : Prop where
  radical : A ≤ f.Ri 1
  quotient_plane : ⁅V, A⁆ ⊔ (V ⊓ centralizer (L : Set G)) = f.Vi 1
  fixed_plane : V ⊓ centralizer (A : Set G) = f.Vi 1
  centralizer_span : CentralizerSpan V A (2 * S.field.degree)

/-- The numerical bound forces the normalization needed to recognize a small
symmetric action on the conjugate module. No critical pair is assumed. -/
theorem SmallSymmetricAction.normalizes {c : Coordinates D S.field}
    {f : InvariantFlag c} {g : G} {W : Subgroup G}
    (h : SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W)
    (hr : (S.field.degree : ℕ∞) < globalR V) :
    W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  exact (le_centralizer_iff.mpr inf_le_right).trans
    (small_centralizer_normalizes g hr inf_le_left h.actor_corank.le)

/-- Root recognition and line transitivity exclude the small symmetric action.
The geometric recognition premise still has to be proved; this theorem only
performs the numerical normalization and the abelian-span contradiction. -/
theorem no_smallAction_of_alignment {c : Coordinates D S.field} (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hr : (S.field.degree : ℕ∞) < globalR V) (g : G)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hroot : ∀ W : Subgroup G,
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W →
      W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 0) V g) :
    ∀ W : Subgroup G, ¬ SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W := by
  intro W hW
  obtain ⟨x, hx, hline⟩ := hroot W hW (hW.normalizes hr)
  exact hne (conjugate_centralizes_of_point_alignment hab g x hx hline)

/-- The actual L₂ point orbit turns plane alignment into centralization.
The orbit input is the preceding 11.1.3/Sylow fixed-point geometry. -/
theorem centralizes_of_plane_alignment {c : Coordinates D S.field} (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (horbit : ∀ y ∈ normalizer (f.Vi 1 : Set G), ∃ l ∈ f.Li 1,
      (f.Vi 0).map (MulAut.conj y).toMonoidHom =
        (f.Vi 0).map (MulAut.conj l).toMonoidHom)
    (g : G) (ha : Alignment (f.Vi 1) V g) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨x, hx, hplane⟩ := ha
  have hy : x * g ∈ normalizer (f.Vi 1 : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (f.Vi 1).map (MulAut.conj (x * g)).toMonoidHom = f.Vi 1
    rwa [← offender_map_conj_map]
  obtain ⟨l, hl, he⟩ := horbit (x * g) hy
  have hlV : l ∈ normalizer (V : Set G) :=
    D.normalizes ((localResidual_le _).trans inf_le_left hl)
  have hz := conjugate_centralizes_of_point_orbit hab (x * g) l hlV he
  have hxA : (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = V.map (MulAut.conj g).toMonoidHom :=
    mem_normalizer_iff_map_conj_eq.mp hx
  rw [← offender_map_conj_map, hxA] at hz
  exact hz

/-- The image condition in `SmallSymmetricAction` uses the literal coordinate
projection. It adds the full kernel, without choosing a complement. -/
theorem quotient_image_eq_iff {c : Coordinates D S.field} {B : Subgroup G}
    (hB : B ≤ V) (U : Submodule S.field.Carrier c.Space) :
    (B.subgroupOf V).map c.projection = U.toAddSubgroup.toSubgroup ↔
      B ⊔ (V ⊓ centralizer (L : Set G)) = c.preimage U := by
  have hk : c.projection.ker.map V.subtype = V ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩
    · rintro ⟨hxV, hxC⟩
      exact ⟨⟨x, hxV⟩, (c.projection_eq_one_iff ⟨x, hxV⟩).mpr hxC, rfl⟩
  have hp : c.preimage U =
      (U.toAddSubgroup.toSubgroup.comap c.projection).map V.subtype := by
    rfl
  constructor
  · intro h
    have he := congrArg (fun Q : Subgroup (Multiplicative c.Space) =>
      (Q.comap c.projection).map V.subtype) h
    rwa [comap_map_eq, Subgroup.map_sup, map_subgroupOf_eq_of_le hB, hk, ← hp] at he
  · intro h
    apply comap_injective c.projection_surjective
    apply map_injective V.subtype_injective
    rwa [comap_map_eq, Subgroup.map_sup, map_subgroupOf_eq_of_le hB, hk, ← hp]

variable (D S)

/-- Conjugation of Sylow fixed spaces gives the actual point orbit needed at
the end of the proof. Relative component normality and the marked fixed-space
identity are precisely the earlier-source inputs. -/
theorem point_orbit_of_sylow_fixed {c : Coordinates D S.field} (f : InvariantFlag c)
    (hN : normalizer (f.Vi 1 : Set G) ≤ normalizer (f.Li 1 : Set G))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G)) :
    ∀ y ∈ normalizer (f.Vi 1 : Set G), ∃ l ∈ f.Li 1,
      (f.Vi 0).map (MulAut.conj y).toMonoidHom =
        (f.Vi 0).map (MulAut.conj l).toMonoidHom := by
  intro y hy
  let K := f.Li 1
  let e : MulAut K := K.normalizerMonoidHom ⟨y, hN hy⟩
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq K P (e • P)
  have hP : (P : Subgroup K).map (MulAut.conj l).toMonoidHom =
      (P : Subgroup K).map e.toMonoidHom := by
    exact congrArg (fun Q : Sylow 2 K => (Q : Subgroup K)) hl
  have hPa : ((P : Subgroup K).map K.subtype).map
      (MulAut.conj (l : G)).toMonoidHom =
      ((P : Subgroup K).map K.subtype).map (MulAut.conj y).toMonoidHom := by
    have he := congrArg (fun B : Subgroup K => B.map K.subtype) hP
    have hlc : K.subtype.comp (MulAut.conj l).toMonoidHom =
        (MulAut.conj (l : G)).toMonoidHom.comp K.subtype := by
      ext x
      rfl
    have hyc : K.subtype.comp e.toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp K.subtype := by
      ext x
      rfl
    rw [map_map, map_map, hlc, hyc] at he
    simpa only [map_map] using he
  have hmap (z : G) (hz : z ∈ normalizer (f.Vi 1 : Set G)) :
      (f.Vi 0).map (MulAut.conj z).toMonoidHom = f.Vi 1 ⊓
        centralizer (((P : Subgroup K).map K.subtype).map
          (MulAut.conj z).toMonoidHom : Set G) := by
    have hzV : (f.Vi 1).map (MulAut.conj z).toMonoidHom = f.Vi 1 :=
      mem_normalizer_iff_map_conj_eq.mp hz
    rw [hfix, map_inf _ _ _ (MulAut.conj z).injective, hzV]
    rw [Theory.GroupTheory.map_centralizer_equiv]
    rfl
  refine ⟨l, l.property, ?_⟩
  rw [hmap y hy, hmap l ((localResidual_le _).trans inf_le_right l.property), hPa]

omit [Finite G] in
/-- Uniqueness is applied inside N_G(U), not in the ambient group G. -/
theorem normalizes_component_of_unique_noncentral {U K : Subgroup G}
    (h : Source.UniqueNoncentralComponent (normalizer (U : Set G)) U K) :
    normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  let H := normalizer (U : Set G)
  let e : H ≃* H := MulAut.conj (⟨g, hg⟩ : H)
  let J := (K.subgroupOf H).map e.toMonoidHom
  have hKH : K ≤ H := h.1.1.1
  have hJ : J.IsCComponent := h.1.1.2.map_equiv e
  have he : J.map H.subtype = K.map (MulAut.conj g).toMonoidHom := by
    change ((K.subgroupOf H).map e.toMonoidHom).map H.subtype = _
    rw [map_map]
    have hcomp : H.subtype.comp e.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    rw [hcomp, ← map_map, map_subgroupOf_eq_of_le hKH]
  have hc : Source.ComponentIn H (J.map H.subtype) := by
    refine ⟨map_subtype_le _, ?_⟩
    change ((J.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hn : ¬ J.map H.subtype ≤ centralizer (U : Set G) := by
    rw [he]
    intro hcentral
    apply h.1.2
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply (map_eq_bot_iff_of_injective _ (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    have hU : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rw [map_commutator, hU]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact he.symm.trans (h.2 _ ⟨hc, hn⟩)

/-- The point-orbit input is supplied by the literal relative-component
conclusion 11.1.3 and the preceding Sylow fixed-space identity. -/
theorem point_orbit_of_unique_component {c : Coordinates D S.field} (f : InvariantFlag c)
    (hK : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G)) :
    ∀ y ∈ normalizer (f.Vi 1 : Set G), ∃ l ∈ f.Li 1,
      (f.Vi 0).map (MulAut.conj y).toMonoidHom =
        (f.Vi 0).map (MulAut.conj l).toMonoidHom :=
  point_orbit_of_sylow_fixed D S f (normalizes_component_of_unique_noncentral hK) P hfix


/-- Conditional assembly of the three source conclusions. The two root-action
recognition steps and the parabolic calculation are still explicit premises;
this theorem is not a proof of 11.2.4 until their owners discharge them.
The SL₃ hypothesis is retained and used in the strict-rank deduction. -/
theorem conclusions_of_geometry {c : Coordinates D S.field} (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hW : ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hK : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G))
    (hroot : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ∀ W : Subgroup G, SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W →
      W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 0) V g)
    (hparabolic : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom))
    (hplane : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) →
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 1) V g) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  have horbit := point_orbit_of_unique_component D S f hK P hfix
  have hr := strict_globalR_of_sl3_condition D S f hSL3 hparameters
  have hsmall : NoSmallActions f := by
    intro g hg hne
    exact no_smallAction_of_alignment f hab hr g hne (hroot g hg hne)
  have hp (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
      (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :=
    hparabolic g hg hne hsmall
  have hn (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
      (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
      ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    intro hn
    exact hne (centralizes_of_plane_alignment f hab horbit g
      (hplane g hg hne hsmall (hp g hg hne) hn))
  refine ⟨weakClosure_le_Ri_of_noncentral_conjugates D S f 1
    (fun g hg hne => (hp g hg hne).radical), hn, ?_⟩
  obtain ⟨g, hg, hne⟩ := exists_noncentral_conjugate hW
  exact globalR_le_of_centralizer_span g (hp g hg hne).centralizer_span (hn g hg hne)

/-- Actual application to the constructed F.7 critical pair. Its remaining
premises are the displayed geometric outputs, not a non-normalization callback.
This conditional consumer does not complete the source theorem. -/
theorem obstruction_of_geometry {c : Coordinates D S.field} (f : InvariantFlag c)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hK : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G))
    (hroot : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ∀ W : Subgroup G, SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W →
      W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 0) V g)
    (hparabolic : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom))
    (hplane : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) →
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 1) V g) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL3' hab hW
  exact (conclusions_of_geometry D S f hab hW hSL3' hparameters hK P hfix
    hroot hparabolic hplane).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
