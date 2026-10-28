module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Fixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition

/-!
# Excluding proper plane displacement in the original conjugate pair

E.3.7 bounds the actual actor corank from below. In the symplectic row,
a proper displacement in the fixed plane is a field line, and orthogonal
fixed-space duality computes both literal centralizer indices, retaining
the entire nonsplit central cover. Reciprocal root recognition identifies
the commutator as a complete field-line preimage on both original modules.

Two conjugates sharing such a line centralize each other: move each line
by its own component and apply the abelian first-line normalizer span.
In the SL3 row the projection is injective. Proper displacement again is
a field line; its displacement homomorphisms and r(G,V)>n first give the
reciprocal normalization, and the existing small-commutator calculation
recognizes the line on the conjugate module. This avoids an unnecessary
rechoice of the conjugate inside the plane residual.

The actual parabolic consumer discharges the proper-displacement callback.
Its outside-radical calculation remains with this nonnormalization owner.
The earlier radical action inputs belong to qt-d-1222-natural-flag-cartan;
the globalS and globalR inputs belong to qt-d-1222-natural-weak-parameters.
Their final discharge stays with qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, 11.2.4, printed p.769; E.3.7, printed p.232,
and the nonsplit root-cover calculation I.2.3(1b), printed p.413.
-/
public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Direct E.3.7 lower bound for the literal action kernel in either remaining branch. -/
theorem actor_corank_lower_of_noncentral [IsElementaryAbelian 2 V]
    (hs : globalS V = S.field.degree) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (W : Subgroup G) (hWV : W ≤ V)
    (hne : ⁅W,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    S.field.degree ≤ subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (W : Set G)) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := A ⊓ centralizer (W : Set G)
  by_contra hn
  have hlt : subgroupCorank A B < S.field.degree := Nat.lt_of_not_ge hn
  have hb : (subgroupCorank A B : ℕ∞) < globalS V := by
    rw [hs]
    exact_mod_cast hlt
  have hBN : B ≤ A ⊓ normalizer (V : Set G) :=
    le_inf inf_le_left (inf_le_left.trans (hg.trans S.sylow_normalizes))
  have he := lemma_E_3_7 g hBN hb
  have hw : W ≤ V ⊓ centralizer (B : Set G) :=
    le_inf hWV (le_centralizer_iff.mpr inf_le_right)
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    ((hw.trans he.le).trans inf_le_right))

open NormalizedPlane.TransvectionFree

/-- A proper nonzero displacement in the marked plane
has dimension one and the actual actor has corank n. -/
theorem sp4_proper_displacement_corank
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    [IsElementaryAbelian 2 V]
    (hs : globalS V=S.field.degree) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hsq : ∀ a : V.map (MulAut.conj g).toMonoidHom,a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hproper : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔
      (V ⊓ centralizer (L:Set G)) ≠ f.Vi 1) :
    Module.finrank S.field.Carrier (displacementSpace
      (planeHom m f (hg.trans S.sylow_normalizes) hsq hfix).range)=1 ∧
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V:Set G))=S.field.degree := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let hA := hg.trans S.sylow_normalizes
  let c := Coordinates.sp4 m
  let actor := planeHom m f hA hsq hfix
  let U := displacementSpace actor.range
  let ρ : Representation S.field.Carrier A (Vector S.field.Carrier) :=
    (symplecticNatural 2).comp actor
  let : FiniteDimensional S.field.Carrier (Coordinates.sp4 m).Space :=
    inferInstanceAs (FiniteDimensional S.field.Carrier (Vector S.field.Carrier))
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj g).toMonoidHom
  have hlower := actor_corank_lower_of_noncentral (S := S) hs g hg V le_rfl hne
  have hcard := planeHom_card m f hA hsq hfix
  have hπ : ∀ (a : A) (v : V), ρ a (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd := by
    intro a v
    exact (LinearEquiv.congr_fun (planeHom_quotient m f hA hsq hfix a)
      (c.projection v).toAdd).trans (quotientAction_projection D S m (inclusion hA a) v)
  have hPfix (a : A) (x : Vector S.field.Carrier) (hx : x∈f.space 1) :
      actor a • x=x := by
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    have hp : (v:G)∈f.Vi 1 := (c.mem_preimage _ v).mpr (by
      change (c.projection v).toAdd∈f.space 1
      rwa [hv])
    have hh := (sp4_projection_fixed_iff_commute m A actor
      (planeHom_action m f hA hsq hfix) a v).mpr (hfix hp a.val a.property)
    have hv' : (show Vector S.field.Carrier from (c.projection v).toAdd)=x :=
      congrArg Multiplicative.toAdd hv
    exact (congrArg (actor a • ·) hv'.symm).trans (hh.trans hv')
  have hle : U≤f.space 1 := by
    change displacementSpace actor.range≤_
    rw [displacementSpace_range_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,x⟩,rfl⟩
    exact displacement_mem_of_self_orthogonal (f.space 1)
      (flag_plane_self_orthogonal m f) (actor a) (hPfix a) x
  have hneP : U≠f.space 1 := by
    intro he
    apply hproper
    have hh := preimage_displacement_eq_commutator_sup (c := c) (S := S) hA ρ hπ
    rw [←displacementSpace_range_eq] at hh
    exact hh.symm.trans (congrArg c.preimage he)
  have hlt : Module.finrank S.field.Carrier U<2 := by
    have hh := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hneP)
    have hf : Module.finrank S.field.Carrier (f.space 1)=2 := f.dimension 1
    exact hh.trans_le hf.le
  have hbound := card_actor_le_displacement_dimension actor.range
  have hd0 : Module.finrank S.field.Carrier U≠0 := by
    intro hz
    change Nat.card actor.range≤Nat.card S.field.Carrier^(Module.finrank S.field.Carrier U)^2 at hbound
    rw [hz] at hbound
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,pow_zero] at hbound
    have hh : 2^S.field.degree≤Nat.card actor.range := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide) hlower
    have hp : 1<2^S.field.degree := one_lt_pow₀ (by decide) (Nat.ne_of_gt S.field.degree_pos)
    omega
  have hd : Module.finrank S.field.Carrier U=1 := by omega
  refine ⟨hd,le_antisymm ?_ hlower⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp
  rw [←hcard,←S.field.card_eq]
  simpa only [show Module.finrank S.field.Carrier (displacementSpace actor.range)=1 from hd,
    one_pow,pow_one] using hbound

/-- The entire nonsplit cover has the same moving index as its natural quotient. -/
theorem sp4_centralizer_index
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (A : Subgroup G) (actor : A →* Sp S.field.Carrier)
    (action_eq : ∀ (a : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (actor a) v)) : G) =
        (a : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(a : G)⁻¹) :
    (centralizer (A : Set G)).relIndex V =
      Nat.card S.field.Carrier ^ Module.finrank S.field.Carrier (displacementSpace actor.range) := by
  let P := TwoLocalCover.fixedSpace actor.range
  let π : V →* Multiplicative (Vector S.field.Carrier) := (Coordinates.sp4 m).projection
  let φ : V →* Multiplicative (Vector S.field.Carrier ⧸ P) :=
    P.mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨w,hw⟩ := P.mkQ_surjective v.toAdd
    obtain ⟨u,hu⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd w)
    refine ⟨u,?_⟩
    change Multiplicative.ofAdd (P.mkQ (π u).toAdd)=v
    change π u=Multiplicative.ofAdd w at hu
    rw [hu,toAdd_ofAdd,hw,ofAdd_toAdd]
  have hk : φ.ker = (centralizer (A:Set G)).subgroupOf V := by
    ext v
    change Submodule.Quotient.mk ((π v).toAdd)=(0:Vector S.field.Carrier ⧸ P) ↔ (v:G)∈centralizer (A:Set G)
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hv
      apply mem_centralizer_iff.mpr
      intro a ha
      exact (sp4_projection_fixed_iff_commute m A actor action_eq ⟨a,ha⟩ v).mp
        (hv (actor ⟨a,ha⟩) ⟨⟨a,ha⟩,rfl⟩)
    · intro hv
      rintro _ ⟨a,rfl⟩
      exact (sp4_projection_fixed_iff_commute m A actor action_eq a v).mpr
        (mem_centralizer_iff.mp hv a.val a.property)
  change ((centralizer (A:Set G)).subgroupOf V).index=_
  rw [←hk,index_ker,φ.range_eq_top_of_surjective hφ]
  have hc := Nat.card_congr (topEquiv :
    (⊤ : Subgroup (Multiplicative (Vector S.field.Carrier ⧸ P))) ≃* _).toEquiv
  exact hc.trans (fixed_quotient_card actor.range)

/-- The proper-displacement case has both of the source's literal coranks n. -/
theorem sp4_proper_displacement_indices
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    [IsElementaryAbelian 2 V]
    (hs : globalS V=S.field.degree) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hsq : ∀ a : V.map (MulAut.conj g).toMonoidHom,a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hproper : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔
      (V ⊓ centralizer (L:Set G)) ≠ f.Vi 1) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V:Set G))=S.field.degree ∧
    subgroupCorank V (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom:Set G))=
      S.field.degree := by
  obtain ⟨hd,ha⟩ := sp4_proper_displacement_corank m f hs g hg hne hsq hfix hproper
  refine ⟨ha,?_⟩
  let actor := planeHom m f (hg.trans S.sylow_normalizes) hsq hfix
  have hi := sp4_centralizer_index m _ actor
    (planeHom_action m f (hg.trans S.sylow_normalizes) hsq hfix)
  rw [hd,pow_one,S.field.card_eq] at hi
  apply (Nat.pow_right_injective (by decide : 2≤(2:ℕ)))
  change 2^subgroupCorank V (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom:Set G))=2^S.field.degree
  rw [subgroupCorank_eq_quotient_finrank,←relIndex_eq_two_pow_quotient_finrank,
    inf_relIndex_left,hi]

/-- Two conjugates sharing a complete marked field line centralize each other.
Both line conjugators stay in their original components. -/
theorem centralizes_of_common_field_line {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0:Set G)) V))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (U W : Submodule S.field.Carrier c.Space)
    (hU : Module.finrank S.field.Carrier U=1)
    (hW : Module.finrank S.field.Carrier W=1)
    (hcommon : c.preimage U=(c.preimage W).map (MulAut.conj g).toMonoidHom) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  obtain ⟨l,hl⟩ := field_line_orbit c hG2 (f.space 0) U (f.dimension 0) hU
  obtain ⟨k,hk⟩ := field_line_orbit c hG2 (f.space 0) W (f.dimension 0) hW
  have hline : (f.Vi 0).map (MulAut.conj (g*(k:G))).toMonoidHom=
      (f.Vi 0).map (MulAut.conj (l:G)).toMonoidHom := by
    change (c.preimage (f.space 0)).map (MulAut.conj (g*(k:G))).toMonoidHom=
      (c.preimage (f.space 0)).map (MulAut.conj (l:G)).toMonoidHom
    rw [←offender_map_conj_map,hk,←hcommon,hl]
  have hz := conjugate_centralizes_of_point_orbit hab (g*(k:G)) l
    (D.normalizes l.property) hline
  have hkV : V.map (MulAut.conj (k:G)).toMonoidHom=V :=
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes k.property)
  rwa [←offender_map_conj_map,hkV] at hz

omit [Finite G] in
private theorem inverse_conjugate_cancel (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom=B := by
  rw [offender_map_conj_map,inv_mul_cancel]
  have he : (MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G := by ext; simp
  rw [he,map_id]

/-- Symmetric indices recognize a common field line on the two original covers. -/
theorem sp4_centralizes_of_small_indices
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0:Set G)) V))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hr : (S.field.degree:ℕ∞)<globalR V)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (ha : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V:Set G))=S.field.degree)
    (hv : subgroupCorank V (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom:Set G))=
      S.field.degree) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := V.map (MulAut.conj g⁻¹).toMonoidHom
  letI := D.elementary
  letI : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  letI : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hsqA : ∀a:A,a^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A)
  have hsqB : ∀b:B,b^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 B)
  have hn : V≤normalizer (A:Set G) :=
    (le_centralizer_iff.mpr (inf_le_right : A ⊓ centralizer (V:Set G)≤_)).trans
      (small_centralizer_normalizes g hr inf_le_left ha.le)
  have hcomm : ⁅B,V⁆=(⁅V,A⁆).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [map_commutator,inverse_conjugate_cancel]
  have hBV : B≤normalizer (V:Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [hcomm]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (le_normalizer_iff_commutator_le_right.mp hn)
    rwa [inverse_conjugate_cancel] at hh
  have hC : (A ⊓ centralizer (V:Set G)).map (MulAut.conj g⁻¹).toMonoidHom=
      V ⊓ centralizer (B:Set G) := by
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,inverse_conjugate_cancel,
      Theory.GroupTheory.map_centralizer_equiv]
    rfl
  have hC' : (V ⊓ centralizer (A:Set G)).map (MulAut.conj g⁻¹).toMonoidHom=
      B ⊓ centralizer (V:Set G) := by
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Theory.GroupTheory.map_centralizer_equiv]
    change B ⊓ centralizer (A.map (MulAut.conj g⁻¹).toMonoidHom:Set G)=_
    rw [inverse_conjugate_cancel]
  have hiA : (centralizer (A:Set G)).relIndex V=Nat.card S.field.Carrier := by
    rw [←inf_relIndex_left V,relIndex_eq_two_pow_quotient_finrank,
      ←subgroupCorank_eq_quotient_finrank,hv,S.field.card_eq]
  have hiB : (centralizer (B:Set G)).relIndex V=Nat.card S.field.Carrier := by
    rw [←inf_relIndex_left V,←hC]
    have hc : V=A.map (MulAut.conj g⁻¹).toMonoidHom := (inverse_conjugate_cancel V g).symm
    conv_lhs => arg 2; rw [hc]
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,
      relIndex_eq_two_pow_quotient_finrank,←subgroupCorank_eq_quotient_finrank,
      ha,S.field.card_eq]
  have hrB : subgroupCorank B (B ⊓ centralizer (V:Set G))=S.field.degree := by
    rw [←hC',subgroupCorank,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hv
  obtain ⟨U,hU,hUeq⟩ := Recognition.commutator_field_line_of_small_indices m
    (hg.trans S.sylow_normalizes) hsqA hiA.le ha
  obtain ⟨W,hW,hWeq⟩ := Recognition.commutator_field_line_of_small_indices m hBV hsqB hiB.le hrB
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) hWeq
  rw [hcomm] at hh
  have hc : ((⁅V,A⁆).map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom=⁅V,A⁆ := by
    simpa only [inv_inv] using inverse_conjugate_cancel ⁅V,A⁆ g⁻¹
  rw [hc,commutator_comm V A,hUeq] at hh
  exact centralizes_of_common_field_line f hab hG2 g U W hU hW hh

/-- Proper symplectic displacement contradicts the abelian first-line span. -/
theorem sp4_quotient_plane_of_radical
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0:Set G)) V))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    [IsElementaryAbelian 2 V] (hs : globalS V=S.field.degree)
    (hr : (S.field.degree:ℕ∞)<globalR V)
    (hradical : f.Ri 1≤centralizer (f.Vi 1:Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥)
    (hR : V.map (MulAut.conj g).toMonoidHom≤f.Ri 1) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L:Set G))=f.Vi 1 := by
  by_contra hp
  let A := V.map (MulAut.conj g).toMonoidHom
  letI : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hsq : ∀a:A,a^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A)
  have hfix : f.Vi 1≤centralizer (A:Set G) := le_centralizer_iff.mpr (hR.trans hradical)
  obtain ⟨ha,hv⟩ := sp4_proper_displacement_indices m f hs g hg hne hsq hfix hp
  exact hne (sp4_centralizes_of_small_indices m f hab hG2 hr g hg ha hv)

omit [Finite G] in
/-- Fixed displacements of size at most 2ⁿ put every original vector in the
normalizer of the conjugate when r(G,V)>n. -/
theorem normalizes_of_fixed_displacements
    {F X : Type*} [Field F] [Finite F] [AddCommGroup X] [Module F X] [Finite X]
    (g : G) (p : V →* Multiplicative X)
    (ρ : Representation F (V.map (MulAut.conj g).toMonoidHom) X)
    (P : Submodule F X) (n : ℕ) (hcard : Nat.card P≤2^n)
    (hmove : ∀a, ∀x:X, ρ a x-x∈P)
    (hfix : ∀a, ∀x∈P, ρ a x=x)
    (hlift : ∀a (v:V), ρ a (p v).toAdd=(p v).toAdd →
      (a:G)*(v:G)=(v:G)*(a:G))
    (hr : (n:ℕ∞)<globalR V) :
    V≤normalizer (V.map (MulAut.conj g).toMonoidHom:Set G) := by
  intro v hv
  let A := V.map (MulAut.conj g).toMonoidHom
  let w := (p ⟨v,hv⟩).toAdd
  let δ : A →* Multiplicative P := {
    toFun a := Multiplicative.ofAdd ⟨ρ a w-w,hmove a w⟩
    map_one' := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simp
    map_mul' a b := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change ρ (a*b) w-w=(ρ a w-w)+(ρ b w-w)
      rw [map_mul,Module.End.mul_apply]
      have he := hfix a (ρ b w-w) (hmove b w)
      rw [map_sub] at he
      calc
        ρ a (ρ b w)-w=(ρ a (ρ b w)-ρ a w)+(ρ a w-w) := by abel
        _=(ρ a w-w)+(ρ b w-w) := by rw [he]; abel }
  have hk : δ.ker≤(centralizer ({v}:Set G)).subgroupOf A := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply hlift a ⟨v,hv⟩
    apply sub_eq_zero.mp
    exact congrArg (fun x : Multiplicative P => x.toAdd.val) ha
  have hi : (centralizer ({v}:Set G)).relIndex A≤2^n := by
    calc
      (centralizer ({v}:Set G)).relIndex A≤δ.ker.index := by
        have hh := relIndex_le_of_le_left (L := (⊤:Subgroup A)) hk index_ne_zero_of_finite
        change ((centralizer ({v}:Set G)).subgroupOf A).index≤δ.ker.index
        simpa only [relIndex_top_right] using hh
      _=Nat.card δ.range := index_ker δ
      _≤Nat.card (Multiplicative P) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _=Nat.card P := Nat.card_congr Multiplicative.toAdd
      _≤2^n := hcard
  let B := A ⊓ centralizer ({v}:Set G)
  have hB : subgroupCorank A B≤n := by
    unfold subgroupCorank
    rw [inf_relIndex_left]
    have hh := Nat.log_mono_right (b := 2) hi
    simpa only [Nat.log_pow (by decide : 1<2)] using hh
  apply small_centralizer_normalizes g hr (show B≤A from inf_le_left) hB
  apply mem_centralizer_iff.mpr
  intro a ha
  exact mem_centralizer_singleton_iff.mp ha.2

/-- A proper displacement in the SL₃ plane is a common field line on both
original modules, contradicting the abelian first-line normalizer span. -/
theorem sl3_quotient_plane_of_radical
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0:Set G)) V))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hr : (S.field.degree:ℕ∞)<globalR V)
    (hradical : f.Ri 1≤centralizer (f.Vi 1:Set G))
    (hmoveR : ⁅V,f.Ri 1⁆≤f.Vi 1)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥)
    (hR : V.map (MulAut.conj g).toMonoidHom≤f.Ri 1) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L:Set G))=f.Vi 1 := by
  by_contra hp
  let c := Coordinates.sl3 m
  let A := V.map (MulAut.conj g).toMonoidHom
  let hA := hg.trans S.sylow_normalizes
  letI : Finite c.Space := inferInstanceAs (Finite (Fin 3 → S.field.Carrier))
  letI : FiniteDimensional S.field.Carrier c.Space :=
    inferInstanceAs (FiniteDimensional S.field.Carrier (Fin 3 → S.field.Carrier))
  have hfix : f.Vi 1≤centralizer (A:Set G) := le_centralizer_iff.mpr (hR.trans hradical)
  let ρ := sl3PlaneAction m f hA hfix
  let U := Coinvariants.ker ρ
  have hfixed := Preliminary.sl3_centralizer_eq_bot D S m
  have hπ : Function.Injective c.projection := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro v hv
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfixed]
    exact ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩
  have hpre : c.preimage U=⁅V,A⁆ := by
    rw [preimage_displacement_eq_commutator_sup (S := S) hA ρ
      (sl3PlaneAction_projection m f hA hfix),hfixed,sup_bot_eq]
  have hUP : U≤f.space 1 := by
    apply (c.preimage_le_iff _ _).mp
    rw [hpre]
    exact (commutator_mono (le_rfl : V≤V) hR).trans hmoveR
  have hU0 : U≠⊥ := by
    intro hz
    rw [hz,c.preimage_bot,hfixed] at hpre
    exact hne hpre.symm
  have hUPne : U≠f.space 1 := by
    intro he
    apply hp
    rw [hfixed,sup_bot_eq,←hpre,he]
    rfl
  have hd : Module.finrank S.field.Carrier U=1 := by
    have hlo : Module.finrank S.field.Carrier U≠0 :=
      fun hz => hU0 (Submodule.finrank_eq_zero.mp hz)
    have hhi := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hUP hUPne)
    rw [f.dimension] at hhi
    omega
  have hρfix (a:A) (x:c.Space) (hx:x∈f.space 1) : ρ a x=x := by
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    have hvP : (v:G)∈f.Vi 1 := (c.mem_preimage _ v).mpr (by
      change (c.projection v).toAdd∈f.space 1
      rwa [hv])
    have he : V.normalizerMonoidHom (inclusion hA a) v=v := by
      apply Subtype.ext
      change (a:G)*(v:G)*(a:G)⁻¹=(v:G)
      rw [hfix hvP a.val a.property,mul_inv_cancel_right]
    have hh := sl3PlaneAction_projection m f hA hfix a v
    rw [he,hv] at hh
    exact hh
  have hn : V≤normalizer (A:Set G) := by
    apply normalizes_of_fixed_displacements g c.projection ρ U S.field.degree
    · rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier),hd,pow_one,S.field.card_eq]
    · intro a x
      exact Coinvariants.sub_mem_ker a x
    · intro a x hx
      exact hρfix a x (hUP hx)
    · intro a v hh
      rw [sl3PlaneAction_projection] at hh
      have he := hπ (Multiplicative.toAdd.injective hh)
      have he' := congrArg Subtype.val he
      change (a:G)*(v:G)*(a:G)⁻¹=(v:G) at he'
      exact mul_inv_eq_iff_eq_mul.mp he'
    · exact hr
  let B := V.map (MulAut.conj g⁻¹).toMonoidHom
  have hcomm : ⁅B,V⁆=(⁅V,A⁆).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [map_commutator,inverse_conjugate_cancel]
  have hBV : B≤normalizer (V:Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [hcomm]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (le_normalizer_iff_commutator_le_right.mp hn)
    rwa [inverse_conjugate_cancel] at hh
  letI := D.elementary
  letI : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hsq : ∀b:B,b^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 B)
  have hnB : ⁅B,V⁆≠⊥ := by
    rw [hcomm]
    intro hz
    exact hne ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp hz)
  have hcard : Nat.card (⁅B,V⁆:Subgroup G)≤Nat.card S.field.Carrier := by
    rw [hcomm,card_map_of_injective (MulAut.conj g⁻¹).injective,←hpre,
      Closure.Nonabelian.card_preimage (.sl3 m) hfixed,hd,pow_one,S.field.card_eq]
  let E : Closure.Geometry D :=
    { input := S
      point := c.binarySubspace (f.space 0)
      plane := c.binarySubspace (f.space 1)
      threeSpace := c.binarySubspace (f.space 2)
      X := ⊥,z := g,H := ⊥ }
  obtain ⟨W,hW,hWeq⟩ := Closure.Amalgam.Even.Linear.commutator_isFieldLine_of_card_le
    (E := E) m hfixed B hBV hsq hnB hcard
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) hWeq
  rw [hcomm] at hh
  have hc : ((⁅V,A⁆).map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom=⁅V,A⁆ := by
    simpa only [inv_inv] using inverse_conjugate_cancel ⁅V,A⁆ g⁻¹
  rw [hc,←hpre] at hh
  exact hne (centralizes_of_common_field_line f hab hG2 g U W hd hW hh.symm)

/-- Proper displacement is excluded in both surviving natural rows. The
SL₃ radical displacement is the exact earlier flag-action input. -/
theorem quotient_plane_of_radical {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0:Set G)) V))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hs : @globalS G _ V D.elementary=S.field.degree)
    (hr : (S.field.degree:ℕ∞)<globalR V)
    (hradical : f.Ri 1≤centralizer (f.Vi 1:Set G))
    (hmoveSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V,f.Ri 1⁆≤f.Vi 1)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥)
    (hR : V.map (MulAut.conj g).toMonoidHom≤f.Ri 1) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L:Set G))=f.Vi 1 := by
  let := D.elementary
  cases c with
  | sl3 m =>
    exact sl3_quotient_plane_of_radical m f hab hG2 hr hradical (hmoveSL3 ⟨m⟩) g hg hne hR
  | sp4 m => exact sp4_quotient_plane_of_radical m f hab hG2 hs hr hradical g hg hne hR
  | g2 m => exact (hG2 ⟨m⟩).elim

/-- The parabolic geometry now has only its outside-radical calculation left.
The proper-displacement, fixed-plane and centralizer-generation steps are proved. -/
theorem parabolic_of_outside_calculation {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0:Set G)) V))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hs : @globalS G _ V D.elementary=S.field.degree)
    (hr : (S.field.degree:ℕ∞)<globalR V)
    (hradical : f.Ri 1≤centralizer (f.Vi 1:Set G))
    (hmoveSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V,f.Ri 1⁆≤f.Vi 1)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) (hsmall : NoSmallActions f)
    (houtside : ¬V.map (MulAut.conj g).toMonoidHom≤f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1)) :
    ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) := by
  apply parabolic_of_two_calculations f hG2 hradical g hg hne hsmall houtside
  intro hR hp
  exact (hp (quotient_plane_of_radical f hab hG2 hs hr hradical hmoveSL3 g hg hne hR)).elim


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
