module

public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.SectionOne.OneSevenSmallSylow
public import Stellmacher.SectionOne.CThreeCtwoSLTwo
public import Stellmacher.PushingUp.FaithfulFourNaturalAction
public import Theory.GroupAction.Quotient

/-!
# The finite `SL₂(2)` pushing-up module lemma

This module proves the `p = 2`, `n = 1` specialization of Stellmacher's
pushing-up module lemma.  For a faithful elementary-abelian module, the
trivial 2-core and the inherited nested-Frattini `SL₂(2)` condition force a
nontrivial quadratic subgroup satisfying the fixed-space cardinal bound to be
the Sylow 2-subgroup.  The acting group is `SL₂(2)`, its action on the
quotient by the global fixed space is the natural two-dimensional action, and
the Sylow fixed space is the product of its commutator line and the global
fixed space.

The proof first derives the equality case of the Section-One offender bound.
It shows that `oneE` is the whole acting group, identifies the unique
one-seven factor, and applies the resulting invariant fixed/commutator
decomposition. The shared faithful four-element recognition theorem identifies
the natural action on the commutator complement. This action is transferred to
the actual fixed-space quotient; the natural Sylow-line identity then gives
the last conclusion.  Section One's assembly API uses one
universe for the actor and module, so the public independent-universe theorem
passes through `ULift` and transports every hypothesis and conclusion along
the canonical group equivalences.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma (2.1),
specialized to `p = 2`, `n = 1`; the proof there cites B. Stellmacher,
*A pushing up result*, J. Algebra 83 (1983), (1.1).  The explicit trivial
2-core hypothesis is the faithful barred form used by the source application;
without it the deleted permutation module for `S₄` is a counterexample.
-/

open scoped IsMulCommutative Pointwise

namespace Stellmacher.PushingUp

universe u v

private theorem elementaryAbelian_subgroup
    {V : Type u} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (show (x : V) * (y : V) = (y : V) * (x : V) from
        (IsMulCommutative.is_comm (M := V)).comm x y)⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

private theorem elementaryAbelian_ulift
    {V : Type v} [Group V] [IsElementaryAbelian 2 V] :
    IsElementaryAbelian 2 (ULift.{u} V) where
  toIsMulCommutative :=
    ⟨⟨fun x y => by
      apply ULift.ext
      exact (IsMulCommutative.is_comm (M := V)).comm x.down y.down⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply ULift.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x.down

private theorem fixingSubgroup_ulift_map
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V] :
    (fixingSubgroup (ULift.{v} G)
      (Set.univ : Set (ULift.{u} V))).map
        (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom =
      fixingSubgroup G (Set.univ : Set V) := by
  let eG : ULift.{v} G ≃* G := MulEquiv.ulift
  let eV : ULift.{u} V ≃* V := MulEquiv.ulift
  ext g
  constructor
  · rintro ⟨gL, hgL, rfl⟩
    apply (mem_fixingSubgroup_iff (M := G) (s := Set.univ)).mpr
    have hgL' := (mem_fixingSubgroup_iff
      (M := ULift.{v} G) (s := Set.univ)).mp hgL
    intro x _hx
    have hfix := hgL' (eV.symm x) (Set.mem_univ _)
    exact congrArg eV hfix
  · intro hg
    refine ⟨eG.symm g, ?_, eG.apply_symm_apply g⟩
    apply (mem_fixingSubgroup_iff (M := ULift.{v} G) (s := Set.univ)).mpr
    have hg' := (mem_fixingSubgroup_iff (M := G) (s := Set.univ)).mp hg
    intro x _hx
    apply eV.injective
    exact hg' (eV x) (Set.mem_univ _)

private theorem fixedPoints_ulift_map
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V] (T : Subgroup G) :
    let TL := T.comap
      (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom
    letI := MulDistribMulAction.compHom V T.subtype
    letI := MulDistribMulAction.compHom (ULift.{u} V) TL.subtype
    (FixedPoints.subgroup TL (ULift.{u} V)).map
        (MulEquiv.ulift : ULift.{u} V ≃* V).toMonoidHom =
      FixedPoints.subgroup T V := by
  dsimp only
  let eG : ULift.{v} G ≃* G := MulEquiv.ulift
  let eV : ULift.{u} V ≃* V := MulEquiv.ulift
  let _ := MulDistribMulAction.compHom V T.subtype
  let TL := T.comap eG.toMonoidHom
  let _ := MulDistribMulAction.compHom (ULift.{u} V) TL.subtype
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [FixedPoints.mem_subgroup]
    intro t
    let tL : TL := ⟨ULift.up (t : G), t.property⟩
    have hfix :=
      (FixedPoints.mem_subgroup (M := TL) (a := y)).mp hy tL
    exact congrArg ULift.down hfix
  · intro hx
    refine ⟨ULift.up x, ?_, rfl⟩
    change ∀ tL : TL, tL • (ULift.up x : ULift.{u} V) = ULift.up x
    intro tL
    apply ULift.ext
    exact (FixedPoints.mem_subgroup (M := T) (a := x)).mp hx
      ⟨tL.1.down, tL.property⟩

private theorem commutatorAction_ulift_map
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V] (T : Subgroup G) :
    let TL := T.comap
      (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom
    letI := MulDistribMulAction.compHom V T.subtype
    letI := MulDistribMulAction.compHom (ULift.{u} V) TL.subtype
    (commutatorAction TL (ULift.{u} V)).map
        (MulEquiv.ulift : ULift.{u} V ≃* V).toMonoidHom =
      commutatorAction T V := by
  dsimp only
  let eG : ULift.{v} G ≃* G := MulEquiv.ulift
  let eV : ULift.{u} V ≃* V := MulEquiv.ulift
  let _ := MulDistribMulAction.compHom V T.subtype
  let TL := T.comap eG.toMonoidHom
  let _ := MulDistribMulAction.compHom (ULift.{u} V) TL.subtype
  rw [commutatorAction_eq_closure, MonoidHom.map_closure,
    commutatorAction_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨tL, wL, rfl⟩, rfl⟩
    exact ⟨⟨tL.1.down, tL.property⟩, wL.down, rfl⟩
  · rintro ⟨t, w, rfl⟩
    let tL : TL := ⟨ULift.up (t : G), t.property⟩
    let wL : ULift.{u} V := ULift.up w
    exact ⟨wL⁻¹ * tL • wL, ⟨tL, wL, rfl⟩, rfl⟩

private theorem commutatorAction₂_ulift_map
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V] (T : Subgroup G) :
    let TL := T.comap
      (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom
    letI := MulDistribMulAction.compHom V T.subtype
    letI := MulDistribMulAction.compHom (ULift.{u} V) TL.subtype
    (commutatorAction₂ TL (ULift.{u} V)).map
        (MulEquiv.ulift : ULift.{u} V ≃* V).toMonoidHom =
      commutatorAction₂ T V := by
  dsimp only
  let eG : ULift.{v} G ≃* G := MulEquiv.ulift
  let eV : ULift.{u} V ≃* V := MulEquiv.ulift
  let _ := MulDistribMulAction.compHom V T.subtype
  let TL := T.comap eG.toMonoidHom
  let _ := MulDistribMulAction.compHom (ULift.{u} V) TL.subtype
  change (Subgroup.closure
    {x : ULift.{u} V | ∃ a : TL, ∃ w : ULift.{u} V,
      w ∈ commutatorAction TL (ULift.{u} V) ∧ x = w⁻¹ * a • w}).map
      eV.toMonoidHom =
    Subgroup.closure
      {x : V | ∃ a : T, ∃ w : V,
        w ∈ commutatorAction T V ∧ x = w⁻¹ * a • w}
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨tL, wL, hwL, rfl⟩, rfl⟩
    refine ⟨⟨tL.1.down, tL.property⟩, wL.down, ?_, rfl⟩
    have hwmap : wL.down ∈
        (commutatorAction TL (ULift.{u} V)).map eV.toMonoidHom :=
      ⟨wL, hwL, rfl⟩
    rwa [commutatorAction_ulift_map T] at hwmap
  · rintro ⟨t, w, hw, rfl⟩
    have hwmap : w ∈
        (commutatorAction TL (ULift.{u} V)).map eV.toMonoidHom := by
      rw [commutatorAction_ulift_map T]
      exact hw
    obtain ⟨wL, hwL, hwd⟩ := hwmap
    let tL : TL := ⟨ULift.up (t : G), t.property⟩
    refine ⟨wL⁻¹ * tL • wL, ⟨tL, wL, hwL, rfl⟩, ?_⟩
    change wL.down = w at hwd
    change wL.down⁻¹ * (t : G) • wL.down = w⁻¹ * (t : G) • w
    rw [hwd]

private theorem frattini_map_equiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro y hy
    have hy' : e.symm y ∈ frattini G :=
      frattini_le_comap_frattini_of_surjective
        (G := H) (H := G) (φ := e.symm.toMonoidHom) e.symm.surjective hy
    exact ⟨e.symm y, hy', e.apply_symm_apply y⟩

private theorem nestedSL2Two_of_core_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hcore : pCore 2 G = ⊥)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    IsSL2Two (G ⧸ frattini G) := by
  let ec : (G ⧸ pCore 2 G) ≃* (G ⧸ (⊥ : Subgroup G)) :=
    QuotientGroup.quotientMulEquivOfEq hcore
  let ecΦ : ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)) ≃*
      ((G ⧸ (⊥ : Subgroup G)) ⧸ frattini (G ⧸ (⊥ : Subgroup G))) :=
    QuotientGroup.congr _ _ ec (frattini_map_equiv ec)
  let e₀ : (G ⧸ (⊥ : Subgroup G)) ≃* G := QuotientGroup.quotientBot
  let eΦ : ((G ⧸ (⊥ : Subgroup G)) ⧸
      frattini (G ⧸ (⊥ : Subgroup G))) ≃* (G ⧸ frattini G) :=
    QuotientGroup.congr _ _ e₀ (frattini_map_equiv e₀)
  obtain ⟨e⟩ := hA
  exact ⟨(ecΦ.trans eΦ).symm.trans e⟩

private theorem permThree_solvable :
    Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let A : Subgroup (Equiv.Perm (Fin 3)) := alternatingGroup (Fin 3)
  have hAsolv : Group.IsSolvable A :=
    Group.isSolvable_of_comm fun x y =>
      (alternatingGroup.isMulCommutative_of_card_le_three
        (by simp : Nat.card (Fin 3) ≤ 3)).is_comm.comm x y
  let _ : Group.IsSolvable A := hAsolv
  have hQcard : Nat.card ((Equiv.Perm (Fin 3)) ⧸ A) = 2 := by
    rw [show Nat.card ((Equiv.Perm (Fin 3)) ⧸ A) = A.index from
      (Subgroup.index_eq_card A).symm]
    exact alternatingGroup.index_eq_two
  have hQcomm : IsMulCommutative ((Equiv.Perm (Fin 3)) ⧸ A) :=
    (isCyclic_of_prime_card (p := 2) hQcard).isMulCommutative
  have hQsolv : Group.IsSolvable ((Equiv.Perm (Fin 3)) ⧸ A) :=
    Group.isSolvable_of_comm fun x y => hQcomm.is_comm.comm x y
  exact (Group.isSolvable_iff_subgroup_quotient A).mpr ⟨hAsolv, hQsolv⟩

private theorem isSL2Two_solvable
    {G : Type*} [Group G] [Finite G] (hG : IsSL2Two G) :
    Group.IsSolvable G := by
  obtain ⟨eG⟩ := hG
  obtain ⟨eS⟩ := SectionOne.sl2Two_equiv_perm_three
  let e := eG.trans eS
  let _ : Group.IsSolvable (Equiv.Perm (Fin 3)) := permThree_solvable
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective

private theorem solvable_of_nestedSL2Two_of_core_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hcore : pCore 2 G = ⊥)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    Group.IsSolvable G := by
  have hQ := nestedSL2Two_of_core_eq_bot hcore hA
  have hQsolv := isSL2Two_solvable hQ
  let _ : Group.IsNilpotent (frattini G) := frattini_nilpotent
  have hΦsolv : Group.IsSolvable (frattini G) := inferInstance
  exact (Group.isSolvable_iff_subgroup_quotient (frattini G)).mpr
    ⟨hΦsolv, hQsolv⟩

private theorem frattini_odd_of_core_eq_bot
    {G : Type*} [Group G] [Finite G] (hcore : pCore 2 G = ⊥) :
    ¬ 2 ∣ Nat.card (frattini G) := by
  let Φ : Subgroup G := frattini G
  let P : Sylow 2 Φ := default
  have hΦnil : Group.IsNilpotent Φ := by
    simpa [Φ] using (frattini_nilpotent (G := G))
  have hPnormal : (P : Subgroup Φ).Normal :=
    Group.IsNilpotent.sylow_normal hΦnil 2 P
  let _ : (P : Subgroup Φ).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hPmapNormal : ((P : Subgroup Φ).map Φ.subtype).Normal := by
    infer_instance
  have hPmapCore : (P : Subgroup Φ).map Φ.subtype ≤ pCore 2 G :=
    le_sSup ⟨hPmapNormal, P.isPGroup'.map Φ.subtype⟩
  intro hdvd
  have hPne : (P : Subgroup Φ) ≠ ⊥ := P.ne_bot_of_dvd_card hdvd
  have hPmapBot : (P : Subgroup Φ).map Φ.subtype = ⊥ :=
    le_bot_iff.mp (hPmapCore.trans (le_of_eq hcore))
  exact hPne <|
    (Subgroup.map_eq_bot_iff_of_injective
      (H := (P : Subgroup Φ)) (f := Φ.subtype) Φ.subtype_injective).1 hPmapBot

private theorem inf_eq_bot_of_two_group_odd_card
    {G : Type*} [Group G] [Finite G]
    (P K : Subgroup G) (hP : IsPGroup 2 P)
    (hKodd : ¬ 2 ∣ Nat.card K) :
    P ⊓ K = ⊥ := by
  have hI : IsPGroup 2 ↑(P ⊓ K) := hP.to_le inf_le_left
  rcases hI.card_eq_or_dvd with hcard | hdvd
  · exact Subgroup.card_eq_one.mp hcard
  · exact False.elim (hKodd (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)))

private theorem sylow_card_two_of_nestedSL2Two_of_core_eq_bot
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hcore : pCore 2 G = ⊥)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    Nat.card S = 2 := by
  let Φ : Subgroup G := frattini G
  let q : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  let Sbar : Sylow 2 (G ⧸ Φ) :=
    S.mapSurjective (QuotientGroup.mk'_surjective Φ)
  have hA' := nestedSL2Two_of_core_eq_bot hcore hA
  have hquotcard : Nat.card (G ⧸ Φ) = 6 := by
    simpa [Φ] using SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hA'
  have hSbarcard : Nat.card Sbar = 2 := by
    rw [Sbar.card_eq_multiplicity, hquotcard]
    have hf6 : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hf6]
  have hodd : ¬ 2 ∣ Nat.card Φ := by
    simpa [Φ] using frattini_odd_of_core_eq_bot hcore
  have hinter : (S : Subgroup G) ⊓ Φ = ⊥ :=
    inf_eq_bot_of_two_group_odd_card (S : Subgroup G) Φ S.isPGroup' hodd
  have hqinj : Function.Injective (q.comp (S : Subgroup G).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro s hs
      have hsΦ : (s : G) ∈ Φ := by
        exact (QuotientGroup.eq_one_iff (N := Φ) (x := (s : G))).mp hs
      have hsI : (s : G) ∈ (S : Subgroup G) ⊓ Φ := ⟨s.property, hsΦ⟩
      rw [hinter] at hsI
      simpa using hsI
    · exact bot_le
  let fS : S →* G ⧸ Φ := q.comp (S : Subgroup G).subtype
  have hfrange : fS.range = (S : Subgroup G).map q := by
    ext x
    simp [fS]
  have hcardmap : Nat.card ((S : Subgroup G).map q) = Nat.card S := by
    rw [← hfrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hqinj).toEquiv).symm
  have hcoe : (Sbar : Subgroup (G ⧸ Φ)) = (S : Subgroup G).map q := rfl
  rw [← hcardmap, ← hcoe, hSbarcard]

private theorem m_eq_fixed_quotient_card_div
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V] (T : Subgroup G) :
    SectionOne.m (G := G) (V := V) T =
      (Nat.card (V ⧸ FixedPoints.subgroup T V) : ℚ) / Nat.card T := by
  let C := FixedPoints.subgroup T V
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hCpos : (Nat.card C : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := C)).ne'
  dsimp only [C] at hmul hCpos ⊢
  unfold SectionOne.m
  rw [show Nat.card V =
      Nat.card (V ⧸ FixedPoints.subgroup T V) *
        Nat.card (FixedPoints.subgroup T V) from hmul,
    Nat.cast_mul]
  field_simp [hCpos]

private theorem initial_module_data
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G) (T : Subgroup G)
    (hfaithful : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcore : pCore 2 G = ⊥)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)))
    (hTS : T ≤ (S : Subgroup G)) (hT : T ≠ ⊥)
    (hquadratic : commutatorAction₂ T V = ⊥)
    (hcard : Nat.card (V ⧸ FixedPoints.subgroup T V) ≤ Nat.card T) :
    Nat.card (V ⧸ FixedPoints.subgroup T V) = Nat.card T ∧
      T = (S : Subgroup G) ∧
      SectionOne.Hypotheses G V ∧
      IsElementaryAbelian 2 (S : Subgroup G) ∧
      SectionOne.m (G := G) (V := V) (S : Subgroup G) = 1 := by
  have hScard : Nat.card S = 2 :=
    sylow_card_two_of_nestedSL2Two_of_core_eq_bot S hcore hA
  have hTcardLe : Nat.card T ≤ 2 := by
    simpa [hScard] using Subgroup.card_le_of_le hTS
  have hTcardGt : 1 < Nat.card T :=
    (Subgroup.one_lt_card_iff_ne_bot T).mpr hT
  have hTcard : Nat.card T = 2 := by omega
  have hTeq : T = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hTS (by simp [hScard, hTcard])
  have hEvenS : Even (Nat.card S) := by rw [hScard]; decide
  have hEvenG : Even (Nat.card G) :=
    hEvenS.trans_dvd (Subgroup.card_subgroup_dvd_card (S : Subgroup G))
  have hsolv : Group.IsSolvable G :=
    solvable_of_nestedSL2Two_of_core_eq_bot hcore hA
  let hSec : SectionOne.Hypotheses G V :=
    { G_solvable := hsolv
      G_even := hEvenG
      action_faithful := hfaithful
      twoCore_eq_bot := hcore }
  have hquadS : commutatorAction₂ (S : Subgroup G) V = ⊥ := by
    rw [← hTeq]
    exact hquadratic
  have hSelem : IsElementaryAbelian 2 (S : Subgroup G) :=
    (SectionOne.lemma_one_one hSec S).part_d hquadS
  have hmge : (1 : ℚ) ≤ SectionOne.m (G := G) (V := V) (S : Subgroup G) :=
    SectionOne.lemma_one_five_m_ge_one_relative hSec S (S : Subgroup G)
      le_rfl hSelem
  have hmform := m_eq_fixed_quotient_card_div (G := G) (V := V) (S : Subgroup G)
  have hqgeQ : (2 : ℚ) ≤
      Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup G) V) := by
    rw [hmform, hScard] at hmge
    linarith
  have hqge : 2 ≤ Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup G) V) := by
    exact_mod_cast hqgeQ
  have hcardS : Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup G) V) ≤ 2 := by
    calc
      Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup G) V) =
          Nat.card (V ⧸ FixedPoints.subgroup T V) := by rw [hTeq]
      _ ≤ Nat.card T := hcard
      _ = 2 := hTcard
  have hqeqS : Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup G) V) = 2 :=
    Nat.le_antisymm hcardS hqge
  have hqeqT : Nat.card (V ⧸ FixedPoints.subgroup T V) = Nat.card T := by
    calc
      Nat.card (V ⧸ FixedPoints.subgroup T V) =
          Nat.card (V ⧸ FixedPoints.subgroup (S : Subgroup G) V) := by rw [hTeq]
      _ = 2 := hqeqS
      _ = Nat.card T := hTcard.symm
  have hm : SectionOne.m (G := G) (V := V) (S : Subgroup G) = 1 := by
    rw [hmform, hqeqS, hScard]
    norm_num
  exact ⟨hqeqT, hTeq, hSec, hSelem, hm⟩

private theorem normalClosure_sylow_eq_top_of_isSL2Two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hG : IsSL2Two G) :
    Subgroup.normalClosure ((S : Subgroup G) : Set G) = ⊤ := by
  let N := Subgroup.normalClosure ((S : Subgroup G) : Set G)
  have hsquare (x : G) (hx : x ^ 2 = 1) : x ∈ N := by
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx).isPGroup 2 _
    obtain ⟨T, hT⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
    have hxS : g * x * g⁻¹ ∈ (S : Subgroup G) := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
        (hT (Subgroup.mem_zpowers x))
    have hconjN : g * x * g⁻¹ ∈ N := Subgroup.le_normalClosure hxS
    have hback := (inferInstance : N.Normal).conj_mem
      (g * x * g⁻¹) hconjN g⁻¹
    simpa [mul_assoc] using hback
  apply top_unique
  intro x _hx
  obtain ⟨a, b, ha, hb, hab⟩ := SectionOne.sl2_involution_products hG x
  rw [hab]
  exact N.mul_mem (hsquare a ha) (hsquare b hb)

private theorem oneE_eq_top_of_module_data
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G)
    (hcore : pCore 2 G = ⊥)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)))
    (hSelem : IsElementaryAbelian 2 (S : Subgroup G))
    (hm : SectionOne.m (G := G) (V := V) (S : Subgroup G) = 1) :
    SectionOne.oneE (G := G) (V := V) (S : Subgroup G) = ⊤ := by
  let J := SectionOne.oneJ (G := G) (V := V) (S : Subgroup G)
  let E := SectionOne.oneE (G := G) (V := V) (S : Subgroup G)
  have hSA : SectionOne.oneA (G := G) (V := V)
      (S : Subgroup G) (S : Subgroup G) := ⟨le_rfl, hSelem, hm.le⟩
  have hSJ : (S : Subgroup G) ≤ J := le_sSup hSA
  have hSE : (S : Subgroup G) ≤ E :=
    hSJ.trans Subgroup.le_normalClosure
  let Φ : Subgroup G := frattini G
  let q : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  let R : Sylow 2 (G ⧸ Φ) :=
    S.mapSurjective (QuotientGroup.mk'_surjective Φ)
  have hA' := nestedSL2Two_of_core_eq_bot hcore hA
  have hRE : (R : Subgroup (G ⧸ Φ)) ≤ E.map q := by
    exact Subgroup.map_mono hSE
  have hEnormal : E.Normal := by
    dsimp only [E, SectionOne.oneE]
    infer_instance
  have hEmapNormal : (E.map q).Normal :=
    hEnormal.map q (QuotientGroup.mk'_surjective Φ)
  let _ : (E.map q).Normal := hEmapNormal
  have hclosure : Subgroup.normalClosure
      (((R : Sylow 2 (G ⧸ Φ)) : Subgroup (G ⧸ Φ)) : Set (G ⧸ Φ)) = ⊤ := by
    simpa [Φ] using normalClosure_sylow_eq_top_of_isSL2Two R hA'
  have hclosureLe : Subgroup.normalClosure
      (((R : Sylow 2 (G ⧸ Φ)) : Subgroup (G ⧸ Φ)) : Set (G ⧸ Φ)) ≤ E.map q :=
    Subgroup.normalClosure_le_normal hRE
  have hEmap : E.map q = ⊤ := by
    apply top_unique
    rw [← hclosure]
    exact hclosureLe
  have hcomap := congrArg (Subgroup.comap q) hEmap
  have hsup : E ⊔ Φ = ⊤ := by
    simpa [Subgroup.comap_map_eq, q, Φ] using hcomap
  exact frattini_nongenerating (by simpa [E, Φ] using hsup)

private theorem top_isOneSevenFactor_of_oneE_eq_top_card_two
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hSec : SectionOne.Hypotheses G V) (S : Sylow 2 G)
    (hScard : Nat.card S = 2)
    (hEtop : SectionOne.oneE (G := G) (V := V) (S : Subgroup G) = ⊤) :
    SectionOne.IsOneSevenFactor (V := V) (⊤ : Subgroup G) := by
  classical
  let F := SectionOne.oneSevenFactors (G := G) (V := V)
  let E := SectionOne.oneSevenGenerated (G := G) (V := V)
  obtain ⟨hEnormal, hprod, _⟩ := SectionOne.oneSeven_global_product hSec S
  change IsInternalDirectProduct E F at hprod
  have hEgen : E = ⊤ :=
    (SectionOne.oneSeven_global_identification hSec S).2.symm.trans hEtop
  have hF : ∀ D ∈ F, SectionOne.IsOneSevenFactor (V := V) D :=
    fun D hD => (SectionOne.mem_oneSevenFactors_iff D).mp hD
  have hcard :=
    (SectionOne.sl2_product_sylow_coordinates S E hEnormal F hprod
      (fun D hD => (hF D hD).1)).2.2.1
  rw [hEgen, inf_top_eq, hScard] at hcard
  have hFcard : F.card = 1 := by
    apply (Nat.pow_right_injective (by decide : 1 < 2))
    simpa using hcard.symm
  obtain ⟨D, hFD⟩ := Finset.card_eq_one.mp hFcard
  have hDin : D ∈ F := by rw [hFD]; simp
  have hDE : D = E := by
    apply le_antisymm
    · rw [hprod.1]
      exact le_iSup (fun K : {K : Subgroup G // K ∈ F} => (K : Subgroup G))
        ⟨D, hDin⟩
    · rw [hprod.1]
      apply iSup_le
      intro K
      have hKD : K.val = D := by simpa [hFD] using K.property
      rw [hKD]
  have hD := hF D hDin
  rwa [hDE, hEgen] at hD

private theorem fixedPoints_top_eq
    {G : Type u} {V : Type v} [Group G] [Group V] [MulDistribMulAction G V] :
    FixedPoints.subgroup (⊤ : Subgroup G) V = FixedPoints.subgroup G V := by
  ext v
  rw [FixedPoints.mem_subgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hv g
    simpa only [Subgroup.mk_smul] using
      hv (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G))
  · intro hv g
    exact (Subgroup.mk_smul (g : G) g.property v).trans (hv (g : G))

private theorem commutatorAction_top_eq
    {G : Type u} {V : Type v} [Group G] [Group V] [MulDistribMulAction G V] :
    commutatorAction (⊤ : Subgroup G) V = commutatorAction G V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨g, v, rfl⟩
    exact ⟨(g : G), v,
      congrArg (fun w => v⁻¹ * w) (Subgroup.mk_smul (g : G) g.property v).symm⟩
  · rintro ⟨g, v, rfl⟩
    exact ⟨(⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)), v,
      congrArg (fun w => v⁻¹ * w)
        (Subgroup.mk_smul g (Subgroup.mem_top g) v)⟩

private theorem top_factor_module_complement
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hTop : SectionOne.IsOneSevenFactor (V := V) (⊤ : Subgroup G)) :
    IsCompl (FixedPoints.subgroup G V) (commutatorAction G V) := by
  let F : Subgroup G := (commutator (⊤ : Subgroup G)).map
    (⊤ : Subgroup G).subtype
  have hFcard : Nat.card F = 3 := by
    simpa [F] using hTop.2.1.2.1
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFcard, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcomplF : IsCompl (FixedPoints.subgroup F V) (commutatorAction F V) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  have hfixed : FixedPoints.subgroup F V = FixedPoints.subgroup G V := by
    apply le_antisymm
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro g
      exact SectionOne.oneSevenFactor_fixes_derived_fixedPoints
        (⊤ : Subgroup G) hTop g (Subgroup.mem_top g) v (by simpa [F] using hv)
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro f
      exact (FixedPoints.mem_subgroup (M := G) (a := v)).mp hv (f : G)
  have hcomm : commutatorAction F V = commutatorAction G V := by
    calc
      commutatorAction F V = commutatorAction (⊤ : Subgroup G) V :=
        (SectionOne.oneSevenFactor_full_commutator_eq_derived
          (⊤ : Subgroup G) hTop).symm
      _ = commutatorAction G V := commutatorAction_top_eq
  rwa [hfixed, hcomm] at hcomplF

private theorem isComplement'_of_isCompl_commutative
    {V : Type u} [Group V] [IsMulCommutative V]
    {C U : Subgroup V} (hcompl : IsCompl C U) :
    U.IsComplement' C := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcompl.disjoint.symm
  rw [← Subgroup.normal_mul U C, sup_comm, hcompl.sup_eq_top]
  rfl

private theorem quotientComplementEquiv_smul
    {A V : Type u} [Group A] [Group V] [IsMulCommutative V]
    [MulDistribMulAction A V]
    (C U : Subgroup V) (hcompl : IsCompl C U)
    (hCinv : IsInvariant A V C) (hUinv : IsInvariant A V U) :
    letI : IsInvariant A V C := hCinv
    letI : MulDistribMulAction A (V ⧸ C) :=
      quotientMulDistribMulAction (A := A) (G := V) C hCinv
    letI : IsInvariant A V U := hUinv
    ∀ (a : A) (x : V ⧸ C),
      (isComplement'_of_isCompl_commutative hcompl).QuotientMulEquiv (a • x) =
        a • (isComplement'_of_isCompl_commutative hcompl).QuotientMulEquiv x := by
  let _ : IsInvariant A V C := hCinv
  let _ : MulDistribMulAction A (V ⧸ C) :=
    quotientMulDistribMulAction (A := A) (G := V) C hCinv
  let _ : IsInvariant A V U := hUinv
  let e : (V ⧸ C) ≃* U :=
    (isComplement'_of_isCompl_commutative hcompl).QuotientMulEquiv
  have hinv (a : A) (u : U) : e.symm (a • u) = a • e.symm u := by
    change QuotientGroup.mk' C ((a • u : U) : V) =
      a • QuotientGroup.mk' C (u : V)
    rfl
  intro a x
  apply e.symm.injective
  calc
    e.symm (e (a • x)) = a • x := e.symm_apply_apply _
    _ = a • e.symm (e x) := congrArg (a • ·) (e.symm_apply_apply x).symm
    _ = e.symm (a • e x) := (hinv a (e x)).symm

private theorem quotient_natural_action_of_top_factor
    {G V : Type u}
    [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hG : IsSL2Two G)
    (hfaithful : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hTop : SectionOne.IsOneSevenFactor (V := V) (⊤ : Subgroup G)) :
    ∃ eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      let U := commutatorAction G V
      letI : IsInvariant G V U := commutatorAction_isInvariant
      letI : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
      IsNaturalSL2TwoActionAlong U eG ∧
      let C := FixedPoints.subgroup G V
      ∃ hCinv : IsInvariant G V C,
        letI := quotientMulDistribMulAction (A := G) (G := V) C hCinv
        IsNaturalSL2TwoActionAlong (V ⧸ C) eG := by
  let C : Subgroup V := FixedPoints.subgroup G V
  let U : Subgroup V := commutatorAction G V
  have hcompl : IsCompl C U := by
    simpa [C, U] using top_factor_module_complement hTop
  have hCinv : IsInvariant G V C := by
    constructor
    intro g v
    constructor
    · intro hv
      have hgv : g • v = v :=
        (FixedPoints.mem_subgroup (M := G) (a := v)).mp (by simpa [C] using hv) g
      rwa [hgv]
    · intro hgv
      have hgvinv : g⁻¹ • (g • v) = g • v :=
        (FixedPoints.mem_subgroup (M := G) (a := g • v)).mp
          (by simpa [C] using hgv) g⁻¹
      have hv_eq : v = g • v := by simpa [smul_smul] using hgvinv
      rwa [hv_eq]
  let hUinv : IsInvariant G V U := by
    simpa [U] using (commutatorAction_isInvariant (A := G) (G := V))
  let _ : IsInvariant G V U := hUinv
  let _ : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  have hUcard : Nat.card U = 4 := by
    rw [show U = commutatorAction (⊤ : Subgroup G) V by
      simpa [U] using commutatorAction_top_eq.symm]
    exact hTop.2.2.1
  have hUfaithful : fixingSubgroup G (Set.univ : Set U) = ⊥ := by
    apply le_antisymm
    · intro g hg
      have hgfixU : ∀ u : U, g • u = u := fun u =>
        (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set U))).mp hg
          u (Set.mem_univ u)
      have hgfixV (w : V) : (g : G) • w = w := by
        have hwtop : w ∈ C ⊔ U := by
          rw [hcompl.sup_eq_top]
          exact Subgroup.mem_top w
        let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
        rcases Subgroup.mem_sup_of_normal_left.mp hwtop with
          ⟨c, hc, z, hz, hcz⟩
        have hgc : (g : G) • c = c :=
          (FixedPoints.mem_subgroup (M := G) (a := c)).mp
            (by simpa [C] using hc) g
        have hgz : (g : G) • z = z :=
          congrArg Subtype.val (hgfixU ⟨z, hz⟩)
        rw [← hcz, smul_mul', hgc, hgz]
      have hgV : (g : G) ∈ fixingSubgroup G (Set.univ : Set V) :=
        (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set V))).mpr
          (fun w _hw => hgfixV w)
      rw [hfaithful] at hgV
      simpa using hgV
    · exact bot_le
  obtain ⟨eG, hNaturalU⟩ :=
    naturalSL2TwoActionAlong_of_faithful_card_four
      hG hUfaithful hUcard
  refine ⟨eG, by simpa [U] using hNaturalU, ?_⟩
  change ∃ hCinv : IsInvariant G V C,
    letI := quotientMulDistribMulAction (A := G) (G := V) C hCinv
    IsNaturalSL2TwoActionAlong (V ⧸ C) eG
  refine ⟨hCinv, ?_⟩
  let _ : IsInvariant G V C := hCinv
  let _ : MulDistribMulAction G (V ⧸ C) :=
    quotientMulDistribMulAction (A := G) (G := V) C hCinv
  let hcomp' : U.IsComplement' C :=
    isComplement'_of_isCompl_commutative hcompl
  let eCU : (V ⧸ C) ≃* U := hcomp'.QuotientMulEquiv
  obtain ⟨eU, heU⟩ := hNaturalU
  let eQ : Additive (V ⧸ C) ≃+ (Fin 2 → ZMod 2) :=
    (MulEquiv.toAdditive eCU).trans eU
  refine ⟨eQ, ?_⟩
  intro g x
  change eU (Additive.ofMul (eCU (g • x))) =
    Matrix.mulVec (eG g).1 (eU (Additive.ofMul (eCU x)))
  rw [quotientComplementEquiv_smul C U hcompl hCinv hUinv g x]
  exact heU g (eCU x)

private theorem fixedPoints_eq_commutator_sup_global_fixed
    {G V : Type u}
    [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNaturalU :
      let U := commutatorAction G V
      letI : IsInvariant G V U := commutatorAction_isInvariant
      letI : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
      IsNaturalSL2TwoActionAlong U eG)
    (hcompl : IsCompl (FixedPoints.subgroup G V) (commutatorAction G V))
    (hquadratic : commutatorAction₂ (S : Subgroup G) V = ⊥) :
    FixedPoints.subgroup (S : Subgroup G) V =
      commutatorAction (S : Subgroup G) V ⊔ FixedPoints.subgroup G V := by
  let C : Subgroup V := FixedPoints.subgroup G V
  let U : Subgroup V := commutatorAction G V
  let hUinvG : IsInvariant G V U := by
    simpa [U] using (commutatorAction_isInvariant (A := G) (G := V))
  let _ : IsInvariant G V U := hUinvG
  let _ : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let hUinvS : IsInvariant (S : Subgroup G) V U :=
    SectionOne.RankOneThreeGroupAssembly.isInvariant_restrict_actor
      (S : Subgroup G) U
  let _ : IsInvariant (S : Subgroup G) V U := hUinvS
  have hline : FixedPoints.subgroup (S : Subgroup G) U =
      commutatorAction (S : Subgroup G) U :=
    fixedPoints_eq_commutatorAction_of_naturalSL2Two_sylow
      S eG (by simpa [U] using hNaturalU)
  have hcommMapLe :
      (commutatorAction (S : Subgroup G) U).map U.subtype ≤
        commutatorAction (S : Subgroup G) V :=
    SectionOne.RankOneThreeGroupAssembly.commutatorAction_map_subtype_le_ambient U
  apply le_antisymm
  · intro w hw
    have hwtop : w ∈ C ⊔ U := by
      have hsup : C ⊔ U = ⊤ :=
        (show IsCompl C U by simpa [C, U] using hcompl).sup_eq_top
      rw [hsup]
      exact Subgroup.mem_top w
    let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
    rcases Subgroup.mem_sup_of_normal_left.mp hwtop with
      ⟨c, hc, z, hz, hcz⟩
    have hzfix : z ∈ FixedPoints.subgroup (S : Subgroup G) V := by
      rw [FixedPoints.mem_subgroup]
      intro s
      have hsw : s • w = w :=
        (FixedPoints.mem_subgroup (M := (S : Subgroup G)) (a := w)).mp hw s
      have hscG : (s : G) • c = c :=
        (FixedPoints.mem_subgroup (M := G) (a := c)).mp
          (by simpa [C] using hc) (s : G)
      have hsc : s • c = c :=
        (Subgroup.mk_smul (s : G) s.property c).trans hscG
      rw [← hcz, smul_mul', hsc] at hsw
      exact mul_left_cancel hsw
    have hzMap : z ∈
        (FixedPoints.subgroup (S : Subgroup G) U).map U.subtype := by
      rw [fixedPoints_subgroup_map_subtype_eq_inf U]
      exact ⟨hz, hzfix⟩
    have hzComm : z ∈ commutatorAction (S : Subgroup G) V := by
      apply hcommMapLe
      rwa [hline] at hzMap
    rw [← hcz]
    apply (commutatorAction (S : Subgroup G) V ⊔ C).mul_mem
    · exact (show C ≤ commutatorAction (S : Subgroup G) V ⊔ C from
        le_sup_right) hc
    · exact (show commutatorAction (S : Subgroup G) V ≤
        commutatorAction (S : Subgroup G) V ⊔ C from le_sup_left) hzComm
  · apply sup_le
    · exact commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquadratic
    · intro c hc
      rw [FixedPoints.mem_subgroup]
      intro s
      have hfixG : (s : G) • c = c :=
        (FixedPoints.mem_subgroup (M := G) (a := c)).mp
          (by simpa [C] using hc) (s : G)
      exact (Subgroup.mk_smul (s : G) s.property c).trans hfixG

private theorem sl2Two_module_same_universe
    {G V : Type u}
    [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G) (T : Subgroup G)
    (hfaithful : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcore : pCore 2 G = ⊥)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)))
    (hTS : T ≤ (S : Subgroup G)) (hT : T ≠ ⊥)
    (_hnp : ¬ IsPGroup 2 G)
    (hquadratic : commutatorAction₂ T V = ⊥)
    (hcard : Nat.card (V ⧸ FixedPoints.subgroup T V) ≤ Nat.card T) :
    Nat.card (V ⧸ FixedPoints.subgroup T V) = Nat.card T ∧
      T = (S : Subgroup G) ∧
      (∃ eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        let C := FixedPoints.subgroup G V
        ∃ hCinv : IsInvariant G V C,
          letI := quotientMulDistribMulAction (A := G) (G := V) C hCinv
          IsNaturalSL2TwoActionAlong (V ⧸ C) eG) ∧
      FixedPoints.subgroup T V =
        commutatorAction T V ⊔ FixedPoints.subgroup G V := by
  obtain ⟨hcardEq, hTeq, hSec, hSelem, hm⟩ :=
    initial_module_data S T hfaithful hcore hA hTS hT hquadratic hcard
  subst T
  have hScard : Nat.card S = 2 :=
    sylow_card_two_of_nestedSL2Two_of_core_eq_bot S hcore hA
  have hEtop : SectionOne.oneE (G := G) (V := V) (S : Subgroup G) = ⊤ :=
    oneE_eq_top_of_module_data S hcore hA hSelem hm
  have hTop : SectionOne.IsOneSevenFactor (V := V) (⊤ : Subgroup G) :=
    top_isOneSevenFactor_of_oneE_eq_top_card_two hSec S hScard hEtop
  have hG : IsSL2Two G :=
    SectionOne.isSL2Two_of_oneE_eq_top_of_sylow_card_two
      hSec S (by simpa using hScard) hEtop
  obtain ⟨eG, hNaturalU, hNaturalQuotient⟩ :=
    quotient_natural_action_of_top_factor hG hfaithful hTop
  have hfixedS : FixedPoints.subgroup (S : Subgroup G) V =
      commutatorAction (S : Subgroup G) V ⊔ FixedPoints.subgroup G V :=
    fixedPoints_eq_commutator_sup_global_fixed
      S eG hNaturalU (top_factor_module_complement hTop) hquadratic
  exact ⟨hcardEq, rfl, ⟨eG, hNaturalQuotient⟩, hfixedS⟩

public theorem sl2Two_module
    {barM : Type u} {V : Type v}
    [Group barM] [Finite barM] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction barM V]
    (Sbar : Sylow 2 barM) (Tbar : Subgroup barM)
    (hfaithful : fixingSubgroup barM (Set.univ : Set V) = ⊥)
    (hcore : pCore 2 barM = ⊥)
    (hA : IsSL2Two
      ((barM ⧸ pCore 2 barM) ⧸ frattini (barM ⧸ pCore 2 barM)))
    (hTS : Tbar ≤ (Sbar : Subgroup barM))
    (hT : Tbar ≠ ⊥)
    (hnp : ¬ IsPGroup 2 barM)
    (hquadratic : commutatorAction₂ Tbar V = ⊥)
    (hcard : Nat.card (V ⧸ FixedPoints.subgroup Tbar V) ≤ Nat.card Tbar) :
    Nat.card (V ⧸ FixedPoints.subgroup Tbar V) = Nat.card Tbar ∧
      Tbar = (Sbar : Subgroup barM) ∧
      (∃ ebarM : barM ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        let CbarM := FixedPoints.subgroup barM V
        ∃ hCbarM : IsInvariant barM V CbarM,
          letI := quotientMulDistribMulAction
            (A := barM) (G := V) CbarM hCbarM
          IsNaturalSL2TwoActionAlong (V ⧸ CbarM) ebarM) ∧
      FixedPoints.subgroup Tbar V =
        commutatorAction Tbar V ⊔ FixedPoints.subgroup barM V := by
  let barML := ULift.{v} barM
  let VL := ULift.{u} V
  let eM : barML ≃* barM := MulEquiv.ulift
  let eV : VL ≃* V := MulEquiv.ulift
  let _ : IsElementaryAbelian 2 VL := elementaryAbelian_ulift
  have hSrange : (Sbar : Subgroup barM) ≤ eM.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr eM.surjective]
    exact le_top
  let SbarL : Sylow 2 barML :=
    Sbar.comapOfInjective eM.toMonoidHom eM.injective hSrange
  let TbarL : Subgroup barML := Tbar.comap eM.toMonoidHom
  have hSmap : (SbarL : Subgroup barML).map eM.toMonoidHom =
      (Sbar : Subgroup barM) := by
    rw [show (SbarL : Subgroup barML) =
      (Sbar : Subgroup barM).comap eM.toMonoidHom from rfl]
    exact Subgroup.map_comap_eq_self_of_surjective eM.surjective _
  have hTmap : TbarL.map eM.toMonoidHom = Tbar := by
    dsimp only [TbarL]
    exact Subgroup.map_comap_eq_self_of_surjective eM.surjective _
  have hfaithfulL :
      fixingSubgroup barML (Set.univ : Set VL) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (f := eM.toMonoidHom) _ eM.injective).mp
    rw [fixingSubgroup_ulift_map, hfaithful]
  have hcoreL : pCore 2 barML = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (f := eM.toMonoidHom) _ eM.injective).mp
    rw [pCore_map_iso 2 eM, hcore]
  let eCore : (barML ⧸ pCore 2 barML) ≃* (barM ⧸ pCore 2 barM) :=
    QuotientGroup.congr _ _ eM (pCore_map_iso 2 eM)
  let eA : ((barML ⧸ pCore 2 barML) ⧸ frattini (barML ⧸ pCore 2 barML)) ≃*
      ((barM ⧸ pCore 2 barM) ⧸ frattini (barM ⧸ pCore 2 barM)) :=
    QuotientGroup.congr _ _ eCore (frattini_map_equiv eCore)
  have hAL : IsSL2Two
      ((barML ⧸ pCore 2 barML) ⧸ frattini (barML ⧸ pCore 2 barML)) := by
    obtain ⟨e⟩ := hA
    exact ⟨eA.trans e⟩
  have hTSL : TbarL ≤ (SbarL : Subgroup barML) := by
    rw [show (SbarL : Subgroup barML) =
      (Sbar : Subgroup barM).comap eM.toMonoidHom from rfl]
    exact Subgroup.comap_mono hTS
  have hTL : TbarL ≠ ⊥ := by
    intro hbot
    apply hT
    rw [← hTmap, hbot, Subgroup.map_bot]
  have hnpL : ¬ IsPGroup 2 barML := by
    intro hp
    exact hnp (IsPGroup.of_equiv hp eM)
  have hquadraticL : commutatorAction₂ TbarL VL = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (f := eV.toMonoidHom) _ eV.injective).mp
    calc
      (commutatorAction₂ TbarL VL).map eV.toMonoidHom =
          commutatorAction₂ Tbar V := by
        convert (commutatorAction₂_ulift_map
          (G := barM) (V := V) Tbar) using 1 <;> rfl
      _ = ⊥ := hquadratic
  have hfixedTmap :
      (FixedPoints.subgroup TbarL VL).map eV.toMonoidHom =
        FixedPoints.subgroup Tbar V := by
    convert (fixedPoints_ulift_map (G := barM) (V := V) Tbar) using 1 <;>
      rfl
  let eFixedQuotient :
      (VL ⧸ FixedPoints.subgroup TbarL VL) ≃*
        (V ⧸ FixedPoints.subgroup Tbar V) :=
    QuotientGroup.congr _ _ eV hfixedTmap
  have hTcard : Nat.card TbarL = Nat.card Tbar := by
    calc
      Nat.card TbarL = Nat.card (TbarL.map eM.toMonoidHom) :=
        Nat.card_congr
          (TbarL.equivMapOfInjective eM.toMonoidHom eM.injective).toEquiv
      _ = Nat.card Tbar := by rw [hTmap]
  have hcardL :
      Nat.card (VL ⧸ FixedPoints.subgroup TbarL VL) ≤ Nat.card TbarL := by
    rw [Nat.card_congr eFixedQuotient.toEquiv, hTcard]
    exact hcard
  obtain ⟨hcardEqL, hTeqL, hNaturalL, hfixedL⟩ :=
    sl2Two_module_same_universe SbarL TbarL hfaithfulL hcoreL hAL
      hTSL hTL hnpL hquadraticL hcardL
  have hcardEq :
      Nat.card (V ⧸ FixedPoints.subgroup Tbar V) = Nat.card Tbar :=
    (Nat.card_congr eFixedQuotient.toEquiv).symm.trans
      (hcardEqL.trans hTcard)
  have hTeq : Tbar = (Sbar : Subgroup barM) := by
    have hmapEq := congrArg (Subgroup.map eM.toMonoidHom) hTeqL
    rwa [hTmap, hSmap] at hmapEq
  have hfixedGlobalMap :
      (FixedPoints.subgroup barML VL).map eV.toMonoidHom =
        FixedPoints.subgroup barM V := by
    calc
      (FixedPoints.subgroup barML VL).map eV.toMonoidHom =
          (FixedPoints.subgroup (⊤ : Subgroup barML) VL).map
            eV.toMonoidHom := by
        rw [fixedPoints_top_eq]
      _ = FixedPoints.subgroup (⊤ : Subgroup barM) V := by
        convert (fixedPoints_ulift_map
          (G := barM) (V := V) (⊤ : Subgroup barM)) using 1 <;> rfl
      _ = FixedPoints.subgroup barM V := fixedPoints_top_eq
  have hcommTmap :
      (commutatorAction TbarL VL).map eV.toMonoidHom =
        commutatorAction Tbar V := by
    convert (commutatorAction_ulift_map
      (G := barM) (V := V) Tbar) using 1 <;> rfl
  have hfixed : FixedPoints.subgroup Tbar V =
      commutatorAction Tbar V ⊔ FixedPoints.subgroup barM V := by
    have hmapEq := congrArg (Subgroup.map eV.toMonoidHom) hfixedL
    rwa [hfixedTmap, Subgroup.map_sup, hcommTmap, hfixedGlobalMap] at hmapEq
  have hNatural :
      ∃ ebarM : barM ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        let CbarM := FixedPoints.subgroup barM V
        ∃ hCbarM : IsInvariant barM V CbarM,
          letI := quotientMulDistribMulAction
            (A := barM) (G := V) CbarM hCbarM
          IsNaturalSL2TwoActionAlong (V ⧸ CbarM) ebarM := by
    obtain ⟨eML, hCLinv, hNatL⟩ := hNaturalL
    let CL := FixedPoints.subgroup barML VL
    let C := FixedPoints.subgroup barM V
    let _ : IsInvariant barML VL CL := hCLinv
    let _ : MulDistribMulAction barML (VL ⧸ CL) :=
      quotientMulDistribMulAction (A := barML) (G := VL) CL hCLinv
    let hCinv : IsInvariant barM V C := by
      constructor
      intro g x
      constructor
      · intro hx
        have hgx : g • x = x :=
          (FixedPoints.mem_subgroup (M := barM) (a := x)).mp
            (by simpa [C] using hx) g
        rwa [hgx]
      · intro hgx
        have hback : g⁻¹ • (g • x) = g • x :=
          (FixedPoints.mem_subgroup (M := barM) (a := g • x)).mp
            (by simpa [C] using hgx) g⁻¹
        have hxeq : x = g • x := by simpa [smul_smul] using hback
        rwa [hxeq]
    let _ : IsInvariant barM V C := hCinv
    let _ : MulDistribMulAction barM (V ⧸ C) :=
      quotientMulDistribMulAction (A := barM) (G := V) C hCinv
    let eQ : (VL ⧸ CL) ≃* (V ⧸ C) :=
      QuotientGroup.congr CL C eV (by simpa [CL, C] using hfixedGlobalMap)
    have heQsmul (g : barML) (x : VL ⧸ CL) :
        eQ (g • x) = eM g • eQ x := by
      induction x using Quotient.inductionOn'
      rfl
    refine ⟨eM.symm.trans eML, hCinv, ?_⟩
    rw [IsNaturalSL2TwoActionAlong] at hNatL ⊢
    obtain ⟨eWL, heWL⟩ := hNatL
    let eW : Additive (V ⧸ C) ≃+ (Fin 2 → ZMod 2) :=
      eQ.symm.toAdditive.trans eWL
    refine ⟨eW, ?_⟩
    intro g x
    have heQsymm : eQ.symm (g • x) = eM.symm g • eQ.symm x := by
      apply eQ.injective
      rw [heQsmul, eQ.apply_symm_apply, eM.apply_symm_apply,
        eQ.apply_symm_apply]
    calc
      eW (Additive.ofMul (g • x)) =
          eWL (Additive.ofMul (eQ.symm (g • x))) := rfl
      _ = eWL (Additive.ofMul (eM.symm g • eQ.symm x)) :=
        congrArg eWL heQsymm
      _ = Matrix.mulVec (eML (eM.symm g)).1
          (eWL (Additive.ofMul (eQ.symm x))) :=
        heWL (eM.symm g) (eQ.symm x)
      _ = Matrix.mulVec ((eM.symm.trans eML) g).1
          (eW (Additive.ofMul x)) := by rfl
  exact ⟨hcardEq, hTeq, hNatural, hfixed⟩

end Stellmacher.PushingUp
