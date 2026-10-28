module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.SL2FourNaturalOrbits.PlaneOrbits.Determinant
public import Theory.Representation.SL2FourNaturalOrbits.SylowDisplacement
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Abel

/-!
# The actual binary-plane orbits of SL₂(4)

There are 35 binary planes in the natural module F₄². The determinant of a
binary basis is independent of its choice and completely classifies the SL₂(4)
orbits. Its zero fiber consists of the five F₄-lines, precisely the planes
centralized pointwise by Sylow two-subgroups. Each of the three nonzero fibers
has ten planes. The quotient by the actual matrix orbit relation is explicitly
identified with the three nonzero field elements. Every binary automorphism
of a noncentral plane is induced by its SL₂(4) stabilizer.

For the orbit proof, move the first basis vector to (1,0). Equal nonzero
determinants then give equal nonzero second coordinates, and an upper
unipotent transports the second basis vector. Zero determinant identifies
F₄-lines, where nonzero-vector transitivity suffices. The existing upper
unipotent Sylow theorem and its fixed-plane calculation identify central type.
All orbit statements use the original subspaces and the original matrix action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §6.2.5,
printed pp.680–681 (PDF pp.697–698). This supplies the SL₂(4) geometry in that
proof; semilinear fusion and the ambient-group conclusions are separate.
-/

@[expose] public section
open Classical

namespace Representation.SL2FourNatural.PlaneGeometry
noncomputable def mapPlane (e : V ≃ₗ[ZMod 2] V) (U : Plane) : Plane :=
  ⟨U.1.map e.toLinearMap,
    (Nat.card_congr (Submodule.equivMapOfInjective e.toLinearMap e.injective U.1).toEquiv).symm.trans U.2⟩

def mapFrame (e : V ≃ₗ[ZMod 2] V) (U : Plane) (p : Frame U.1) : Frame (mapPlane e U).1 :=
  ⟨(⟨e (p.1.1 : V), ⟨p.1.1,p.1.1.2,rfl⟩⟩,
    ⟨e (p.1.2 : V), ⟨p.1.2,p.1.2.2,rfl⟩⟩),
    (fun h => p.2.1 (Subtype.ext (e.injective ((congrArg Subtype.val h).trans (map_zero e).symm)))),
    (fun h => p.2.2.1 (Subtype.ext (e.injective ((congrArg Subtype.val h).trans (map_zero e).symm)))),
    (fun h => p.2.2.2 (Subtype.ext (e.injective (congrArg Subtype.val h))))⟩

lemma determinant_action (A : SL) (U : Plane) :
    determinant (mapPlane (action A) U) = determinant U := by
  rw [determinant_eq _ (mapFrame (action A) U (chosenFrame U))]
  exact wedge_action A _ _

lemma determinant_frobenius (U : Plane) :
    determinant (mapPlane frobeniusLinear U) = fieldFrobenius (determinant U) := by
  rw [determinant_eq _ (mapFrame frobeniusLinear U (chosenFrame U))]
  exact wedge_frobenius _ _

lemma submodule_eq_of_card (U W : Submodule (ZMod 2) V) (h : U ≤ W)
    (hc : Nat.card U = Nat.card W) : U = W := by
  apply le_antisymm h
  have hs := (Submodule.inclusion_injective h).bijective_of_nat_card_le hc.ge
  intro x hx
  obtain ⟨y,hy⟩ := hs.2 ⟨x,hx⟩
  have he : (y : V) = x := congrArg Subtype.val hy
  rw [← he]
  exact y.2

lemma wedge_zero_iff (u v : V) (hu : u ≠ 0) :
    wedge u v = 0 ↔ v ∈ Submodule.span F ({u} : Set V) := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    have he : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp h
    by_cases hu0 : u 0 = 0
    · have hu1 : u 1 ≠ 0 := by
        intro hh
        apply hu
        funext i
        fin_cases i <;> simp [hu0, hh]
      have hv0 : v 0 = 0 := by
        rw [hu0, zero_mul] at he
        exact (mul_eq_zero.mp he.symm).resolve_left hu1
      refine ⟨v 1 / u 1, ?_⟩
      funext i
      fin_cases i <;> simp [hu0,hu1,hv0]
    · refine ⟨v 0 / u 0, ?_⟩
      funext i
      fin_cases i
      · simp [hu0]
      · change v 0 / u 0 * u 1 = v 1
        rw [div_mul_eq_mul_div, div_eq_iff hu0]
        simpa [mul_comm] using he.symm
  · rintro ⟨c,rfl⟩
    simp only [wedge, Pi.smul_apply, smul_eq_mul]
    ring

lemma card_field_span (u : V) (hu : u ≠ 0) :
    Nat.card ((Submodule.span F ({u} : Set V)).restrictScalars (ZMod 2)) = 4 := by
  change Nat.card (Submodule.span F ({u} : Set V)) = 4
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_span_singleton hu,
    pow_one, Nat.card_eq_fintype_card, card_field]

lemma determinant_zero_iff (U : Plane) : determinant U = 0 ↔ IsFieldLine U.1 := by
  let p := chosenFrame U
  have hu : (p.1.1 : V) ≠ 0 := (forgetFrame U p).2.1
  rw [determinant_eq U p]
  constructor
  · intro h
    let W := Submodule.span F ({(p.1.1 : V)} : Set V)
    have hle : U.1 ≤ W.restrictScalars (ZMod 2) := by
      rw [plane_eq_span U p, Submodule.span_le]
      rintro x (rfl | rfl)
      · exact Submodule.mem_span_singleton_self _
      · exact (wedge_zero_iff _ _ hu).mp h
    have hEq : U.1 = W.restrictScalars (ZMod 2) :=
      submodule_eq_of_card _ _ hle (U.2.trans (card_field_span _ hu).symm)
    exact ⟨W, finrank_span_singleton hu, hEq.symm⟩
  · rintro ⟨W,hW,hWU⟩
    have hum : (p.1.1 : V) ∈ W := by
      change (p.1.1 : V) ∈ W.restrictScalars (ZMod 2)
      rw [hWU]
      exact p.1.1.2
    have hvm : (p.1.2 : V) ∈ W := by
      change (p.1.2 : V) ∈ W.restrictScalars (ZMod 2)
      rw [hWU]
      exact p.1.2.2
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hW hum hu] at hvm
    exact (wedge_zero_iff _ _ hu).mpr hvm

lemma field_plane_eq_span (U : Plane) (hU : IsFieldLine U.1) (u : V)
    (hu : u ∈ U.1) (hu0 : u ≠ 0) :
    U.1 = (Submodule.span F ({u} : Set V)).restrictScalars (ZMod 2) := by
  obtain ⟨W,hW,hWU⟩ := hU
  rw [← hWU] at hu ⊢
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hW hu hu0]

lemma action_smul (A : SL) (c : F) (u : V) : action A (c • u) = c • action A u :=
  (Matrix.SpecialLinearGroup.toLin' A).map_smul c u

lemma field_line_transitive (U W : Plane) (hU : IsFieldLine U.1) (hW : IsFieldLine W.1) :
    ∃ A : SL, U.1.map (action A).toLinearMap = W.1 := by
  let p := chosenFrame U
  let q := chosenFrame W
  have hu : (p.1.1 : V) ≠ 0 := (forgetFrame U p).2.1
  have hv : (q.1.1 : V) ≠ 0 := (forgetFrame W q).2.1
  obtain ⟨A,hA⟩ := transitive_nonzero _ _ hu hv
  refine ⟨A, submodule_eq_of_card _ _ ?_ ((mapPlane (action A) U).2.trans W.2.symm)⟩
  rintro x ⟨y,hy,rfl⟩
  rw [field_plane_eq_span U hU _ p.1.1.2 hu] at hy
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
  change action A (c • (p.1.1 : V)) ∈ W.1
  rw [action_smul, hA]
  exact (SetLike.ext_iff.mp (field_plane_eq_span W hW _ q.1.1.2 hv) _).mpr
    (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))
lemma upper_pair_transport (v w : V) (hv : v 1 ≠ 0) (he : v 1 = w 1) :
    ∃ C : SL, action C ![1,0] = ![1,0] ∧ action C v = w := by
  refine ⟨upper ((w 0 - v 0) / v 1), ?_, ?_⟩
  · simp [upper_action]
  · rw [upper_action]
    funext i
    fin_cases i
    · change v 0 + (w 0 - v 0) / v 1 * v 1 = w 0
      rw [div_mul_cancel₀ _ hv]
      abel
    · exact he

lemma pair_transport (p q : Frame V)
    (hd : wedge p.1.1 p.1.2 = wedge q.1.1 q.1.2)
    (hn : wedge p.1.1 p.1.2 ≠ 0) :
    ∃ A : SL, action A p.1.1 = q.1.1 ∧ action A p.1.2 = q.1.2 := by
  obtain ⟨A,hA⟩ := exists_first_column p.1.1 p.2.1
  obtain ⟨B,hB⟩ := exists_first_column q.1.1 q.2.1
  let v := action A⁻¹ p.1.2
  let w := action B⁻¹ q.1.2
  have hv : v 1 = wedge p.1.1 p.1.2 := by
    have ht := wedge_action A ![1,0] v
    rw [hA, show action A v = p.1.2 by simp [v]] at ht
    simpa [wedge] using ht.symm
  have hw : w 1 = wedge q.1.1 q.1.2 := by
    have ht := wedge_action B ![1,0] w
    rw [hB, show action B w = q.1.2 by simp [w]] at ht
    simpa [wedge] using ht.symm
  obtain ⟨C,hCe,hCv⟩ := upper_pair_transport v w (by rwa [hv]) (hv.trans (hd.trans hw.symm))
  refine ⟨B * C * A⁻¹, ?_, ?_⟩
  · simp only [map_mul, LinearEquiv.mul_apply]
    rw [show action A⁻¹ p.1.1 = ![1,0] by rw [← hA]; simp, hCe, hB]
  · simp only [map_mul, LinearEquiv.mul_apply]
    change action B (action C v) = q.1.2
    rw [hCv]
    simp [w]

lemma map_eq_of_frame (U W : Plane) (p : Frame U.1) (q : Frame W.1) (A : SL)
    (hu : action A (p.1.1 : V) = q.1.1) (hv : action A (p.1.2 : V) = q.1.2) :
    U.1.map (action A).toLinearMap = W.1 := by
  apply submodule_eq_of_card _ _ _ ((mapPlane (action A) U).2.trans W.2.symm)
  rintro x ⟨y,hy,rfl⟩
  change action A y ∈ W.1
  rw [plane_eq_span U p] at hy
  change y ∈ Submodule.span (ZMod 2) ({(p.1.1 : V),(p.1.2 : V)} : Set V) at hy
  rw [mem_binary_span] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · rw [map_zero]; exact W.1.zero_mem
  · rw [hu]; exact q.1.1.2
  · rw [hv]; exact q.1.2.2
  · rw [map_add, hu, hv]; exact W.1.add_mem q.1.1.2 q.1.2.2

/-- The determinant is a complete invariant for the actual SL₂(4) action. -/
lemma orbit_iff_determinant (U W : Plane) :
    (∃ A : SL, U.1.map (action A).toLinearMap = W.1) ↔ determinant U = determinant W := by
  constructor
  · rintro ⟨A,hA⟩
    have h : mapPlane (action A) U = W := Subtype.ext hA
    rw [← h, determinant_action]
  · intro hd
    by_cases hn : determinant U = 0
    · exact field_line_transitive U W ((determinant_zero_iff U).mp hn)
        ((determinant_zero_iff W).mp (hd ▸ hn))
    · let p := chosenFrame U
      let q := chosenFrame W
      obtain ⟨A,hu,hv⟩ := pair_transport (forgetFrame U p) (forgetFrame W q)
        ((determinant_eq U p).symm.trans (hd.trans (determinant_eq W q)))
        (fun h => hn ((determinant_eq U p).trans h))
      exact ⟨A, map_eq_of_frame U W p q A hu hv⟩

lemma card_orbit (U : Plane) :
    Nat.card {W : Plane // ∃ A : SL, U.1.map (action A).toLinearMap = W.1} =
      if IsFieldLine U.1 then 5 else 10 := by
  classical
  have e : {W : Plane // ∃ A : SL, U.1.map (action A).toLinearMap = W.1} ≃
      {W : Plane // determinant W = determinant U} :=
    Equiv.subtypeEquivRight (fun W => (orbit_iff_determinant U W).trans eq_comm)
  rw [Nat.card_congr e, card_determinant_fiber]
  simp only [determinant_zero_iff]

/-- Every binary automorphism of a noncentral plane is induced by its SL stabilizer. -/
lemma noncentral_automorphism (U : Plane) (hU : ¬ IsFieldLine U.1)
    (e : U.1 ≃ₗ[ZMod 2] U.1) :
    ∃ A : SL, U.1.map (action A).toLinearMap = U.1 ∧
      ∀ u : U.1, action A (u : V) = (e u : V) := by
  let p := chosenFrame U
  let q : Frame U.1 := ⟨(e p.1.1,e p.1.2),
    (fun h => p.2.1 (e.injective (h.trans (map_zero e).symm))),
    (fun h => p.2.2.1 (e.injective (h.trans (map_zero e).symm))),
    (fun h => p.2.2.2 (e.injective h))⟩
  have hn : determinant U ≠ 0 := fun h => hU ((determinant_zero_iff U).mp h)
  obtain ⟨A,hu,hv⟩ := pair_transport (forgetFrame U p) (forgetFrame U q)
    ((determinant_eq U p).symm.trans (determinant_eq U q))
    (fun h => hn ((determinant_eq U p).trans h))
  refine ⟨A, map_eq_of_frame U U p q A hu hv, ?_⟩
  change action A (p.1.1 : V) = (e p.1.1 : V) at hu
  change action A (p.1.2 : V) = (e p.1.2 : V) at hv
  intro u
  rcases four_span U.2 p u with rfl | rfl | rfl | rfl
  · simp
  · exact hu
  · exact hv
  · simpa only [Submodule.coe_add, map_add] using congrArg₂ (· + ·) hu hv

/-- The literal pointwise centralization condition on a binary plane. -/
def CentralizedBy (U : Plane) (P : Subgroup SL) : Prop :=
  ∀ A ∈ P, ∀ u ∈ U.1, action A u = u

lemma upperFixed_fieldLine : IsFieldLine upperFixed := by
  refine ⟨Submodule.span F ({![1,0]} : Set V), finrank_span_singleton (by decide), ?_⟩
  ext v
  change (v ∈ Submodule.span F ({![1,0]} : Set V)) ↔ v ∈ upperFixed
  rw [Submodule.mem_span_singleton, mem_upperFixed]
  constructor
  · rintro ⟨c,rfl⟩
    simp
  · intro h
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [h]

lemma upper_transvection (c : F) :
    upper c = Matrix.SpecialLinearGroup.transvection zero_ne_one c := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.SpecialLinearGroup.transvection_coe]

lemma central_upper : CentralizedBy ⟨upperFixed,card_upperFixed⟩
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2 : Subgroup SL) := by
  intro A hA u hu
  obtain ⟨c,hc⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F A).mp hA
  rw [← upper_transvection] at hc
  subst A
  exact (upper_fixed_iff u).mpr ((mem_upperFixed u).mp hu) c

lemma central_map (U : Plane) (P : Sylow 2 SL) (hP : CentralizedBy U P) (a : SL) :
    CentralizedBy (mapPlane (action a) U) (a • P : Sylow 2 SL) := by
  intro g hg v hv
  have hg' : ∃ b ∈ (P : Subgroup SL), a * b * a⁻¹ = g := by
    change g ∈ ((a • P : Sylow 2 SL) : Subgroup SL) at hg
    rw [Sylow.coe_subgroup_smul] at hg
    exact hg
  obtain ⟨b,hb,rfl⟩ := hg'
  obtain ⟨w,hw,rfl⟩ := hv
  simp only [map_mul, LinearEquiv.mul_apply]
  change action a (action b (action a⁻¹ (action a w))) = action a w
  rw [show action a⁻¹ (action a w) = w by simp, hP b hb w hw]

lemma sylow_fixed_isFieldLine (P : Sylow 2 SL) :
    ∃ W : Plane, IsFieldLine W.1 ∧
      ∀ v, v ∈ W.1 ↔ ∀ A ∈ (P : Subgroup SL), action A v = v := by
  obtain ⟨W,hc,hfix,-⟩ := sylow_fixed_plane_displacements P
  let W₄ : Submodule F V := {
    carrier := W
    zero_mem' := W.zero_mem
    add_mem' := W.add_mem
    smul_mem' := by
      intro c v hv
      apply (hfix _).mpr
      intro A hA
      rw [action_smul, (hfix v).mp hv A hA] }
  have hc₄ : Nat.card W₄ = 4 := hc
  have hr : Module.finrank F W₄ = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := W₄)
    rw [hc₄, Nat.card_eq_fintype_card, card_field] at h
    exact (Nat.pow_right_injective (by decide : 1 < (4 : ℕ))
      (show (4 : ℕ) ^ 1 = 4 ^ Module.finrank F W₄ from h)).symm
  exact ⟨⟨W,hc⟩,⟨W₄,hr,rfl⟩,hfix⟩

/-- Central type in the source is exactly being an actual F₄-line. -/
lemma fieldLine_iff_sylow_centralized (U : Plane) :
    IsFieldLine U.1 ↔ ∃ P : Sylow 2 SL, CentralizedBy U P := by
  constructor
  · intro hU
    obtain ⟨a,ha⟩ := field_line_transitive ⟨upperFixed,card_upperFixed⟩ U
      upperFixed_fieldLine hU
    have hm : mapPlane (action a) ⟨upperFixed,card_upperFixed⟩ = U := Subtype.ext ha
    refine ⟨a • Matrix.SpecialLinearGroup.upperUnipotentSylow F 2, ?_⟩
    rw [← hm]
    exact central_map _ _ central_upper a
  · rintro ⟨P,hP⟩
    obtain ⟨W,hW,hfix⟩ := sylow_fixed_isFieldLine P
    have hle : U.1 ≤ W.1 := fun v hv => (hfix v).mpr (fun A hA => hP A hA v hv)
    have he := submodule_eq_of_card U.1 W.1 hle (U.2.trans W.2.symm)
    rwa [he]


lemma card_field_lines : Nat.card {U : Plane // IsFieldLine U.1} = 5 := by
  have e : {U : Plane // IsFieldLine U.1} ≃ {U : Plane // determinant U = 0} :=
    Equiv.subtypeEquivRight (fun U => (determinant_zero_iff U).symm)
  rw [Nat.card_congr e, card_determinant_fiber]
  simp

lemma card_noncentral_planes : Nat.card {U : Plane // ¬ IsFieldLine U.1} = 30 := by
  let := Fintype.ofFinite Plane
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_planes, card_field_lines]

lemma determinant_surjective : Function.Surjective determinant := by
  intro d
  have hc : 0 < Nat.card {U : Plane // determinant U = d} := by
    rw [card_determinant_fiber]
    split_ifs <;> decide
  obtain ⟨U,hU⟩ := (Nat.card_pos_iff.mp hc).1
  exact ⟨U,hU⟩

abbrev NoncentralPlane := {U : Plane // ¬ IsFieldLine U.1}
abbrev NonzeroDeterminant := {d : F // d ≠ 0}

noncomputable def noncentralDeterminant (U : NoncentralPlane) : NonzeroDeterminant :=
  ⟨determinant U.1, fun h => U.2 ((determinant_zero_iff U.1).mp h)⟩

lemma noncentralDeterminant_surjective : Function.Surjective noncentralDeterminant := by
  intro d
  obtain ⟨U,hU⟩ := determinant_surjective d.1
  have hn : ¬ IsFieldLine U.1 := by
    intro h
    exact d.2 (hU.symm.trans ((determinant_zero_iff U).mpr h))
  exact ⟨⟨U,hn⟩,Subtype.ext hU⟩

/-- The equivalence relation is defined by actual determinant-one matrices. -/
def noncentralOrbitSetoid : Setoid NoncentralPlane where
  r U W := ∃ A : SL, U.1.1.map (action A).toLinearMap = W.1.1
  iseqv := {
    refl := fun U => (orbit_iff_determinant U.1 U.1).mpr rfl
    symm := fun {U W} h => (orbit_iff_determinant W.1 U.1).mpr
      ((orbit_iff_determinant U.1 W.1).mp h).symm
    trans := fun {U W Z} h k => (orbit_iff_determinant U.1 Z.1).mpr
      (((orbit_iff_determinant U.1 W.1).mp h).trans ((orbit_iff_determinant W.1 Z.1).mp k)) }

/-- The three noncentral SL orbits are indexed by the three nonzero determinants. -/
noncomputable def noncentralOrbitEquiv : Quotient noncentralOrbitSetoid ≃ NonzeroDeterminant :=
  (Quotient.congrRight (r := noncentralOrbitSetoid) (r' := Setoid.ker noncentralDeterminant) (fun U W => by
    change (∃ A : SL, U.1.1.map (action A).toLinearMap = W.1.1) ↔
      noncentralDeterminant U = noncentralDeterminant W
    rw [Subtype.ext_iff]
    exact orbit_iff_determinant U.1 W.1)).trans
    (Setoid.quotientKerEquivOfSurjective noncentralDeterminant noncentralDeterminant_surjective)

lemma card_noncentral_orbits : Nat.card (Quotient noncentralOrbitSetoid) = 3 := by
  rw [Nat.card_congr noncentralOrbitEquiv, Nat.card_eq_fintype_card]
  decide +kernel

lemma card_noncentral_orbit (U : NoncentralPlane) :
    Nat.card {W : NoncentralPlane // noncentralOrbitSetoid.r U W} = 10 := by
  have e : {W : NoncentralPlane // noncentralOrbitSetoid.r U W} ≃
      {W : Plane // determinant W = determinant U.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun W : Plane => ¬ IsFieldLine W.1)
      (fun W : Plane => ∃ A : SL, U.1.1.map (action A).toLinearMap = W.1)).trans
      (Equiv.subtypeEquivRight (fun W => by
        rw [orbit_iff_determinant]
        constructor
        · exact fun h => h.2.symm
        · intro h
          refine ⟨?_,h.symm⟩
          intro hW
          apply U.2
          apply (determinant_zero_iff U.1).mp
          rw [← h]
          exact (determinant_zero_iff W).mpr hW))
  rw [Nat.card_congr e, card_determinant_fiber]
  exact if_neg (show determinant U.1 ≠ 0 from (noncentralDeterminant U).2)

end Representation.SL2FourNatural.PlaneGeometry
