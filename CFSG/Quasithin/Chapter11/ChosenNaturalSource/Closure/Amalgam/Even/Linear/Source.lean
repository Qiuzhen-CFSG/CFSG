module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.Alignment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.SmallCommutator
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Critical

/-!
# The SL₃ pair after the preceding point-core action

The point-core bound gives a commutator of order at most q. Semilinear
involutions have larger displacement, so the acting conjugate is field-linear.
One nonzero displacement supplies a full field line, forcing equality with V₁.
Reverse the literal commutator under g⁻¹ and apply the same small-displacement
argument to obtain the line on the second module. Actual SL₃ line transitivity
then gives the right correction g*l and the elementary-closure contradiction.

The independent point-core bound [V,R₁] ≤ V₁ remains explicit. Its producer
is qt-d-1222-amalgam-even-sl3-point-core; final assembly remains with the
SL₃ task. Fixed-space vanishing is the preceding 11.4.1 conclusion owned by
qt-d-1222-shadow-components. This is not yet an unconditional proof of the
SL₃ branch of 11.5.8.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Closure.Geometry D}
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
  (f : InvariantFlag (.sl3 m)) (hm : FlagMatch E f)

include m f hm

private theorem point_card (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card E.V₁ = Nat.card E.input.field.Carrier := by
  rw [← hm.point_eq, InvariantFlag.Vi,
    Nonabelian.card_preimage (.sl3 m) hfixed, f.dimension, E.input.field.card_eq]
  simp

omit m f hm [Finite G] in
private theorem map_conj_inv_conj (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, MonoidHom.id_apply]
    group
  rw [he, map_id]

/-- The reciprocal field line follows from the small literal commutator.
No assumption about the inverse conjugate's placement in R₁ is needed. -/
theorem reciprocal_fieldLine (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (g : G) (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = E.V₁)
    (hle : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    IsFieldLine E (.sl3 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom) := by
  let A := V.map (MulAut.conj g⁻¹).toMonoidHom
  have hAV : ⁅A, V⁆ = E.V₁.map (MulAut.conj g⁻¹).toMonoidHom := by
    have he := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hcomm
    rw [map_commutator] at he
    have hv : (V.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = V := by
      simpa only [inv_inv] using map_conj_inv_conj V g⁻¹
    rw [hv] at he
    exact he
  have hn : A ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hle.trans inf_le_right)
    rw [map_commutator] at hh
    have hv : (V.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = V := by
      simpa only [inv_inv] using map_conj_inv_conj V g⁻¹
    rwa [hv] at hh
  have hne : ⁅A, V⁆ ≠ ⊥ := by
    rw [hAV]
    intro hz
    have hp := (map_eq_bot_iff_of_injective E.V₁ (MulAut.conj g⁻¹).injective).mp hz
    exact f.V_ne_bot 0 (hm.point_eq.trans hp)
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hc : Nat.card (⁅A, V⁆ : Subgroup G) ≤ Nat.card E.input.field.Carrier := by
    rw [hAV, card_map_of_injective (MulAut.conj g⁻¹).injective, point_card m f hm hfixed]
  rw [← hAV]
  exact commutator_isFieldLine_of_card_le m hfixed A hn
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A)) hne hc

/-- Discharge the SL₃ quadratic alternatives using the earlier natural
point-core action bound. The bound concerns all of R₁, independently of a
critical pair; its source producer remains a separate prerequisite. -/
theorem critical_pair_geometry_of_core_bound
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hcore : ⁅V, E.R₁⁆ ≤ E.V₁)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hle : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = E.V₁ ∧
      IsFieldLine E (.sl3 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom) := by
  let B := V.map (MulAut.conj g).toMonoidHom
  have hp : ⁅V, B⁆ ≤ E.V₁ := (commutator_mono le_rfl hg).trans hcore
  have hBV : B ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hle.trans inf_le_left)
  let := D.elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hc : Nat.card (⁅B, V⁆ : Subgroup G) ≤ Nat.card E.input.field.Carrier := by
    rw [commutator_comm]
    exact (card_le_of_le hp).trans_eq (point_card m f hm hfixed)
  have hn : ⁅B, V⁆ ≠ ⊥ := by rw [commutator_comm]; exact hne
  obtain ⟨U, hU, he⟩ := commutator_isFieldLine_of_card_le m hfixed B hBV
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B)) hn hc
  have hcard : Nat.card (⁅V, B⁆ : Subgroup G) = Nat.card E.V₁ := by
    rw [commutator_comm, ← he, Nonabelian.card_preimage (.sl3 m) hfixed U,
      hU, pow_one, point_card m f hm hfixed, E.input.field.card_eq]
  have heq : ⁅V, B⁆ = E.V₁ := eq_of_le_of_card_ge hp hcard.ge
  exact ⟨heq, reciprocal_fieldLine m f hm hfixed g heq hle⟩

/-- The literal pair contradicts the elementary closure once its earlier
point-core action has been supplied. Alignment is constructed, not assumed. -/
theorem false_of_critical_pair_of_core_bound
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hcore : ⁅V, E.R₁⁆ ≤ E.V₁) (hab : IsMulCommutative E.W)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hle : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) : False := by
  have hp := critical_pair_geometry_of_core_bound m f hm hfixed hcore g hg hne hle
  exact hne (commutes_of_fieldLine m f hm hab g hp.2)

/-- Apply the geometric contradiction to the exact pair constructed by F.7.
The only new action premise is the independent preceding point-core bound. -/
theorem not_even_of_core_bound
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hcore : ⁅V, E.R₁⁆ ≤ E.V₁) (hab : IsMulCommutative E.W)
    (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    ¬ Even (distance E h hout) := by
  intro he
  obtain ⟨g, hg, hn, hc⟩ := exists_critical_conjugate_in_R₁ E h hout he
  exact false_of_critical_pair_of_core_bound m f hm hfixed hcore hab g hg hn hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
