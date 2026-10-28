module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Outside.Plane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Outside.Radical

/-!
# The outside-radical calculation on the original natural modules

Fixing the first field line removes coefficient automorphisms. In the
symplectic row each involution then lies in the actual Sp₄ image, and
uniqueness of the full-cover action lifts it to the original module.
In SL₃ the original projection is injective. Thus quotient fixed vectors
are precisely commuting elements in both rows.

The preceding plane calculation computes the two literal centralizer
coranks and the first-line commutator. An actor outside O₂(L₂T) cannot
centralize the plane, so it gives exactly the small symmetric action
excluded by reciprocal root recognition. First-line fixation and s(G,V)=n
are the authorized earlier 11.2.2 inputs, retained for the final source owner.

Source: Aschbacher--Smith, 11.2.2(3--4) and 11.2.4, printed pp.768--769;
the nonsplit fixed-lifting calculation is I.2.3(1b), printed p.413.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Outside
open NormalizedPlane.TransvectionFree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem quotient_fixes_point {c : Coordinates D S.field}
    (f : InvariantFlag c) {A : Subgroup G} (hA : A≤normalizer (V:Set G))
    (hfix : f.Vi 0≤centralizer (A:Set G)) (a:A) (x:c.Space) (hx:x∈f.space 0) :
    c.conjugationAction (hA.trans (seed_normalizer_le D S)) hA a x=x := by
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
  have hp : (v:G)∈f.Vi 0 := (c.mem_preimage _ v).mpr (by
    change (c.projection v).toAdd∈f.space 0
    rwa [hv])
  have he : V.normalizerMonoidHom (inclusion hA a) v=v := by
    apply Subtype.ext
    change (a:G)*(v:G)*(a:G)⁻¹=(v:G)
    rw [hfix hp a.val a.property,mul_inv_cancel_right]
  have hh := c.conjugationAction_projection (hA.trans (seed_normalizer_le D S)) hA a v
  rw [he,hv] at hh
  exact hh

private theorem sl3_linear_of_point_fixed
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hfix : f.Vi 0≤centralizer (A:Set G)) (a:A) :
    ∀ (r:S.field.Carrier) (x:(Coordinates.sl3 m).Space),
      (Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a (r • x)=
      r • (Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a x := by
  let E : Closure.Geometry D :=
    { input := S
      point := (Coordinates.sl3 m).binarySubspace (f.space 0)
      plane := (Coordinates.sl3 m).binarySubspace (f.space 1)
      threeSpace := (Coordinates.sl3 m).binarySubspace (f.space 2)
      X := ⊥,z := 1,H := ⊥ }
  obtain ⟨σ,hσ⟩ := Closure.Amalgam.Even.Linear.normalizerAction_semilinear
    (E := E) m (inclusion hA a)
  have hs (r:S.field.Carrier) (x:(Coordinates.sl3 m).Space) :
      (Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a (r • x)=
      σ r • (Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a x := by
    simpa only [Closure.Amalgam.Even.Linear.normalizerAction_restrict
      (E := E) m A (hA.trans (seed_normalizer_le D S)) hA] using hσ r x
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (f.space_ne_bot 0)
  have he (r:S.field.Carrier) : σ r=r := by
    have hh := hs r x
    rw [quotient_fixes_point f hA hfix a x hx,
      quotient_fixes_point f hA hfix a (r • x) ((f.space 0).smul_mem r hx)] at hh
    exact (smul_left_injective S.field.Carrier hx0) hh.symm
  intro r x
  rw [hs,he]

def sl3PointAction
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hfix : f.Vi 0≤centralizer (A:Set G)) :
    Representation S.field.Carrier A (Coordinates.sl3 m).Space where
  toFun a := {
    toFun := (Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a
    map_add' := ((Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a).map_add
    map_smul' := sl3_linear_of_point_fixed m f hA hfix a }
  map_one' := by
    ext x
    exact LinearMap.congr_fun (map_one ((Coordinates.sl3 m).conjugationAction
      (hA.trans (seed_normalizer_le D S)) hA)) x
  map_mul' a b := by
    ext x
    exact LinearMap.congr_fun (map_mul ((Coordinates.sl3 m).conjugationAction
      (hA.trans (seed_normalizer_le D S)) hA) a b) x

theorem sl3PointAction_projection
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hfix : f.Vi 0≤centralizer (A:Set G)) (a:A) (v:V) :
    sl3PointAction m f hA hfix a ((Coordinates.sl3 m).projection v).toAdd=
      ((Coordinates.sl3 m).projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd :=
  (Coordinates.sl3 m).conjugationAction_projection (hA.trans (seed_normalizer_le D S)) hA a v

variable (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))

private theorem field_large : 2<Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1<(2:ℕ)) S.nonbinary

private theorem point_actor_inner {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 0≤centralizer (A:Set G)) (a:A) :
    linearAction (quotientAction D S m) (inclusion hA a)∈naturalDerivedImage := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (f.space_ne_bot 0)
  apply quotientAction_inner_of_line D S m (inclusion hA a)
    (by rw [←map_pow,hsq,map_one]) x hx0
  intro r
  have hh := quotient_fixes_point f hA hfix a (r • x) ((f.space 0).smul_mem r hx)
  have hp : (Coordinates.sp4 m).conjugationAction
      (hA.trans (seed_normalizer_le D S)) hA a (r • x)=
      quotientAction D S m (inclusion hA a) (r • x) := by
    obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd (r • x))
    have he := (Coordinates.sp4 m).conjugationAction_projection
      (hA.trans (seed_normalizer_le D S)) hA a v
    rw [←quotientAction_projection D S m (inclusion hA a) v,hv] at he
    exact he
  exact hp.symm.trans hh

def pointHom {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 0≤centralizer (A:Set G)) : A →* Sp S.field.Carrier :=
  (SymplecticNaturalNormalizer.naturalEquiv (field_large (S := S))).symm.toMonoidHom.comp
    (((linearAction (quotientAction D S m)).comp (inclusion hA)).codRestrict
      naturalDerivedImage (point_actor_inner m f hA hsq hfix))

theorem pointHom_quotient {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 0≤centralizer (A:Set G)) (a:A) :
    SymplecticNaturalNormalizer.naturalHom (pointHom m f hA hsq hfix a)=
      linearAction (quotientAction D S m) (inclusion hA a) := by
  exact congrArg Subtype.val
    ((SymplecticNaturalNormalizer.naturalEquiv (field_large (S := S))).apply_symm_apply _)

theorem pointHom_action {A : Subgroup G}
    (hA : A≤normalizer (V:Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 0≤centralizer (A:Set G)) (a:A) (v:D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (pointHom m f hA hsq hfix a) v)):G)=
        (a:G)*(D.spaceEquiv (Multiplicative.ofAdd v):G)*(a:G)⁻¹ := by
  rw [←fullAction_eq_marked D S m (inclusion hA a) _
    (pointHom_quotient m f hA hsq hfix a).symm]
  exact fullAction_conjugation D _ v


omit m f in
theorem small_action_of_noncentral_plane {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    [IsElementaryAbelian 2 V] (hs : globalS V=S.field.degree)
    (g:G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (hpoint : f.Vi 0≤centralizer (V.map (MulAut.conj g).toMonoidHom:Set G))
    (hne : ⁅f.Vi 1,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let hA := hg.trans S.sylow_normalizes
  cases c with
  | g2 m => exact (hG2 ⟨m⟩).elim
  | sl3 m =>
    let c := Coordinates.sl3 m
    let ρ := sl3PointAction m f hA hpoint
    apply small_action_of_plane_action f g hg hs ρ
      (sl3PointAction_projection m f hA hpoint) ?_ ?_ hne
    · exact fun a x hx => quotient_fixes_point f hA hpoint a x hx
    · intro a v
      constructor
      · intro he
        rw [sl3PointAction_projection] at he
        have hp := Multiplicative.toAdd.injective he
        have hπ : Function.Injective c.projection := by
          apply (MonoidHom.ker_eq_bot_iff c.projection).mp
          apply bot_unique
          intro w hw
          have hc := (c.projection_eq_one_iff w).mp hw
          have hz : (w:G)∈V ⊓ centralizer (L:Set G) := ⟨w.property,hc⟩
          rw [Preliminary.sl3_centralizer_eq_bot D S m] at hz
          exact Subtype.ext (mem_bot.mp hz)
        have he' := congrArg Subtype.val (hπ hp)
        exact mul_inv_eq_iff_eq_mul.mp he'
      · intro he
        rw [sl3PointAction_projection]
        congr 2
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr he
  | sp4 m =>
    letI : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    have hsq : ∀a:A,a^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A)
    let actor := pointHom m f hA hsq hpoint
    let ρ : Representation S.field.Carrier A (Coordinates.sp4 m).Space :=
      (symplecticNatural 2).comp actor
    have hπ (a:A) (v:V) : ρ a ((Coordinates.sp4 m).projection v).toAdd=
        ((Coordinates.sp4 m).projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd := by
      have hh := LinearEquiv.congr_fun (pointHom_quotient m f hA hsq hpoint a)
        ((Coordinates.sp4 m).projection v).toAdd
      exact hh.trans (quotientAction_projection D S m (inclusion hA a) v)
    have hlift := sp4_projection_fixed_iff_commute m A actor (pointHom_action m f hA hsq hpoint)
    apply small_action_of_plane_action f g hg hs ρ hπ ?_ hlift hne
    intro a x hx
    obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd x)
    have hp : (v:G)∈f.Vi 0 := ((Coordinates.sp4 m).mem_preimage _ v).mpr (by
      change ((Coordinates.sp4 m).projection v).toAdd∈f.space 0
      rwa [hv])
    have hh := (hlift a v).mpr (hpoint hp a.val a.property)
    change ρ a ((Coordinates.sp4 m).projection v).toAdd=((Coordinates.sp4 m).projection v).toAdd at hh
    rw [hv] at hh
    exact hh

omit m f in
/-- Outside the literal radical the plane action is nontrivial; its actual
centralizer kernels and quotient commutator give the forbidden small action. -/
theorem small_action_of_outside_radical {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    [IsElementaryAbelian 2 V] (hs : globalS V=S.field.degree)
    (g:G) (hg : V.map (MulAut.conj g).toMonoidHom≤T)
    (hpoint : f.Vi 0≤centralizer (V.map (MulAut.conj g).toMonoidHom:Set G))
    (hout : ¬ V.map (MulAut.conj g).toMonoidHom≤f.Ri 1) :
    SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1) := by
  apply small_action_of_noncentral_plane f hG2 hs g hg hpoint
  intro hz
  apply hout
  apply (le_inf hg (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hz))).trans
  exact sylow_plane_centralizer_le_radical f hG2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Outside
