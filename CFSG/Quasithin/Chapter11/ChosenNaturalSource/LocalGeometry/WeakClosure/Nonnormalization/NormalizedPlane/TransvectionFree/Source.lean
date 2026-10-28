module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.RootPair.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Flag

/-!
# The original normalized-pair plane action and its source consumer

Plane fixation removes the field and scalar parts of each involutory actor.
The original central-cover uniqueness theorem lifts that inner action to the
whole chosen module. Its literal kernel is C_A(V), so reciprocal corank 2n
gives image order q² in the marked plane radical. The quadratic-refinement
bound then forces the entire original plane preimage into the commutator.
This excludes the strict-commutator branch, including nonsplit central covers,
and reciprocal Sylow transport supplies the requested ambient alignment.

The final consumers remove the plane-alignment premise from all three source
conclusions and from the actual critical-pair obstruction. Reciprocal small-root
recognition and the preceding offender/parabolic calculation remain explicit
obligations of qt-d-1222-natural-conjugate-nonnormalization. Earlier numerical,
G2, flag and relative-component premises remain with the named parent
qt-d-1222-natural-weak-closure-source. These conditional consumers do not yet
establish the whole source theorem.

Source: Aschbacher--Smith, 11.2.4--5, printed pp.769--770. The central-cover
quadratic-refinement argument replaces the final transvection-root detour.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Matrix Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))

private theorem plane_field_large : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) S.nonbinary

/-- The displayed invariant flag uses the basis of the original inner Sylow. -/
theorem flag_space_eq (i : Fin 3) : f.space i = Sp4.space m i.succ :=
  Sp4.space_inner_unique m i (f.space i) (f.dimension i)
    (inf_le_left.trans (f.invariant i))

private theorem quotient_fixes_plane {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) (a : A)
    (v : Vector S.field.Carrier) (hv : v ∈ f.space 1) :
    quotientAction D S m (inclusion hA a) v = v := by
  let c := Coordinates.sp4 m
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hwP : (w : G) ∈ f.Vi 1 := (c.mem_preimage _ w).mpr (by
    change (c.projection w).toAdd ∈ f.space 1
    rw [hw]
    exact hv)
  have hc := mem_centralizer_iff.mp (hfix hwP) a.val a.property
  have he : V.normalizerMonoidHom (inclusion hA a) w = w := by
    apply Subtype.ext
    change (a:G) * (w:G) * (a:G)⁻¹ = (w:G)
    rw [hc,mul_inv_cancel_right]
  have hh := quotientAction_projection D S m (inclusion hA a) w
  rw [he,hw] at hh
  exact hh

private theorem plane_actor_inner {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) (a : A) :
    linearAction (quotientAction D S m) (inclusion hA a) ∈ naturalDerivedImage := by
  have hn : f.space 1 ≠ ⊥ := by
    intro hz
    have hd := f.dimension 1
    rw [hz,finrank_bot] at hd
    norm_num at hd
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  exact quotientAction_inner_of_line D S m (inclusion hA a)
    (by rw [←map_pow,hsq,map_one]) v hv0
    (fun t => quotient_fixes_plane m f hA hfix a _ ((f.space 1).smul_mem t hv))

/-- The actual homomorphism to Sp₄ for plane-fixing elementary actors. -/
def planeHom {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) : A →* Sp S.field.Carrier :=
  (SymplecticNaturalNormalizer.naturalEquiv (plane_field_large (S := S))).symm.toMonoidHom.comp
    (((linearAction (quotientAction D S m)).comp (inclusion hA)).codRestrict
      naturalDerivedImage (plane_actor_inner m f hA hsq hfix))

theorem planeHom_quotient {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) (a : A) :
    SymplecticNaturalNormalizer.naturalHom (planeHom m f hA hsq hfix a) =
      linearAction (quotientAction D S m) (inclusion hA a) := by
  exact congrArg Subtype.val
    ((SymplecticNaturalNormalizer.naturalEquiv (plane_field_large (S := S))).apply_symm_apply _)

/-- This equality is on the full original module, including its central kernel. -/
theorem planeHom_action {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) (a : A) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (planeHom m f hA hsq hfix a) v)) : G) =
        (a : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (a : G)⁻¹ := by
  rw [←fullAction_eq_marked D S m (inclusion hA a) _
    (planeHom_quotient m f hA hsq hfix a).symm]
  exact fullAction_conjugation D _ v

private theorem planeHom_ker {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) :
    (planeHom m f hA hsq hfix).ker = (A ⊓ centralizer (V : Set G)).subgroupOf A := by
  ext a
  constructor
  · intro ha
    refine ⟨a.property,mem_centralizer_iff.mpr ?_⟩
    intro v hv
    obtain ⟨w,hw⟩ := D.spaceEquiv.surjective ⟨v,hv⟩
    have hh := planeHom_action m f hA hsq hfix a w.toAdd
    rw [show planeHom m f hA hsq hfix a = 1 from ha,map_one] at hh
    change (D.spaceEquiv w : G) = (a:G) * (D.spaceEquiv w : G) * (a:G)⁻¹ at hh
    rw [hw] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · rintro ⟨_,ha⟩
    change planeHom m f hA hsq hfix a = 1
    apply SymplecticNaturalNormalizer.naturalHom_injective
    rw [planeHom_quotient,map_one]
    apply LinearEquiv.ext
    intro v
    let c := Coordinates.sp4 m
    obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    have he : V.normalizerMonoidHom (inclusion hA a) w = w := by
      apply Subtype.ext
      change (a:G) * (w:G) * (a:G)⁻¹ = (w:G)
      have hc : (w : G) * (a : G) = (a : G) * (w : G) :=
        mem_centralizer_iff.mp ha w.val w.property
      rw [←hc,mul_inv_cancel_right]
    have hh := quotientAction_projection D S m (inclusion hA a) w
    rw [he,hw] at hh
    exact hh

/-- The image order is computed from the literal ambient action kernel. -/
theorem planeHom_card {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) :
    Nat.card (planeHom m f hA hsq hfix).range =
      2 ^ subgroupCorank A (A ⊓ centralizer (V : Set G)) := by
  rw [←index_ker,planeHom_ker]
  change (A ⊓ centralizer (V : Set G)).relIndex A = _
  rw [subgroupCorank_eq_quotient_finrank,relIndex_eq_two_pow_quotient_finrank]

private theorem mem_radical_of_fixes_plane (g : Sp S.field.Carrier)
    (hfix : ∀ v ∈ plane S.field.Carrier, g • v = v) :
    g ∈ Plane.radical.map planeLocal.subtype := by
  have hB : g.val.toBlocks₁₁ = 1 := by
    ext i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inl i)
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single,Matrix.toBlocks₁₁,Matrix.one_apply,Pi.single_apply] using h
  have hP : g ∈ planeParabolic := by
    rw [mem_planeParabolic_iff]
    intro i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inr i)
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single] using h
  have hg : g ∈ planeLocal := (Plane.mem_local_iff g).mpr
    ⟨hP,by rw [hB]; exact Matrix.det_one⟩
  refine ⟨⟨g,hg⟩,?_,rfl⟩
  apply Subtype.ext
  exact hB

/-- The homomorphism takes values in the radical of this same marked plane. -/
theorem planeHom_range {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A : Set G)) :
    (planeHom m f hA hsq hfix).range ≤
      (Plane.radical.map planeLocal.subtype).map (MulAut.conj (Sp4.alignment m)).toMonoidHom := by
  rintro _ ⟨a,rfl⟩
  let b := Sp4.alignment m
  let x := planeHom m f hA hsq hfix a
  have hfix' : ∀ v ∈ (plane S.field.Carrier).map (symplecticNatural 2 b), x • v=v := by
    intro v hv
    have hv' : v ∈ f.space 1 := by
      rw [flag_space_eq]
      exact hv
    have h := LinearEquiv.congr_fun (planeHom_quotient m f hA hsq hfix a) v
    exact h.trans (quotient_fixes_plane m f hA hfix a v hv')
  refine ⟨b⁻¹*x*b,mem_radical_of_fixes_plane (S := S) _ ?_,?_⟩
  · intro v hv
    have h := hfix' (b • v) ⟨v,hv,rfl⟩
    simp only [mul_smul,h,inv_smul_smul]
  · change b * (b⁻¹*x*b) * b⁻¹ = x
    group

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree

end

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Plane fixation and the literal actor corank saturate the original cover.
This includes the nonsplit central kernel, without a root-avoidance hypothesis. -/
theorem plane_le_commutator_of_corank
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A : Set G))
    (hcorank : subgroupCorank A (A ⊓ centralizer (V : Set G)) = 2 * S.field.degree) :
    f.Vi 1 ≤ ⁅V,A⁆ := by
  have hsq : ∀ a : A, a^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)
  apply RootPair.plane_le_commutator_of_action m f A (planeHom m f hA hsq hfix)
    (Sp4.alignment m)
  · exact flag_space_eq m f 1
  · exact planeHom_action m f hA hsq hfix
  · exact planeHom_range m f hA hsq hfix
  · rw [planeHom_card,hcorank]

/-- The normalized symplectic pair has the full plane commutator. The
reciprocal parabolic geometry supplies the actual actor corank internally. -/
theorem symplectic_commutator_eq
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = f.Vi 1 := by
  let := D.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj g).toMonoidHom
  have hgeom := hp g hg hne
  apply le_antisymm (le_sup_left.trans_eq hgeom.quotient_plane)
  apply plane_le_commutator_of_corank m f _ (hg.trans S.sylow_normalizes)
  · exact hgeom.fixed_plane.symm.le.trans inf_le_right
  · exact (symplectic_action_coranks m f hp g hg hne hn).1

/-- All natural rows now give normalized-pair plane alignment from the
preceding uniform parabolic calculation. There is no plane-action callback. -/
theorem alignment_of_parabolic {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Alignment (f.Vi 1) V g := by
  apply alignment_of_equal_commutator f hp g hne hn
  cases c with
  | sl3 m =>
    simpa only [Preliminary.sl3_centralizer_eq_bot D S m,sup_bot_eq]
      using (hp g hg hne).quotient_plane
  | sp4 m => exact symplectic_commutator_eq m f hp g hg hne hn
  | g2 m => exact (hG2 ⟨m⟩).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree

end

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.2.4 after discharging normalized-pair plane alignment.
The small-root recognition and offender calculations remain explicit local obligations. -/
theorem conclusions_of_root_and_parabolic {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hroot : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ∀ W : Subgroup G, SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W →
      W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 0) V g)
    (hparabolic : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom)) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_geometry D S f hab hW hSL3 hparameters hK P hfix hroot hparabolic
  intro g hg hne hsmall _ hn
  exact NormalizedPlane.TransvectionFree.alignment_of_parabolic f hG2
    (fun k hk hkne => hparabolic k hk hkne hsmall) g hg hne hn

/-- Application to the actual constructed critical pair, with the same remaining local inputs. -/
theorem obstruction_of_root_and_parabolic {c : Coordinates D S.field} (f : InvariantFlag c)
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
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hroot : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ∀ W : Subgroup G, SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W →
      W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 0) V g)
    (hparabolic : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom)) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  apply obstruction_of_nonnormalization D S H hTH hout f hSL3
  intro hSL3' hab hW
  exact (conclusions_of_root_and_parabolic D S f hab hW hSL3' hparameters hK P hfix
    hG2 hroot hparabolic).2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization

end
