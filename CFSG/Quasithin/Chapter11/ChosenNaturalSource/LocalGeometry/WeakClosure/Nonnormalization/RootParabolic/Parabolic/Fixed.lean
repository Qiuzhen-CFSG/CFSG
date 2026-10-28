module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.Action

/-!
# The exact fixed plane on the original natural module

A compatible field-linear action identifies the literal group commutator,
joined with C_V(L), with the preimage of its displacement space. In the Sp₄
row the displacement plane is self-orthogonal, and the full-cover fixed-lifting
theorem identifies its original centralizer without a splitting assumption.
In the SL₃ row, plane fixation eliminates the field automorphism; dimension
three then forces precisely the plane as the common fixed space.

The actual parabolic consumer discharges its fixed-plane and centralizer-span
clauses from the first two local calculations and the preceding flag theorem
R₂ ≤ C_G(V₂). That earlier flag input belongs to
qt-d-1222-natural-flag-cartan and is discharged by the final owner
qt-d-1222-natural-weak-closure-source. The outside-radical and
proper-displacement calculations remain with this module's nonnormalization
owner; the conditional consumer is not yet the complete source 11.2.4.

Source: Aschbacher--Smith, 11.2.4, printed p.769; the nonsplit fixed lifting
uses the actual cover from I.2.3(1b), printed p.413.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem commutator_le_preimage_displacement {c : Coordinates D S.field}
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (ρ : Representation S.field.Carrier A c.Space)
    (hρ : ∀ (a : A) (v : V), ρ a (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd) :
    ⁅V,A⁆ ≤ c.preimage (Coinvariants.ker ρ) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha v hv
  let w : V := V.normalizerMonoidHom (inclusion hA ⟨a,ha⟩) ⟨v,hv⟩ * (⟨v,hv⟩ : V)⁻¹
  change (w:G) ∈ c.preimage (Coinvariants.ker ρ)
  apply (c.mem_preimage _ w).mpr
  change (c.projection w).toAdd ∈ Coinvariants.ker ρ
  change (c.projection (V.normalizerMonoidHom (inclusion hA ⟨a,ha⟩) ⟨v,hv⟩ *
    (⟨v,hv⟩ : V)⁻¹)).toAdd ∈ _
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,←hρ]
  exact Coinvariants.sub_mem_ker (ρ := ρ) (⟨a,ha⟩ : A) _


/-- The original group commutator modulo the full central kernel is exactly
the field-linear displacement space, when the actual action is field-linear. -/
theorem preimage_displacement_eq_commutator_sup {c : Coordinates D S.field}
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (ρ : Representation S.field.Carrier A c.Space)
    (hρ : ∀ (a : A) (v : V), ρ a (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd) :
    c.preimage (Coinvariants.ker ρ)=⁅V,A⁆ ⊔ (V ⊓ centralizer (L:Set G)) := by
  have hs : ∀ x∈Coinvariants.ker ρ, ∀ r : S.field.Carrier,
      ∃ v : V, (v:G)∈⁅V,A⁆ ∧ (c.projection v).toAdd=r • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a,y⟩,rfl⟩ := hx
      intro r
      obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd (r • y))
      let w : V := V.normalizerMonoidHom (inclusion hA a) v*v⁻¹
      refine ⟨w,?_,?_⟩
      · rw [commutator_comm]
        exact commutator_mem_commutator a.property v.property
      · change (c.projection (V.normalizerMonoidHom (inclusion hA a) v*v⁻¹)).toAdd=_
        rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,←hρ,hv]
        simp only [toAdd_ofAdd,map_smul,smul_sub]
    | zero =>
      intro r
      exact ⟨1,one_mem _,by simp⟩
    | add x y hx hy ihx ihy =>
      intro r
      obtain ⟨v,hv,hvx⟩ := ihx r
      obtain ⟨w,hw,hwy⟩ := ihy r
      exact ⟨v*w,mul_mem hv hw,by rw [map_mul,toAdd_mul,hvx,hwy,smul_add]⟩
    | smul r x hx ih =>
      intro s
      simpa only [smul_smul] using ih (s*r)
  apply le_antisymm
  · intro v hv
    have hvV := D.centralQuotientPreimage_le _ hv
    have hxp := (c.mem_preimage _ ⟨v,hvV⟩).mp hv
    change (c.projection ⟨v,hvV⟩).toAdd∈Coinvariants.ker ρ at hxp
    obtain ⟨w,hw,hwp⟩ := hs _ hxp 1
    simp only [one_smul] at hwp
    have he : c.projection w=c.projection ⟨v,hvV⟩ := Multiplicative.toAdd.injective hwp
    have hk : (v*(w:G)⁻¹)∈V ⊓ centralizer (L:Set G) := by
      refine ⟨V.mul_mem hvV (V.inv_mem w.property),?_⟩
      apply (c.projection_eq_one_iff (⟨v,hvV⟩*w⁻¹)).mp
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hh := (⁅V,A⁆ ⊔ (V ⊓ centralizer (L:Set G))).mul_mem
      (mem_sup_right hk) (mem_sup_left hw)
    simpa only [inv_mul_cancel_right] using hh
  · apply sup_le (commutator_le_preimage_displacement hA ρ hρ)
    rw [←c.preimage_bot]
    exact (c.preimage_le_iff _ _).mpr bot_le

private theorem displacement_eq_of_quotient_commutator {c : Coordinates D S.field}
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (ρ : Representation S.field.Carrier A c.Space)
    (hρ : ∀ (a : A) (v : V), ρ a (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd)
    (P : Submodule S.field.Carrier c.Space)
    (hmove : ⁅V,A⁆ ⊔ (V ⊓ centralizer (L:Set G)) = c.preimage P) :
    Coinvariants.ker ρ = P := by
  apply c.preimage_injective
  rw [preimage_displacement_eq_commutator_sup hA ρ hρ,hmove]

open NormalizedPlane.TransvectionFree
variable (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private theorem planeHom_projection (f : InvariantFlag (Coordinates.sp4 m))
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A:Set G)) (a : A) (v : V) :
    (symplecticNatural 2 (planeHom m f hA hsq hfix a)) ((Coordinates.sp4 m).projection v).toAdd =
      ((Coordinates.sp4 m).projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd := by
  have hh := LinearEquiv.congr_fun (planeHom_quotient m f hA hsq hfix a)
    ((Coordinates.sp4 m).projection v).toAdd
  exact hh.trans (quotientAction_projection D S m (inclusion hA a) v)

/-- Full original quotient-plane displacement identifies the fixed subgroup,
including every vector of the nonsplit central kernel. -/
theorem fixed_plane_of_sp4_quotient_plane (f : InvariantFlag (Coordinates.sp4 m))
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A:Set G))
    (hmove : ⁅V,A⁆ ⊔ (V ⊓ centralizer (L:Set G))=f.Vi 1) :
    V ⊓ centralizer (A:Set G)=f.Vi 1 := by
  let c := Coordinates.sp4 m
  let actor := planeHom m f hA hsq hfix
  let ρ : Representation S.field.Carrier A (Vector S.field.Carrier) :=
    (symplecticNatural 2).comp actor
  have hd : displacementSpace actor.range=f.space 1 := by
    rw [displacementSpace_range_eq]
    exact displacement_eq_of_quotient_commutator (c := Coordinates.sp4 m) (S := S) hA ρ
      (planeHom_projection m f hA hsq hfix) _ hmove
  have hf : Theory.SpecificGroups.SymplecticFour.TwoLocalCover.fixedSpace actor.range=f.space 1 := by
    rw [←orthogonal_displacementSpace,hd,flag_plane_self_orthogonal m f]
  apply le_antisymm
  · intro v hv
    apply (c.mem_preimage _ ⟨v,hv.1⟩).mpr
    change (c.projection ⟨v,hv.1⟩).toAdd∈f.space 1
    rw [←hf]
    rintro _ ⟨a,rfl⟩
    exact (sp4_projection_fixed_iff_commute m A actor
      (planeHom_action m f hA hsq hfix) a ⟨v,hv.1⟩).mpr
      (mem_centralizer_iff.mp hv.2 a.val a.property)
  · exact le_inf (D.centralQuotientPreimage_le _) hfix


omit m in
private theorem quotient_fixes_preimage {c : Coordinates D S.field}
    (f : InvariantFlag c) {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A:Set G)) (a : A)
    (v : c.Space) (hv : v∈f.space 1) :
    c.conjugationAction (hA.trans (seed_normalizer_le D S)) hA a v=v := by
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hp : (w:G)∈f.Vi 1 := (c.mem_preimage _ w).mpr (by
    change (c.projection w).toAdd∈f.space 1
    rwa [hw])
  have he : V.normalizerMonoidHom (inclusion hA a) w=w := by
    apply Subtype.ext
    change (a:G)*(w:G)*(a:G)⁻¹=(w:G)
    rw [hfix hp a.val a.property,mul_inv_cancel_right]
  have hh := c.conjugationAction_projection (hA.trans (seed_normalizer_le D S)) hA a w
  rw [he,hw] at hh
  exact hh

omit m in
private theorem sl3_plane_action_linear
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A:Set G)) (a : A) :
    ∀ (r : S.field.Carrier) (v : (Coordinates.sl3 m).Space), (Coordinates.sl3 m).conjugationAction
      (hA.trans (seed_normalizer_le D S)) hA a (r • v) =
      r • (Coordinates.sl3 m).conjugationAction
        (hA.trans (seed_normalizer_le D S)) hA a v := by
  let E : Closure.Geometry D :=
    { input := S
      point := (Coordinates.sl3 m).binarySubspace (f.space 0)
      plane := (Coordinates.sl3 m).binarySubspace (f.space 1)
      threeSpace := (Coordinates.sl3 m).binarySubspace (f.space 2)
      X := ⊥, z := 1, H := ⊥ }
  obtain ⟨σ,hσ⟩ := Closure.Amalgam.Even.Linear.normalizerAction_semilinear
    (E := E) m (inclusion hA a)
  have hs (r : S.field.Carrier) (v : (Coordinates.sl3 m).Space) :
      (Coordinates.sl3 m).conjugationAction
        (hA.trans (seed_normalizer_le D S)) hA a (r • v) =
      σ r • (Coordinates.sl3 m).conjugationAction
        (hA.trans (seed_normalizer_le D S)) hA a v := by
    simpa only [Closure.Amalgam.Even.Linear.normalizerAction_restrict
      (E := E) m A (hA.trans (seed_normalizer_le D S)) hA] using hσ r v
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (f.space_ne_bot 1)
  have he (r : S.field.Carrier) : σ r=r := by
    have hh := hs r v
    rw [quotient_fixes_preimage f hA hfix a v hv,
      quotient_fixes_preimage f hA hfix a (r • v) ((f.space 1).smul_mem r hv)] at hh
    exact (smul_left_injective S.field.Carrier hv0) hh.symm
  intro r v
  rw [hs,he]

omit m in
/-- The literal plane fixer acts linearly on the original SL3 quotient:
fixing a nonzero field subspace removes its coefficient automorphism. -/
def sl3PlaneAction
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A:Set G)) :
    Representation S.field.Carrier A (Coordinates.sl3 m).Space where
  toFun a := {
    toFun := (Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a
    map_add' := ((Coordinates.sl3 m).conjugationAction (hA.trans (seed_normalizer_le D S)) hA a).map_add
    map_smul' := sl3_plane_action_linear m f hA hfix a }
  map_one' := by
    ext x
    exact LinearMap.congr_fun (map_one ((Coordinates.sl3 m).conjugationAction
      (hA.trans (seed_normalizer_le D S)) hA)) x
  map_mul' a b := by
    ext x
    exact LinearMap.congr_fun (map_mul ((Coordinates.sl3 m).conjugationAction
      (hA.trans (seed_normalizer_le D S)) hA) a b) x

omit m in
theorem sl3PlaneAction_projection
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A:Set G)) (a : A) (v : V) :
    sl3PlaneAction m f hA hfix a ((Coordinates.sl3 m).projection v).toAdd =
      ((Coordinates.sl3 m).projection (V.normalizerMonoidHom (inclusion hA a) v)).toAdd :=
  (Coordinates.sl3 m).conjugationAction_projection (hA.trans (seed_normalizer_le D S)) hA a v

omit m in
/-- A nontrivial field-linear action on the three-space fixing the plane
has exactly that plane as its fixed space. -/
theorem fixed_plane_of_sl3_quotient_plane
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hfix : f.Vi 1 ≤ centralizer (A:Set G))
    (hmove : ⁅V,A⁆ ⊔ (V ⊓ centralizer (L:Set G))=f.Vi 1) :
    V ⊓ centralizer (A:Set G)=f.Vi 1 := by
  let : FiniteDimensional S.field.Carrier (Coordinates.sl3 m).Space :=
    inferInstanceAs (FiniteDimensional S.field.Carrier (Fin 3 → S.field.Carrier))
  let c := Coordinates.sl3 m
  let ρ := sl3PlaneAction m f hA hfix
  have hd : Coinvariants.ker ρ=f.space 1 :=
    displacement_eq_of_quotient_commutator (c := Coordinates.sl3 m) (S := S) hA ρ (sl3PlaneAction_projection m f hA hfix) _ hmove
  have hP : f.space 1 ≤ ρ.invariants := by
    intro v hv a
    exact quotient_fixes_preimage f hA hfix a v hv
  have hn : ρ.invariants ≠ ⊤ := by
    intro ht
    have hz : Coinvariants.ker ρ=⊥ := by
      apply bot_unique
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,x⟩,rfl⟩
      have hx : x∈ρ.invariants := by rw [ht]; trivial
      change ρ a x-x∈(⊥ : Submodule S.field.Carrier (Coordinates.sl3 m).Space)
      rw [hx a,sub_self]
      exact Submodule.zero_mem _
    exact f.space_ne_bot 1 (hd.symm.trans hz)
  have hf : f.space 1=ρ.invariants := by
    apply Submodule.eq_of_le_of_finrank_eq hP
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hn)
    have hlo := Submodule.finrank_mono hP
    rw [f.dimension] at hlo ⊢
    have ht : Module.finrank S.field.Carrier
        (⊤ : Submodule S.field.Carrier (Coordinates.sl3 m).Space)=3 := by
      rw [finrank_top]
      change Module.finrank S.field.Carrier (Fin 3 → S.field.Carrier)=3
      simp
    rw [ht] at hlt
    omega
  apply le_antisymm
  · intro v hv
    apply (c.mem_preimage _ ⟨v,hv.1⟩).mpr
    change (c.projection ⟨v,hv.1⟩).toAdd∈f.space 1
    rw [hf]
    intro a
    rw [sl3PlaneAction_projection]
    congr 2
    apply Subtype.ext
    change (a:G)*v*(a:G)⁻¹=v
    rw [mem_centralizer_iff.mp hv.2 a.val a.property,mul_inv_cancel_right]
  · exact le_inf (D.centralQuotientPreimage_le _) hfix


omit m in
/-- The fixed-plane calculation on either surviving natural row, on the
literal original preimages and with the entire relative centralizer retained. -/
theorem fixed_plane_of_quotient_plane {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    {A : Subgroup G} (hA : A ≤ normalizer (V:Set G)) (hsq : ∀a:A,a^2=1)
    (hfix : f.Vi 1 ≤ centralizer (A:Set G))
    (hmove : ⁅V,A⁆ ⊔ (V ⊓ centralizer (L:Set G))=f.Vi 1) :
    V ⊓ centralizer (A:Set G)=f.Vi 1 := by
  cases c with
  | sl3 m => exact fixed_plane_of_sl3_quotient_plane m f hA hfix hmove
  | sp4 m => exact fixed_plane_of_sp4_quotient_plane m f hA hsq hfix hmove
  | g2 m => exact (hG2 ⟨m⟩).elim

omit m in
/-- The third and fourth parabolic calculations now follow from the first
two and the preceding flag-radical centralization theorem. The two remaining
calculations are local obligations of the nonnormalization owner. -/
theorem parabolic_of_two_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1:Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) (hsmall : NoSmallActions f)
    (houtside : ¬V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1))
    (hproper : V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L:Set G)) ≠ f.Vi 1 →
      ∃l∈f.Li 1, SmallSymmetricAction f
        ((V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom) V) :
    ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) := by
  apply parabolic_of_three_calculations f hG2 g hg hne hsmall houtside hproper
  intro hR hmove
  apply fixed_plane_of_quotient_plane f hG2 (hg.trans S.sylow_normalizes) ?_
    (le_centralizer_iff.mpr (hR.trans hradical)) hmove
  intro a
  obtain ⟨v,hv,he⟩ := a.property
  let := D.elementary
  apply Subtype.ext
  change (a:G)^2=1
  rw [←he,←map_pow,elemPow_eq_one_of_isElementaryAbelian v hv,map_one]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
