module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree.Source
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting

/-!
# Centralizer generation on the original plane cover

Each original vector gives a displacement homomorphism into a fixed plane.
Its kernel centralizes that original vector, and the plane has at most q²
possible displacements. The corresponding centralizers therefore generate V
with actor corank at most 2n. In the symplectic row, the universal-cover
fixed-lifting theorem identifies the original point stabilizer through its
natural projection, retaining every nonsplit central vector. In the SL3 row,
the projection is injective and the original commutator lies in the plane.

The genuine invariant flag and the previously constructed full-cover actor
supply the required geometry. The final consumer proves the numerical clause
of ParabolicGeometry from its preceding three calculations. Those three local
calculations remain obligations of qt-d-1222-natural-conjugate-nonnormalization;
this module alone does not establish source 11.2.4.

Source: Aschbacher--Smith, 11.2.4, printed p.769, and I.2.3(1b), p.413.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped IsMulCommutative
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic

private theorem centralizerSpan_of_fixed_displacements
    {G F X : Type*} [Group G] [Finite G] [Field F] [Finite F]
    [AddCommGroup X] [Module F X] [Finite X]
    (V A : Subgroup G) (p : V →* Multiplicative X)
    (ρ : Representation F A X) (P : Submodule F X)
    (n : ℕ) (hcard : Nat.card P ≤ 2^n)
    (hmove : ∀ a : A, ∀ x : X, ρ a x-x ∈ P)
    (hfix : ∀ a : A, ∀ x ∈ P, ρ a x=x)
    (hlift : ∀ (a : A) (v : V), ρ a (p v).toAdd=(p v).toAdd →
      (a : G)*(v : G)=(v : G)*(a : G)) :
    CentralizerSpan V A n := by
  intro v hv
  let w : X := (p ⟨v,hv⟩).toAdd
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
  have hk : δ.ker ≤ (centralizer ({v} : Set G)).subgroupOf A := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply hlift a ⟨v,hv⟩
    apply sub_eq_zero.mp
    exact congrArg (fun x : Multiplicative P => x.toAdd.val) ha
  have hi : (centralizer ({v} : Set G)).relIndex A ≤ 2^n := by
    calc
      (centralizer ({v} : Set G)).relIndex A ≤ δ.ker.index := by
        have hh := relIndex_le_of_le_left (L := (⊤ : Subgroup A)) hk index_ne_zero_of_finite
        change ((centralizer ({v} : Set G)).subgroupOf A).index ≤ δ.ker.index
        simpa only [relIndex_top_right] using hh
      _ = Nat.card δ.range := index_ker δ
      _ ≤ Nat.card (Multiplicative P) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card P := Nat.card_congr Multiplicative.toAdd
      _ ≤ 2^n := hcard
  let B := A ⊓ centralizer ({v} : Set G)
  have hB : subgroupCorank A B ≤ n := by
    unfold subgroupCorank
    rw [inf_relIndex_left]
    have hh := Nat.log_mono_right (b := 2) hi
    simpa only [Nat.log_pow (by decide : 1<2)] using hh
  refine (show V ⊓ centralizer (B : Set G) ≤ _ from
    le_iSup_of_le B (le_iSup_of_le (show B ≤ A from inf_le_left)
      (le_iSup_of_le (f := fun (_ : subgroupCorank A B ≤ n) => V ⊓ centralizer (B : Set G)) hB le_rfl))) ?_
  refine ⟨hv,mem_centralizer_iff.mpr ?_⟩
  intro a ha
  exact mem_centralizer_singleton_iff.mp ha.2


variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

theorem sp4_projection_fixed_iff_commute (A : Subgroup G) (actor : A →* Sp S.field.Carrier)
    (action_eq : ∀ (a : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (actor a) v)) : G) =
        (a : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(a : G)⁻¹)
    (a : A) (v : V) :
    actor a • (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v).toAdd) =
      ((Coordinates.sp4 m).projection v).toAdd ↔ (a : G)*(v : G)=(v : G)*(a : G) := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Sp S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let a' : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    ⟨actor a,Group.IsPerfect.mem_commutator⟩
  let p := sp4CoverProjection D S m
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : D.spaceEquiv (Multiplicative.ofAdd w)=v := D.spaceEquiv.apply_symm_apply v
  have hpw : p w=((Coordinates.sp4 m).projection v).toAdd := rfl
  constructor
  · intro hf
    have hh := SymplecticFourOrthogonalCover.cover_fixed_of_projection_fixed p
      (sp4CoverProjection_isCover D S m) a' w (by
        change actor a • p w=p w
        rwa [hpw])
    have he := action_eq a w
    change Preliminary.markedAction D m (actor a) w=w at hh
    rw [hh,hw] at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  · intro hc
    have hh : Preliminary.markedAction D m (actor a) w=w := by
      apply Multiplicative.ofAdd.injective
      apply D.spaceEquiv.injective
      apply Subtype.ext
      rw [action_eq,hw,hc,mul_inv_cancel_right]
    have he := LinearMap.congr_fun (p.isIntertwining' a') w
    change p (Preliminary.markedAction D m (actor a) w)=actor a • p w at he
    rw [hh,hpw] at he
    exact he.symm

/-- Every original vector centralizes a subgroup of actor corank at most 2n.
The projection's central kernel is retained by the cover fixed-lifting theorem. -/
theorem centralizerSpan_of_sp4_plane_actor (A : Subgroup G)
    (actor : A →* Sp S.field.Carrier)
    (action_eq : ∀ (a : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (actor a) v)) : G) =
        (a : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(a : G)⁻¹)
    (P : Submodule S.field.Carrier (Vector S.field.Carrier))
    (hP : (form S.field.Carrier).orthogonal P=P)
    (hfix : ∀ (a : A) v, v∈P → actor a • v=v) :
    CentralizerSpan V A (2*S.field.degree) := by
  have hd : Module.finrank S.field.Carrier P=2 := by
    have hh := LinearMap.BilinForm.finrank_orthogonal (W := P) TwoLocalCover.form_nondegenerate
    rw [hP] at hh
    have hv : Module.finrank S.field.Carrier (Vector S.field.Carrier)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hv] at hh
    omega
  apply centralizerSpan_of_fixed_displacements (X := Vector S.field.Carrier) V A (Coordinates.sp4 m).projection
    ((symplecticNatural 2).comp actor) P (2*S.field.degree)
  · rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier),hd,S.field.card_eq,←pow_mul,
      Nat.mul_comm S.field.degree]
  · intro a v
    exact displacement_mem_of_self_orthogonal P hP (actor a) (hfix a) v
  · exact hfix
  · intro a v
    exact (sp4_projection_fixed_iff_commute m A actor action_eq a v).mp

open NormalizedPlane.TransvectionFree

/-- The genuine invariant plane is self-orthogonal in its original marking. -/
theorem flag_plane_self_orthogonal (f : InvariantFlag (Coordinates.sp4 m)) :
    (form S.field.Carrier).orthogonal (f.space 1)=f.space 1 := by
  letI : FiniteDimensional S.field.Carrier (Coordinates.sp4 m).Space :=
    inferInstanceAs (FiniteDimensional S.field.Carrier (Vector S.field.Carrier))
  have hle : f.space 1 ≤ (form S.field.Carrier).orthogonal (f.space 1) := by
    intro v hv w hw
    rw [flag_space_eq m f 1] at hv hw
    change v ∈ (plane S.field.Carrier).map (symplecticNatural 2 (Sp4.alignment m)) at hv
    change w ∈ (plane S.field.Carrier).map (symplecticNatural 2 (Sp4.alignment m)) at hw
    obtain ⟨v',hv',rfl⟩ := hv
    obtain ⟨w',hw',rfl⟩ := hw
    change form S.field.Carrier (Sp4.alignment m • w') (Sp4.alignment m • v')=0
    rw [preserves_form]
    exact plane_isotropic _ _ hw' hv'
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,f.dimension]
  change 2=Module.finrank S.field.Carrier (Vector S.field.Carrier)-2
  simp [Theory.SpecificGroups.SymplecticFour.Vector]

/-- The original plane centralizer supplies the concrete actor; no action map
or split-cover hypothesis is left to the source consumer. -/
theorem centralizerSpan_of_sp4_plane_fixed (f : InvariantFlag (Coordinates.sp4 m))
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (hsq : ∀ a : A, a^2=1) (hfix : f.Vi 1 ≤ centralizer (A : Set G)) :
    CentralizerSpan V A (2*S.field.degree) := by
  let actor := planeHom m f hA hsq hfix
  have hact := planeHom_action m f hA hsq hfix
  apply centralizerSpan_of_sp4_plane_actor m A actor hact (f.space 1)
    (flag_plane_self_orthogonal m f)
  intro a x hx
  let c := Coordinates.sp4 m
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
  have hp : (v:G)∈f.Vi 1 := (c.mem_preimage _ v).mpr (by
    change (c.projection v).toAdd∈f.space 1
    rwa [hv])
  have hh := (sp4_projection_fixed_iff_commute m A actor hact a v).mpr (hfix hp a.val a.property)
  have hv' : (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v).toAdd)=x :=
    congrArg Multiplicative.toAdd hv
  exact (congrArg (actor a • ·) hv'.symm).trans (hh.trans hv')


omit m in
/-- In the SL3 row the actual plane has q² elements, so its fixed displacements
bound the original point centralizers without any extra scalar-action hypothesis. -/
theorem centralizerSpan_of_sl3_plane_fixed
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (hmove : ⁅V,A⁆ ≤ f.Vi 1) (hfix : f.Vi 1 ≤ centralizer (A : Set G)) :
    CentralizerSpan V A (2*S.field.degree) := by
  letI : FiniteDimensional S.field.Carrier (Coordinates.sl3 m).Space :=
    inferInstanceAs (FiniteDimensional S.field.Carrier (Fin 3 → S.field.Carrier))
  let c := Coordinates.sl3 m
  let hL : A ≤ normalizer (L : Set G) := hA.trans (seed_normalizer_le D S)
  let ρ : Representation (ZMod 2) A (Fin 3 → S.field.Carrier) := c.conjugationAction hL hA
  apply centralizerSpan_of_fixed_displacements (X := Fin 3 → S.field.Carrier) V A c.projection ρ
    ((f.space 1).restrictScalars (ZMod 2)) (2*S.field.degree)
  · change Nat.card (f.space 1) ≤ _
    rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier),f.dimension,S.field.card_eq,←pow_mul]
    exact le_of_eq (congrArg (2^·) (Nat.mul_comm _ _))
  · intro a x
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    let w : V := V.normalizerMonoidHom (inclusion hA a) v*v⁻¹
    have hw : (w:G)∈⁅V,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator a.property v.property
    have hp := (c.mem_preimage (f.space 1) w).mp (hmove hw)
    change (c.projection w).toAdd∈f.space 1 at hp
    have he : (c.projection w).toAdd=ρ a x-x := by
      change (c.projection (V.normalizerMonoidHom (inclusion hA a) v*v⁻¹)).toAdd=_
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,
        ←c.conjugationAction_projection hL hA,hv]
      rfl
    change ρ a x-x∈f.space 1
    rwa [he] at hp
  · intro a x hx
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    have hp : (v:G)∈f.Vi 1 := (c.mem_preimage _ v).mpr (by
      change (c.projection v).toAdd∈f.space 1
      rwa [hv])
    have he : V.normalizerMonoidHom (inclusion hA a) v=v := by
      apply Subtype.ext
      change (a:G)*(v:G)*(a:G)⁻¹=(v:G)
      rw [hfix hp a.val a.property,mul_inv_cancel_right]
    have hh := c.conjugationAction_projection hL hA a v
    rw [he,hv] at hh
    exact hh
  · intro a v hv
    have he : V.normalizerMonoidHom (inclusion hA a) v=v := by
      have hinj : Function.Injective c.projection := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        apply bot_unique
        intro u hu
        apply mem_bot.mpr
        apply Subtype.ext
        apply mem_bot.mp
        rw [←Preliminary.sl3_centralizer_eq_bot D S m]
        exact ⟨u.property,(c.projection_eq_one_iff u).mp hu⟩
      apply hinj
      apply Multiplicative.toAdd.injective
      exact (c.conjugationAction_projection hL hA a v).symm.trans hv
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

omit m in
/-- The numerical centralizer generation in both surviving natural rows,
using the literal original commutator and fixed plane. -/
theorem centralizerSpan_of_plane_fixed {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    {A : Subgroup G} (hA : A ≤ normalizer (V : Set G)) (hsq : ∀a : A,a^2=1)
    (hmove : ⁅V,A⁆ ≤ f.Vi 1) (hfix : f.Vi 1 ≤ centralizer (A : Set G)) :
    CentralizerSpan V A (2*S.field.degree) := by
  cases c with
  | sl3 m => exact centralizerSpan_of_sl3_plane_fixed m f hA hmove hfix
  | sp4 m => exact centralizerSpan_of_sp4_plane_fixed m f hA hsq hfix
  | g2 m => exact (hG2 ⟨m⟩).elim

omit m in
/-- The actual parabolic consumer now needs only its first three calculations;
centralizer generation, including the nonsplit symplectic kernel, is proved here. -/
theorem parabolic_of_three_calculations {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) (hsmall : NoSmallActions f)
    (houtside : ¬V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1))
    (hproper : V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L:Set G)) ≠ f.Vi 1 →
      ∃l∈f.Li 1, SmallSymmetricAction f
        ((V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom) V)
    (hfixed : V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔ (V ⊓ centralizer (L:Set G)) = f.Vi 1 →
      V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) = f.Vi 1) :
    ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) := by
  have hR : V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 := by
    by_contra hn
    exact hsmall g hg hne (f.Vi 1) (houtside hn)
  have hplane : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ⊔
      (V ⊓ centralizer (L:Set G))=f.Vi 1 := by
    by_contra hn
    obtain ⟨l,hl,hs⟩ := hproper hR hn
    exact no_smallAction_after_replacement D S f hsmall g hR hne hl V hs
  have hfix := hfixed hR hplane
  refine ⟨hR,hplane,hfix,?_⟩
  apply centralizerSpan_of_plane_fixed f hG2 (hg.trans S.sylow_normalizes) ?_
    (le_sup_left.trans_eq hplane) (hfix.symm.le.trans inf_le_right)
  intro a
  obtain ⟨v,hv,he⟩ := a.property
  letI := D.elementary
  apply Subtype.ext
  change (a:G)^2=1
  rw [←he,←map_pow,elemPow_eq_one_of_isElementaryAbelian v hv,map_one]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
