module
public import Theory.SpecificGroups.Triality.ArmsFixedQuotient
public import Theory.SpecificGroups.Triality.ArmsParabolicAtTwo
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Intrinsic orbit separation in the binary triality arms core

The quotient of the actual arms core by its center has only one nonzero
Sylow-fixed vector. The Borel stabilizes it, so its parabolic orbit has at
most nine elements. Torus scalings and the positive short-root shear produce
fourteen distinct images of a nonzero highest short-root vector. These bounds
exclude every endpoint automorphism carrying that short-root vector to a
Sylow-fixed vector, including automorphisms induced by a cubic extension.

The proof uses symbolic root coordinates and the genuine Borel index. No
finite group enumeration or ambient recognition is assumed. The source
application is EightLargeParabolic/FusionSeparation.lean.
Source: Aschbacher--Smith F.4.35, printed p.292; GLS3 §§2.4,2.6.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Triality.Standard.EvenInvolutionGeometry.ArmsOrbit
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators
open ArmsNormalization
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "Q" => radical P Node.arms
local notation "L" => parabolic P Node.arms
theorem prime_two : (P).prime=2 := rfl
abbrev Space := Q ⧸ center Q

def coreAction : L →* MulAut Q :=
  (Q).normalizerMonoidHom.comp
    (inclusion ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .arms)).mp
      (radical_normal P .arms)))

def action : L →* MulAut Space := (quotientAut (center Q)).comp coreAction

theorem coreAction_val (h : L) (q : Q) : (coreAction h q).val=h.val*q.val*h.val⁻¹ := rfl

def point (q : Q) : Space := QuotientGroup.mk' (center Q) q

def points (q : Space) : Set Space := Set.range fun h : L => action h q

theorem action_point (h : L) (q : Q) :
    action h (point q)=point (coreAction h q) := quotientAut_apply_mk _ _ _

theorem point_eq_iff (q t : Q) : point q=point t ↔ q.val*t.val⁻¹∈highestRoot P := by
  change (q : Q ⧸ center Q)=(t : Q ⧸ center Q) ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  rw [div_eq_mul_inv]
  change q*t⁻¹∈center Q ↔ _
  rw [←embedded_center_radical_arms P prime_two]
  constructor
  · intro hh
    exact ⟨q*t⁻¹,hh,rfl⟩
  · rintro ⟨y,hy,he⟩
    exact (show y=q*t⁻¹ from Subtype.ext he) ▸ hy

/-- Fixedness in the literal quotient is the ambient commutator condition. -/
theorem action_point_fixed_iff (h : L) (q : Q) :
    action h (point q)=point q ↔ ⁅h.val,q.val⁆∈highestRoot P := by
  rw [action_point,point_eq_iff,coreAction_val]
  rfl

theorem point_eq_coordinates (v w : ArmsParameters P)
    (h : point (armsCoordinates P prime_two v)=point (armsCoordinates P prime_two w)) :
    v.1=w.1 ∧ v.2 0=w.2 0 ∧ v.2 1=w.2 1 :=
  coordinates_eq_of_central_difference P prime_two w v ((point_eq_iff _ _).mp h)

def fixedVector : Space := point (armsCoordinates P prime_two (![0,0],![0,1,0]))

private theorem long_two_mem (f : fixedField P) : long P prime_two 2 f∈Q := by
  rw [radical_eq_descendedRootSubgroup P prime_two .arms]
  exact long_mem P prime_two .arms 2 trivial f
private theorem long_one_mem (f : fixedField P) : long P prime_two 1 f∈Q := by
  rw [radical_eq_descendedRootSubgroup P prime_two .arms]
  exact long_mem P prime_two .arms 1 trivial f

private theorem long_two_point (f : fixedField P) : point ⟨long P prime_two 2 f,long_two_mem f⟩=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have hh : long P prime_two 2 f∈highestRoot P := by
    refine ⟨longElementary P prime_two 2 f,?_,rfl⟩
    change elementaryInclusion P (longElementary P prime_two 2 f)∈splitHighestRoot P
    rw [longElementary_val]
    exact ⟨Multiplicative.ofAdd f.val,rfl⟩
  rw [←embedded_center_radical_arms P prime_two] at hh
  obtain ⟨x,hx,he⟩ := hh
  exact (show x=⟨long P prime_two 2 f,long_two_mem f⟩ from Subtype.ext he) ▸ hx

/-- The actual Sylow-fixed quotient has only one possible nonzero vector. -/
theorem fixed_point_alternatives (q : Space)
    (hq : ∀ h : L, h.val∈unipotent P → action h q=q) : q=1 ∨ q=fixedVector := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
  have hfix (a : ExtensionField P) : ⁅short P prime_two 0 a,u.val⁆∈highestRoot P := by
    have hs : short P prime_two 0 a∈unipotent P :=
      descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P prime_two .central)
        (short_mem P prime_two .central 0 trivial a)
    have hh := hq ⟨_,(unipotent_le_borel P).trans (borel_le_parabolic P .arms) hs⟩ hs
    change action _ (point u)=point u at hh
    rw [action_point] at hh
    exact (point_eq_iff _ _).mp hh
  obtain ⟨e,f,huf⟩ := fixed_mod_center_long_support P prime_two u hfix
  have hu : u=⟨long P prime_two 1 e,long_one_mem e⟩*⟨long P prime_two 2 f,long_two_mem f⟩ := Subtype.ext huf
  have he : e=0 ∨ e=1 := by
    have hs : e.val^2=e.val := e.property
    rcases eq_zero_or_one_of_sq_eq_self hs with h|h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have huq : point u=point ⟨long P prime_two 1 e,long_one_mem e⟩ := by
    rw [hu]
    change QuotientGroup.mk' (center Q) (_*_) = _
    rw [map_mul]
    change point _ * point _ = _
    rw [long_two_point,mul_one]
  change point u=1 ∨ point u=fixedVector
  rw [huq]
  rcases he with rfl|rfl
  · left
    have hz : (⟨long P prime_two 1 0,long_one_mem 0⟩ : Q)=1 := Subtype.ext (long_zero P prime_two 1)
    rw [hz]
    exact map_one (QuotientGroup.mk' (center Q))
  · right
    apply congrArg point
    apply Subtype.ext
    rw [armsCoordinates_factorization]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one]

private theorem orbit_bound {A X : Type*} [Group A] [Finite A] [Group X]
    (f : A →* MulAut X) (B : Subgroup A) (q : X)
    (hidx : B.index≤9) (hfix : ∀ b∈B, f b q=q) :
    (Set.range fun a : A => f a q).ncard≤9 := by
  let : MulAction A X := MulAction.compHom X f
  have hb : B ≤ MulAction.stabilizer A q := hfix
  change Nat.card (MulAction.orbit A q)≤9
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A q)]
  exact (Subgroup.index_antitone hb).trans hidx

/-- The quotient orbit bound is intrinsic, so it is unaffected by endpoint automorphisms. -/
theorem fixed_point_orbit_bound (q : Space)
    (hq : ∀ h : L, h.val∈unipotent P → action h q=q) : (points q).ncard≤9 := by
  have hb : ∀ b : L, b.val∈borel P → action b q=q := by
    intro b hb
    by_cases hq1 : q=1
    · simp only [hq1,map_one]
    have hfixed : ∀ h : L, h.val∈unipotent P → action h (action b q)=action b q := by
      intro h hh
      have hnorm := (normal_subgroupOf_iff_le_normalizer (unipotent_le_borel P)).mp
        (ConcreteBruhat.unipotent_normal_in_borel P prime_two)
      have hm : b.val⁻¹*h.val*b.val∈unipotent P := by
        simpa only [inv_inv,Subgroup.subtype_apply] using
          (mem_normalizer_iff.mp (hnorm ((borel P).inv_mem hb)) h.val).mp hh
      have he := hq (b⁻¹*h*b) hm
      have he' := congrArg (action b) he
      change action h (action b q)=action b q
      calc
        _ = action b (action (b⁻¹*h*b) q) := by
          simp only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply]
          rw [MulEquiv.apply_symm_apply]
        _ = _ := he'
    have hne : action b q≠1 := fun he => hq1 ((action b).injective (he.trans (map_one _).symm))
    have hne' := (fixed_point_alternatives q hq).resolve_left hq1
    exact ((fixed_point_alternatives (action b q) hfixed).resolve_left hne).trans hne'.symm
  exact orbit_bound action ((borel P).subgroupOf L) q
    (OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic 1 Nat.zero_lt_one .arms).le hb

theorem short_two_mem (d : ExtensionField P) : short P prime_two 2 d∈Q := by
  rw [radical_eq_descendedRootSubgroup P prime_two .arms]
  exact short_mem P prime_two .arms 2 (by change (2 : Fin 3)≠0; decide) d

private theorem short_coordinates (d : ExtensionField P) :
    (armsCoordinates P prime_two (![0,d],![0,0,0])).val=short P prime_two 2 d := by
  rw [armsCoordinates_factorization]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one]

private theorem torus_short_two_general (R : Parameters) (hp : R.prime=2) (hq : R.q=2)
    (t : (ExtensionField R)ˣ) (d : ExtensionField R) :
    torusActor R hp .arms t * short R hp 2 d * (torusActor R hp .arms t)⁻¹ =
      short R hp 2 (t.val⁻¹*d) := by
  have hscale : t.val * fieldFrobenius R t.val /
      fieldFrobenius R (fieldFrobenius R t.val)=t.val⁻¹ := by
    simp only [fieldFrobenius_apply,hq]
    field_simp
  have hh := (torus_arms_short_two_conjugate R hp t d).trans
    (congrArg (fun s : ExtensionField R => shortSplit R 2 (s*d)) hscale)
  have he : torusElementary R hp .arms t * shortElementary R hp 2 d *
      (torusElementary R hp .arms t)⁻¹ = shortElementary R hp 2 (t.val⁻¹*d) := by
    apply elementaryInclusion_injective R
    simpa only [map_mul,map_inv,shortElementary_val] using hh
  simpa only [torusActor,short,map_mul,map_inv] using congrArg (toCarrier R) he

private theorem torus_short_two (t : (ExtensionField P)ˣ) (d : ExtensionField P) :
    torusActor P prime_two .arms t * short P prime_two 2 d * (torusActor P prime_two .arms t)⁻¹ =
      short P prime_two 2 (t.val⁻¹*d) := torus_short_two_general P prime_two rfl t d

/-- The Borel already produces every nonzero short parameter and both next
long coordinates in the actual core quotient. -/
theorem short_coordinate_orbit (d₀ : ExtensionField P) (hd₀ : d₀≠0)
    (d : (ExtensionField P)ˣ) (e : fixedField P) :
    point (armsCoordinates P prime_two (![0,d.val],![0,e,0]))∈
      points (point ⟨short P prime_two 2 d₀,short_two_mem d₀⟩) := by
  let t : (ExtensionField P)ˣ := Units.mk0 (d₀/d.val) (div_ne_zero hd₀ d.ne_zero)
  have ht : t.val⁻¹*d₀=d.val := by
    dsimp [t]
    field_simp
  obtain ⟨a,ha⟩ := armsPairing_surjective_left P prime_two d.val d.ne_zero e
  have hs : short P prime_two 0 a∈L :=
    (unipotent_le_borel P).trans (borel_le_parabolic P .arms)
      (descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P prime_two .central)
        (short_mem P prime_two .central 0 trivial a))
  have htor : torusActor P prime_two .arms t∈L :=
    levi_le_parabolic P .arms (torusActor_mem_levi P prime_two .arms t)
  refine ⟨⟨short P prime_two 0 a*torusActor P prime_two .arms t,(L).mul_mem hs htor⟩,?_⟩
  change action _ (point _)=point _
  rw [action_point]
  apply congrArg point
  apply Subtype.ext
  change (short P prime_two 0 a*torusActor P prime_two .arms t)*short P prime_two 2 d₀*
    (short P prime_two 0 a*torusActor P prime_two .arms t)⁻¹ = _
  rw [show (short P prime_two 0 a*torusActor P prime_two .arms t)*short P prime_two 2 d₀*
      (short P prime_two 0 a*torusActor P prime_two .arms t)⁻¹ =
      short P prime_two 0 a*(torusActor P prime_two .arms t*short P prime_two 2 d₀*
      (torusActor P prime_two .arms t)⁻¹)*(short P prime_two 0 a)⁻¹ by group,
    torus_short_two,ht,←short_coordinates,short_shear]
  congr 2
  simp [shearParameters,higherCoefficient,ha]

/-- The short-root orbit in Q/Z has at least fourteen elements. Only the
seven nonzero field parameters and the two long coordinates are counted. -/
theorem short_orbit_lower (d : ExtensionField P) (hd : d≠0) :
    14≤(points (point ⟨short P prime_two 2 d,short_two_mem d⟩)).ncard := by
  let f : ((ExtensionField P)ˣ × fixedField P) →
      points (point ⟨short P prime_two 2 d,short_two_mem d⟩) := fun x =>
    ⟨point (armsCoordinates P prime_two (![0,x.1.val],![0,x.2,0])),
      short_coordinate_orbit d hd x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh := point_eq_coordinates _ _ (congrArg Subtype.val he)
    apply Prod.ext
    · exact Units.ext (congrFun hh.1 1)
    · exact hh.2.2
  have hc := Nat.card_le_card_of_injective f hf
  have hsize : Nat.card ((ExtensionField P)ˣ × fixedField P)=14 := by
    rw [Nat.card_prod,Nat.card_units,card_extensionField,card_fixedField]
    rfl
  exact hsize ▸ hc

/-- A short-root quotient cannot be moved to a Sylow-fixed quotient by an
endpoint automorphism compatible with an automorphism of the actual core. -/
theorem short_not_fixed_of_compatible
    (d : ExtensionField P) (hd : d≠0) (a : MulAut L) (b : MulAut Space)
    (hab : ∀ h : L, ∀ q : Space, b (action h q)=action (a h) (b q)) :
    ¬ (∀ h : L, h.val∈unipotent P →
      action h (b (point ⟨short P prime_two 2 d,short_two_mem d⟩))=
        b (point ⟨short P prime_two 2 d,short_two_mem d⟩)) := by
  intro hfix
  have horbit (q : Space) : b '' points q=points (b q) := by
    ext x
    constructor
    · rintro ⟨_,⟨h,rfl⟩,rfl⟩
      exact ⟨a h,(hab h q).symm⟩
    · rintro ⟨h,rfl⟩
      refine ⟨action (a.symm h) q,⟨_,rfl⟩,?_⟩
      rw [hab,a.apply_symm_apply]
  have he (q : Space) : (points (b q)).ncard=(points q).ncard := by
    rw [←horbit,Set.ncard_image_of_injective _ b.injective]
  have hu := fixed_point_orbit_bound _ hfix
  rw [he] at hu
  have hl := short_orbit_lower d hd
  omega

/-- Core automorphisms induce the compatible quotient actions used by the
original ambient normalizer. -/
theorem short_not_fixed_of_core_compatible
    (d : ExtensionField P) (hd : d≠0) (a : MulAut L) (c : MulAut Q)
    (hac : ∀ h : L, ∀ q : Q, c (coreAction h q)=coreAction (a h) (c q)) :
    ¬ (∀ h : L, h.val∈unipotent P →
      action h (point (c ⟨short P prime_two 2 d,short_two_mem d⟩))=
        point (c ⟨short P prime_two 2 d,short_two_mem d⟩)) := by
  let b := quotientAut (center Q) c
  have he (q : Q) : b (point q)=point (c q) := quotientAut_apply_mk _ _ _
  have hab (h : L) (q : Space) : b (action h q)=action (a h) (b q) := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
    change b (action h (point u))=action (a h) (b (point u))
    rw [action_point,he,he,action_point,hac]
  simpa only [he] using short_not_fixed_of_compatible d hd a b hab

end Triality.Standard.EvenInvolutionGeometry.ArmsOrbit

