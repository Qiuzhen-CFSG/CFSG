module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Natural

/-!
# The actual natural frame and pairing seed for MS93 (4.4.1)

The supplied section of W/Z_c and the actual subgroup U_c can be placed over
one quotient marking without choosing an orientation. The inner relative
marking defines the favorable orientation; its negation constructs literal
contragredient coordinates. The fixed-core quotient has the required marked
extension, and the actual image of Z_c inherits the coordinates of U_c.

PairingWitness specifies a genuine SourceData application and the seed
containments used by the proved quotient lift. Its existence and the exclusion
of the opposite orientation remain mathematical obligations. Neither is
asserted here, and neither conclusion of (4.4.1) is a witness field.

The natural-image descent adapts the earlier FirstPairing construction while
retaining W = localZSpan instead of the full radius group. No Counterexample
or trapped-radius hypothesis is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), pp.890--891,
with (1.7)(i), pp.847--848, and the c-notation on p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
open RankOnePairing Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Both actual natural factors, using the quotient marking supplied by
c(W/Z_c)=1. This contains no choice of orientation. -/
structure FrameAt (a c : Vertex R) where
  sectionData : Escape.NaturalSectionAt c (localZSpan R a c) (Z R c)
  naturalU : NaturalFactor sectionData.projection ⊤
    ((U R c).subgroupOf (stabilizer R c)) ⊥

namespace FrameAt
variable {a c : Vertex R} (f : FrameAt a c)

/-- The natural moving factor has the same orientation as U_c exactly when
the relative marking is inner. This refers to the actual two actions. -/
def SameOrientation : Prop :=
  f.naturalU.marking.symm.trans f.sectionData.module_section.natural.marking ∈
    MulAut.innerSubgroup SL

/-- The expanded section hypothesis supplies the actual ambient triple bound. -/
theorem triple_le_Z (f : FrameAt a c) :
    ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c := by
  have h := map_mono (f := (stabilizer R c).subtype)
    f.sectionData.module_section.triple_le
  simpa only [map_commutator,
    map_subgroupOf_eq_of_le f.sectionData.local_group,
    map_subgroupOf_eq_of_le (show Q R c ≤ stabilizer R c from fun _ hx => hx.1),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R c), Ltilde] using h

/-- In the other orientation the quotient has actual contragredient
coordinates, with its original radical denominator. -/
noncomputable def dualFactor (h : ¬ f.SameOrientation) :
    DualFactor f.sectionData.projection ⊤
      (Escape.movingPreimage ((Q R c).subgroupOf (stabilizer R c))
        ((localZSpan R a c).subgroupOf (stabilizer R c))
        ((Z R c).subgroupOf (stabilizer R c)))
      (Escape.radicalPreimage ((Q R c).subgroupOf (stabilizer R c))
        ((localZSpan R a c).subgroupOf (stabilizer R c))
        ((Z R c).subgroupOf (stabilizer R c)))
      ((U R c).subgroupOf (stabilizer R c)) f.naturalU :=
  Escape.PairingControl.FirstPairing.Orientation.dualFactorOfNotInner
    f.naturalU f.sectionData.module_section.natural h

end FrameAt

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- Align the given natural subgroup with the section's genuine marking.
No trapped radius or fixed-space orientation is needed. -/
theorem frame_nonempty (common : CommonFacts R source geometry)
    {a c : Vertex R} (hc : color R c = false) (hnat : HasNaturalSection R a c) :
    Nonempty (FrameAt a c) := by
  obtain ⟨s⟩ := hnat
  obtain ⟨n⟩ := Escape.PairingControl.FirstPairing.Orientation.naturalU_nonempty
    (moduleFacts common) c hc s.projection
    s.module_section.projection_surjective s.module_section.projection_kernel
  exact ⟨⟨s, n⟩⟩

namespace FrameAt
variable {a c : Vertex R} (f : FrameAt a c)

/-- The marked projection on the actual quotient G_c/D_c. -/
abbrev projection : LocalQuotient c →* SL :=
  quotientProjection c f.sectionData.projection f.sectionData.module_section.projection_kernel

/-- The source extension (A) for any common marked flag. -/
noncomputable def extension (source : LocalSource L R) (hc : color R c = false)
    (flag : SL) (hflag : BinaryWeakBN flag) : Extension (M := LocalQuotient c) :=
  quotientExtension source c hc f.sectionData.projection
    f.sectionData.module_section.projection_surjective
    f.sectionData.module_section.projection_kernel flag hflag

@[simp] theorem extension_projection (source : LocalSource L R) (hc : color R c = false)
    (flag : SL) (hflag : BinaryWeakBN flag) :
    (f.extension source hc flag hflag).projection = f.projection := rfl

/-- The core in the pairing extension is exactly the image of Q_c. -/
theorem extension_core (source : LocalSource L R) (hc : color R c = false)
    (flag : SL) (hflag : BinaryWeakBN flag) :
    extensionCore (f.extension source hc flag hflag).projection = quotientImage c (Q R c) :=
  quotientExtension_core source c hc f.sectionData.projection
    f.sectionData.module_section.projection_surjective
    f.sectionData.module_section.projection_kernel flag hflag

/-- Both Section 1 local normalizers are the actual marked parabolic preimages. -/
theorem extension_parabolic (source : LocalSource L R) (hc : color R c = false)
    (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool) :
    localParabolic (f.extension source hc flag hflag) i = parabolic f.projection flag i :=
  quotientExtension_parabolic source c hc f.sectionData.projection
    f.sectionData.module_section.projection_surjective
    f.sectionData.module_section.projection_kernel flag hflag i

/-- Natural coordinates on the literal image of Z_c, retaining the same
projection and the marking of U_c. The fixed summand is killed by D_c. -/
noncomputable def naturalZ (common : CommonFacts R source geometry)
    (hc : color R c = false) :
    NaturalFactor f.projection ⊤ (quotientImage c (Z R c)) ⊥ := by
  let E := Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.naturalImageEquiv
    (moduleFacts common) c hc
  let coord := E.symm.trans f.naturalU.equivOfBot
  let hn := quotientImage_normal c (Z R c) (Z_normalized R c)
  refine {
    marking := f.naturalU.marking
    coordinates := coord.toMonoidHom
    surjective := coord.surjective
    kernel := ?_
    normalized := le_normalizer_of_normal
    action := ?_ }
  · rw [bot_subgroupOf]
    exact coord.toMonoidHom.ker_eq_bot_iff.mpr coord.injective
  · intro l _ x y hy
    obtain ⟨l₀, rfl⟩ := QuotientGroup.mk'_surjective (denominator c) l
    let u := E.symm x
    let v := E.symm y
    have hu : (l₀ : stabilizer R c) * (u : stabilizer R c) * l₀⁻¹ ∈
        (U R c).subgroupOf (stabilizer R c) :=
      (mem_normalizer_iff.mp (f.naturalU.normalized (mem_top l₀)) _).mp u.property
    let z : (U R c).subgroupOf (stabilizer R c) := ⟨_, hu⟩
    have hz : E z = y := by
      apply Subtype.ext
      change quotientMap c (l₀ * (u : stabilizer R c) * l₀⁻¹) = (y : LocalQuotient c)
      rw [map_mul, map_mul, map_inv]
      have hx : quotientMap c (u : stabilizer R c) = (x : LocalQuotient c) :=
        congrArg Subtype.val (E.apply_symm_apply x)
      rw [hx]
      exact hy.symm
    have hv : (v : stabilizer R c) = l₀ * (u : stabilizer R c) * l₀⁻¹ := by
      have he : v = z := E.injective ((E.apply_symm_apply y).trans hz.symm)
      exact congrArg Subtype.val he
    exact f.naturalU.action l₀ (mem_top _) u v hv

@[simp] theorem naturalZ_marking (common : CommonFacts R source geometry)
    (hc : color R c = false) : (f.naturalZ common hc).marking = f.naturalU.marking := rfl

end FrameAt

/-- A source pairing seed still to be constructed in the favorable orientation.
The whole span is generated modulo C(Q_c); no commutator conclusion is a field.
The seed's origin bound is used to propagate centralization of Q_a ∩ Q_c. -/
structure PairingWitness (source : LocalSource L R) {a c : Vertex R}
    (hc : color R c = false) (f : FrameAt a c) where
  flag : SL
  weakBN : BinaryWeakBN flag
  side : Bool
  seed : Subgroup (LocalQuotient c)
  data : let := quotientImage_normal c (Z R c) (Z_normalized R c)
         let := quotientImage_normal c (Q R c) (Q_normalized R c)
         SourceData (f.extension source hc flag weakBN) side
           (quotientImage c (Z R c)) (quotientImage c (Q R c)) seed
  fixed : quotientImage c (Z R c) ⊓ centralizer
    (localResidual (localParabolic (f.extension source hc flag weakBN) side) :
      Set (LocalQuotient c)) ≠ ⊥
  seed_le : seed ≤ quotientImage c (localZSpan R a c)
  origin : seed ≤ quotientImage c (Z R a) ⊔
    centralizer (quotientImage c (Q R c) : Set (LocalQuotient c))
  generation : quotientImage c (localZSpan R a c) ≤ generated seed ⊔
    centralizer (quotientImage c (Q R c) : Set (LocalQuotient c))

/-- The quotient pairing, including propagation from the seed to the actual
local span, proves both clauses for every permitted x. Existence of the
witness is a separate mathematical obligation. -/
theorem PairingWitness.localControl {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    {f : FrameAt a c} (p : PairingWitness source hc f) : LocalControlAt R a c :=
  localControl_of_pairing ha hc hd hb (f.extension source hc p.flag p.weakBN)
    p.side p.seed p.data p.fixed p.seed_le p.origin p.generation

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
