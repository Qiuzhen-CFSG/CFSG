module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.CentralTarget
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path

/-!
# Vanishing of the proposed natural-to-dual commutator pairing

Transport a bilinear equivariant pairing on the literal relative quotients
through their supplied section maps. The target coordinates are constructed
in `CentralTarget`, using the original marking and projection. The matrix
calculation then forces the pairing to vanish. `moving_pairing_zero` applies
this to exactly the layers of (iii) and the requested natural reading of (iv).

The kernel quotients used here equal the stated relative quotients by the
`kernel` fields of the section witnesses. No quotient-model witness or
commutator descent is constructed or assumed to follow from its name.
In particular this is not a counterexample to the full source theorem.
It identifies a problem with using a nonzero pairing into the printed
target to recognize the requested natural orientation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii--iv), pp.898--899.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open Subgroup Stellmacher.PushingUp.AmalgamGraph DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}
  (common : CommonFacts R source geometry)

private theorem coordinate_pairing_zero
    (β : (W × W) → (W × W) → CentralQuotient R)
    (hadd₁ : ∀ v v' w, β (v + v') w = β v w * β v' w)
    (hadd₂ : ∀ v w w', β v (w + w') = β v w * β v w')
    (hact : ∀ (m : M) (v w : W × W),
      β ((common.natural.marking (source.projection m)).val.mulVec v.1,
          (common.natural.marking (source.projection m)).val.mulVec v.2)
        (dual (common.natural.marking (source.projection m)) w.1,
          dual (common.natural.marking (source.projection m)) w.2) =
        centralConjugate m (β v w)) : ∀ v w, β v w = 1 := by
  let E := centralQuotientCoordinates common
  have hz₁ (w) : β 0 w = 1 := by
    apply mul_left_cancel (a := β 0 w)
    simpa only [zero_add, mul_one] using (hadd₁ 0 0 w).symm
  have hz₂ (v) : β v 0 = 1 := by
    apply mul_left_cancel (a := β v 0)
    simpa only [zero_add, mul_one] using (hadd₂ v 0 0).symm
  let row (v : W × W) : (W × W) →+ W :=
    { toFun := fun w => (E (β v w)).toAdd
      map_zero' := by rw [hz₂, map_one]; rfl
      map_add' := by intro w w'; rw [hadd₂, map_mul]; rfl }
  let lin : (W × W) →+ ((W × W) →ₗ[ZMod 2] W) :=
    { toFun := fun v => (row v).toZModLinearMap 2
      map_zero' := by apply LinearMap.ext; intro w; apply funext; intro k; change (E (β 0 w)).toAdd k = 0; rw [hz₁,map_one]; rfl
      map_add' := by
        intro v v'
        apply LinearMap.ext
        intro w
        apply funext
        intro k
        change (E (β (v + v') w)).toAdd k =
          (E (β v w)).toAdd k + (E (β v' w)).toAdd k
        rw [hadd₁,map_mul]; rfl }
  have he (v w : W × W) : (lin.toZModLinearMap 2) v w = (E (β v w)).toAdd := rfl
  have hlin : lin.toZModLinearMap 2 = 0 := by
    apply Linear.naturalPair_dualPair_bilinear_zero
    intro g v w
    obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
    have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
    simp only [he]
    rw [← hmg, hact]
    exact centralQuotientCoordinates_action common m (β v w)
  intro v w
  apply E.injective
  apply Multiplicative.toAdd.injective
  rw [E.map_one]
  exact congrArg (fun f : (W × W) →ₗ[ZMod 2] (W × W) →ₗ[ZMod 2] W => f v w) hlin

/-- Any bilinear equivariant pairing from these literal quotients into the
printed target is zero. This is a restriction on a proposed pairing; no
commutator descent or natural-model existence is asserted. -/
theorem literal_quotient_pairing_zero {A N B D : Subgroup (FreeAmalgam R)}
    (n : MarkedPairSection source common A N false)
    (d : MarkedPairSection source common B D true)
    (β : (A ⧸ n.quotient.ker) → (B ⧸ d.quotient.ker) → CentralQuotient R)
    (hmul₁ : ∀ x x' y, β (x * x') y = β x y * β x' y)
    (hmul₂ : ∀ x y y', β x (y * y') = β x y * β x y')
    (hact : ∀ (m : M) (a a' : A) (b b' : B),
      (a' : FreeAmalgam R) = embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹ →
      (b' : FreeAmalgam R) = embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹ →
      β (QuotientGroup.mk a') (QuotientGroup.mk b') =
        centralConjugate m (β (QuotientGroup.mk a) (QuotientGroup.mk b))) :
    ∀ x y, β x y = 1 := by
  let en := QuotientGroup.quotientKerEquivOfSurjective n.quotient n.onto
  let ed := QuotientGroup.quotientKerEquivOfSurjective d.quotient d.onto
  let f (v w : W × W) := β (en.symm (Multiplicative.ofAdd v)) (ed.symm (Multiplicative.ofAdd w))
  have hf (a : A) (b : B) : f (n.quotient a).toAdd (d.quotient b).toAdd =
      β (QuotientGroup.mk a) (QuotientGroup.mk b) := by
    have hn : en (QuotientGroup.mk a) = n.quotient a := rfl
    have hd : ed (QuotientGroup.mk b) = d.quotient b := rfl
    change β (en.symm (n.quotient a)) (ed.symm (d.quotient b)) = _
    rw [← hn,← hd,en.symm_apply_apply,ed.symm_apply_apply]
  have hzero : ∀ v w, f v w = 1 := by
    apply coordinate_pairing_zero common f
    · intro v v' w
      change β (en.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd v')) _ = _
      rw [map_mul,hmul₁]
    · intro v w w'
      change β _ (ed.symm (Multiplicative.ofAdd w * Multiplicative.ofAdd w')) = _
      rw [map_mul,hmul₂]
    · intro m v w
      obtain ⟨a,ha⟩ := n.onto (Multiplicative.ofAdd v)
      obtain ⟨b,hb⟩ := d.onto (Multiplicative.ofAdd w)
      let a' : A := ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
        le_normalizer_iff.mp n.normalized _ ⟨m,rfl⟩ _ a.property⟩
      let b' : B := ⟨embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹,
        le_normalizer_iff.mp d.normalized _ ⟨m,rfl⟩ _ b.property⟩
      have hna := n.action m a a' rfl
      have hdb := d.action m b b' rfl
      simp only [Bool.false_eq_true, reduceIte, ha, hb, toAdd_ofAdd] at hna hdb
      rw [← hna, ← hdb, hf]
      have hv : v = (n.quotient a).toAdd := (congrArg Multiplicative.toAdd ha).symm
      have hw : w = (d.quotient b).toAdd := (congrArg Multiplicative.toAdd hb).symm
      rw [hv,hw,hf]
      exact hact m a a' b b' rfl rfl
  intro x y
  have h := hzero (en x).toAdd (ed y).toAdd
  simpa only [f, ofAdd_toAdd, MulEquiv.symm_apply_apply] using h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open Subgroup Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- Apply the obstruction to the literal source layers. The two kernel
quotients below are precisely the quotients by hat W and hat V, by the
`kernel` fields of `n` and `d`. Existence of `n` remains unproved. -/
theorem moving_pairing_zero (common : CommonFacts R source geometry)
    (p : Higher.SourcePath (alpha R))
    (n : MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false)
    (d : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (β : (_ ⧸ n.quotient.ker) → (_ ⧸ d.quotient.ker) → CentralQuotient R)
    (hmul₁ : ∀ x x' y, β (x * x') y = β x y * β x' y)
    (hmul₂ : ∀ x y y', β x (y * y') = β x y * β x y')
    (hact : ∀ (m : M)
      (a a' : ↥(⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)))
      (b b' : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)),
      (a' : FreeAmalgam R) = embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹ →
      (b' : FreeAmalgam R) = embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹ →
      β (QuotientGroup.mk a') (QuotientGroup.mk b') =
        centralConjugate m (β (QuotientGroup.mk a) (QuotientGroup.mk b))) :
    ∀ x y, β x y = 1 :=
  literal_quotient_pairing_zero common n d β hmul₁ hmul₂ hact

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
