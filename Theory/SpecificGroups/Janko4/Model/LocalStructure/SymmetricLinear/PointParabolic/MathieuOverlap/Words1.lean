module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Data
/-!
# Certified words for the max4 point-parabolic Mathieu intersection

These are literal words in the ATLAS max4 outputs, evaluated in the existing
28-dimensional restriction and the actual S₅ × SL₃(2) quotient. The faithful
combination detects equality in the native subgroup. Packed multiplication
identities are checked by the Lean kernel.

Source: ATLAS J4G1-max4W1 and J4G1-f2r112B0, with attribution in Model.Data
and SymmetricLinear.Model; Aschbacher–Smith 12.5.3–4, printed pp.818–819.
-/

public noncomputable section
namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup CharacteristicTwo SylowTwoPart SylowTwoPart.KernelCardinality
namespace MathieuOverlap
@[expose] def g000 : max4Subgroup := 1
lemma image_g000 : representation g000 = decode identityRows := by
  exact (map_one representation).trans decode_identity.symm
lemma quotient_g000 : max4Projection g000 = quot000 := by
  exact map_one max4Projection

@[expose] def g001 : max4Subgroup := CharacteristicTwo.first
lemma image_g001 : representation g001 = decode rows000 := by
  exact image_first
lemma quotient_g001 : max4Projection g001 = quot001 := by
  exact max4Projection_first

@[expose] def g002 : max4Subgroup := CharacteristicTwo.second
lemma image_g002 : representation g002 = decode rows001 := by
  exact image_second
lemma quotient_g002 : max4Projection g002 = quot002 := by
  exact max4Projection_second

@[expose] def g003 : max4Subgroup := g001⁻¹
set_option maxRecDepth 2000 in
lemma image_g003 : representation g003 = decode rows000 := by
  apply inverse_image g001 _ _ image_g001
  exact (product _ _ _ (by decide +kernel : ∀ i : Fin 28, Simplicity.Elevens.BridgeCertificate.fastRow (rows000.get i) rows000.toList = identityRows.get i)).trans decode_identity
lemma quotient_g003 : max4Projection g003 = quot001 := by
  rw [g003, map_inv, quotient_g001]
  decide +kernel

@[expose] def g004 : max4Subgroup := g002⁻¹
set_option maxRecDepth 2000 in
lemma image_g004 : representation g004 = decode rows002 := by
  apply inverse_image g002 _ _ image_g002
  exact (product _ _ _ (by decide +kernel : ∀ i : Fin 28, Simplicity.Elevens.BridgeCertificate.fastRow (rows001.get i) rows002.toList = identityRows.get i)).trans decode_identity
lemma quotient_g004 : max4Projection g004 = quot003 := by
  rw [g004, map_inv, quotient_g002]
  decide +kernel

@[expose] def g005 : max4Subgroup := (pivotWord 0 : max4Subgroup)
lemma image_g005 : representation g005 = decode rows003 := by
  exact image_pivotWord seedConjugate_coordinates 0
lemma quotient_g005 : max4Projection g005 = quot000 := by
  exact quotient_pivotWord 0

@[expose] def g006 : max4Subgroup := (pivotWord 1 : max4Subgroup)
lemma image_g006 : representation g006 = decode rows004 := by
  exact image_pivotWord seedConjugate_coordinates 1
lemma quotient_g006 : max4Projection g006 = quot000 := by
  exact quotient_pivotWord 1

@[expose] def g007 : max4Subgroup := (pivotWord 2 : max4Subgroup)
lemma image_g007 : representation g007 = decode rows005 := by
  exact image_pivotWord seedConjugate_coordinates 2
lemma quotient_g007 : max4Projection g007 = quot000 := by
  exact quotient_pivotWord 2

@[expose] def g008 : max4Subgroup := (pivotWord 3 : max4Subgroup)
lemma image_g008 : representation g008 = decode rows006 := by
  exact image_pivotWord seedConjugate_coordinates 3
lemma quotient_g008 : max4Projection g008 = quot000 := by
  exact quotient_pivotWord 3

@[expose] def g009 : max4Subgroup := (pivotWord 4 : max4Subgroup)
lemma image_g009 : representation g009 = decode rows007 := by
  exact image_pivotWord seedConjugate_coordinates 4
lemma quotient_g009 : max4Projection g009 = quot000 := by
  exact quotient_pivotWord 4

@[expose] def g010 : max4Subgroup := (pivotWord 5 : max4Subgroup)
lemma image_g010 : representation g010 = decode rows008 := by
  exact image_pivotWord seedConjugate_coordinates 5
lemma quotient_g010 : max4Projection g010 = quot000 := by
  exact quotient_pivotWord 5

@[expose] def g011 : max4Subgroup := (pivotWord 6 : max4Subgroup)
lemma image_g011 : representation g011 = decode rows009 := by
  exact image_pivotWord seedConjugate_coordinates 6
lemma quotient_g011 : max4Projection g011 = quot000 := by
  exact quotient_pivotWord 6

@[expose] def g012 : max4Subgroup := (pivotWord 7 : max4Subgroup)
lemma image_g012 : representation g012 = decode rows010 := by
  exact image_pivotWord seedConjugate_coordinates 7
lemma quotient_g012 : max4Projection g012 = quot000 := by
  exact quotient_pivotWord 7

@[expose] def g013 : max4Subgroup := (pivotWord 8 : max4Subgroup)
lemma image_g013 : representation g013 = decode rows011 := by
  exact image_pivotWord seedConjugate_coordinates 8
lemma quotient_g013 : max4Projection g013 = quot000 := by
  exact quotient_pivotWord 8

@[expose] def g014 : max4Subgroup := (pivotWord 9 : max4Subgroup)
lemma image_g014 : representation g014 = decode rows012 := by
  exact image_pivotWord seedConjugate_coordinates 9
lemma quotient_g014 : max4Projection g014 = quot000 := by
  exact quotient_pivotWord 9

@[expose] def g015 : max4Subgroup := (pivotWord 10 : max4Subgroup)
lemma image_g015 : representation g015 = decode rows013 := by
  exact image_pivotWord seedConjugate_coordinates 10
lemma quotient_g015 : max4Projection g015 = quot000 := by
  exact quotient_pivotWord 10

@[expose] def g016 : max4Subgroup := (pivotWord 11 : max4Subgroup)
lemma image_g016 : representation g016 = decode rows014 := by
  exact image_pivotWord seedConjugate_coordinates 11
lemma quotient_g016 : max4Projection g016 = quot000 := by
  exact quotient_pivotWord 11

@[expose] def g017 : max4Subgroup := (pivotWord 12 : max4Subgroup)
lemma image_g017 : representation g017 = decode rows015 := by
  exact image_pivotWord seedConjugate_coordinates 12
lemma quotient_g017 : max4Projection g017 = quot000 := by
  exact quotient_pivotWord 12

@[expose] def g018 : max4Subgroup := (pivotWord 13 : max4Subgroup)
lemma image_g018 : representation g018 = decode rows016 := by
  exact image_pivotWord seedConjugate_coordinates 13
lemma quotient_g018 : max4Projection g018 = quot000 := by
  exact quotient_pivotWord 13

@[expose] def g019 : max4Subgroup := (pivotWord 14 : max4Subgroup)
lemma image_g019 : representation g019 = decode rows017 := by
  exact image_pivotWord seedConjugate_coordinates 14
lemma quotient_g019 : max4Projection g019 = quot000 := by
  exact quotient_pivotWord 14

@[expose] def g020 : max4Subgroup := g002 * g001
set_option maxRecDepth 2000 in
lemma image_g020 : representation g020 = decode rows018 := by
  exact (map_mul representation g002 g001).trans
    ((congrArg₂ (· * ·) image_g002 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g020 : max4Projection g020 = quot004 := by
  have h : quot002 * quot001 = quot004 := by decide +kernel
  exact (map_mul max4Projection g002 g001).trans
    ((congrArg₂ (· * ·) quotient_g002 quotient_g001).trans h)

@[expose] def g021 : max4Subgroup := g020 * g002
set_option maxRecDepth 2000 in
lemma image_g021 : representation g021 = decode rows019 := by
  exact (map_mul representation g020 g002).trans
    ((congrArg₂ (· * ·) image_g020 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g021 : max4Projection g021 = quot005 := by
  have h : quot004 * quot002 = quot005 := by decide +kernel
  exact (map_mul max4Projection g020 g002).trans
    ((congrArg₂ (· * ·) quotient_g020 quotient_g002).trans h)

@[expose] def g022 : max4Subgroup := g021 * g001
set_option maxRecDepth 2000 in
lemma image_g022 : representation g022 = decode rows020 := by
  exact (map_mul representation g021 g001).trans
    ((congrArg₂ (· * ·) image_g021 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g022 : max4Projection g022 = quot006 := by
  have h : quot005 * quot001 = quot006 := by decide +kernel
  exact (map_mul max4Projection g021 g001).trans
    ((congrArg₂ (· * ·) quotient_g021 quotient_g001).trans h)

@[expose] def g023 : max4Subgroup := g022 * g002
set_option maxRecDepth 2000 in
lemma image_g023 : representation g023 = decode rows021 := by
  exact (map_mul representation g022 g002).trans
    ((congrArg₂ (· * ·) image_g022 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g023 : max4Projection g023 = quot007 := by
  have h : quot006 * quot002 = quot007 := by decide +kernel
  exact (map_mul max4Projection g022 g002).trans
    ((congrArg₂ (· * ·) quotient_g022 quotient_g002).trans h)

@[expose] def g024 : max4Subgroup := g023 * g001
set_option maxRecDepth 2000 in
lemma image_g024 : representation g024 = decode rows022 := by
  exact (map_mul representation g023 g001).trans
    ((congrArg₂ (· * ·) image_g023 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g024 : max4Projection g024 = quot008 := by
  have h : quot007 * quot001 = quot008 := by decide +kernel
  exact (map_mul max4Projection g023 g001).trans
    ((congrArg₂ (· * ·) quotient_g023 quotient_g001).trans h)

@[expose] def g025 : max4Subgroup := g024 * g002
set_option maxRecDepth 2000 in
lemma image_g025 : representation g025 = decode rows023 := by
  exact (map_mul representation g024 g002).trans
    ((congrArg₂ (· * ·) image_g024 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g025 : max4Projection g025 = quot009 := by
  have h : quot008 * quot002 = quot009 := by decide +kernel
  exact (map_mul max4Projection g024 g002).trans
    ((congrArg₂ (· * ·) quotient_g024 quotient_g002).trans h)

@[expose] def g026 : max4Subgroup := g025 * g002
set_option maxRecDepth 2000 in
lemma image_g026 : representation g026 = decode rows024 := by
  exact (map_mul representation g025 g002).trans
    ((congrArg₂ (· * ·) image_g025 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g026 : max4Projection g026 = quot010 := by
  have h : quot009 * quot002 = quot010 := by decide +kernel
  exact (map_mul max4Projection g025 g002).trans
    ((congrArg₂ (· * ·) quotient_g025 quotient_g002).trans h)

@[expose] def g027 : max4Subgroup := g026 * g001
set_option maxRecDepth 2000 in
lemma image_g027 : representation g027 = decode rows025 := by
  exact (map_mul representation g026 g001).trans
    ((congrArg₂ (· * ·) image_g026 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g027 : max4Projection g027 = quot011 := by
  have h : quot010 * quot001 = quot011 := by decide +kernel
  exact (map_mul max4Projection g026 g001).trans
    ((congrArg₂ (· * ·) quotient_g026 quotient_g001).trans h)

@[expose] def g028 : max4Subgroup := g027 * g002
set_option maxRecDepth 2000 in
lemma image_g028 : representation g028 = decode rows026 := by
  exact (map_mul representation g027 g002).trans
    ((congrArg₂ (· * ·) image_g027 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g028 : max4Projection g028 = quot012 := by
  have h : quot011 * quot002 = quot012 := by decide +kernel
  exact (map_mul max4Projection g027 g002).trans
    ((congrArg₂ (· * ·) quotient_g027 quotient_g002).trans h)

@[expose] def g029 : max4Subgroup := g028 * g002
set_option maxRecDepth 2000 in
lemma image_g029 : representation g029 = decode rows027 := by
  exact (map_mul representation g028 g002).trans
    ((congrArg₂ (· * ·) image_g028 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g029 : max4Projection g029 = quot013 := by
  have h : quot012 * quot002 = quot013 := by decide +kernel
  exact (map_mul max4Projection g028 g002).trans
    ((congrArg₂ (· * ·) quotient_g028 quotient_g002).trans h)

@[expose] def g030 : max4Subgroup := g029 * g001
set_option maxRecDepth 2000 in
lemma image_g030 : representation g030 = decode rows028 := by
  exact (map_mul representation g029 g001).trans
    ((congrArg₂ (· * ·) image_g029 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g030 : max4Projection g030 = quot014 := by
  have h : quot013 * quot001 = quot014 := by decide +kernel
  exact (map_mul max4Projection g029 g001).trans
    ((congrArg₂ (· * ·) quotient_g029 quotient_g001).trans h)

@[expose] def g031 : max4Subgroup := g030 * g004
set_option maxRecDepth 2000 in
lemma image_g031 : representation g031 = decode rows029 := by
  exact (map_mul representation g030 g004).trans
    ((congrArg₂ (· * ·) image_g030 image_g004).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g031 : max4Projection g031 = quot015 := by
  have h : quot014 * quot003 = quot015 := by decide +kernel
  exact (map_mul max4Projection g030 g004).trans
    ((congrArg₂ (· * ·) quotient_g030 quotient_g004).trans h)

@[expose] def g032 : max4Subgroup := g031 * g001
set_option maxRecDepth 2000 in
lemma image_g032 : representation g032 = decode rows030 := by
  exact (map_mul representation g031 g001).trans
    ((congrArg₂ (· * ·) image_g031 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g032 : max4Projection g032 = quot016 := by
  have h : quot015 * quot001 = quot016 := by decide +kernel
  exact (map_mul max4Projection g031 g001).trans
    ((congrArg₂ (· * ·) quotient_g031 quotient_g001).trans h)

@[expose] def g033 : max4Subgroup := g032 * g002
set_option maxRecDepth 2000 in
lemma image_g033 : representation g033 = decode rows031 := by
  exact (map_mul representation g032 g002).trans
    ((congrArg₂ (· * ·) image_g032 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g033 : max4Projection g033 = quot017 := by
  have h : quot016 * quot002 = quot017 := by decide +kernel
  exact (map_mul max4Projection g032 g002).trans
    ((congrArg₂ (· * ·) quotient_g032 quotient_g002).trans h)

@[expose] def g034 : max4Subgroup := g033 * g002
set_option maxRecDepth 2000 in
lemma image_g034 : representation g034 = decode rows032 := by
  exact (map_mul representation g033 g002).trans
    ((congrArg₂ (· * ·) image_g033 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g034 : max4Projection g034 = quot018 := by
  have h : quot017 * quot002 = quot018 := by decide +kernel
  exact (map_mul max4Projection g033 g002).trans
    ((congrArg₂ (· * ·) quotient_g033 quotient_g002).trans h)

@[expose] def g035 : max4Subgroup := g034 * g001
set_option maxRecDepth 2000 in
lemma image_g035 : representation g035 = decode rows033 := by
  exact (map_mul representation g034 g001).trans
    ((congrArg₂ (· * ·) image_g034 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g035 : max4Projection g035 = quot019 := by
  have h : quot018 * quot001 = quot019 := by decide +kernel
  exact (map_mul max4Projection g034 g001).trans
    ((congrArg₂ (· * ·) quotient_g034 quotient_g001).trans h)

@[expose] def g036 : max4Subgroup := g035 * g002
set_option maxRecDepth 2000 in
lemma image_g036 : representation g036 = decode rows034 := by
  exact (map_mul representation g035 g002).trans
    ((congrArg₂ (· * ·) image_g035 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g036 : max4Projection g036 = quot020 := by
  have h : quot019 * quot002 = quot020 := by decide +kernel
  exact (map_mul max4Projection g035 g002).trans
    ((congrArg₂ (· * ·) quotient_g035 quotient_g002).trans h)

@[expose] def g037 : max4Subgroup := g036 * g001
set_option maxRecDepth 2000 in
lemma image_g037 : representation g037 = decode rows035 := by
  exact (map_mul representation g036 g001).trans
    ((congrArg₂ (· * ·) image_g036 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g037 : max4Projection g037 = quot021 := by
  have h : quot020 * quot001 = quot021 := by decide +kernel
  exact (map_mul max4Projection g036 g001).trans
    ((congrArg₂ (· * ·) quotient_g036 quotient_g001).trans h)

@[expose] def g038 : max4Subgroup := g037 * g004
set_option maxRecDepth 2000 in
lemma image_g038 : representation g038 = decode rows036 := by
  exact (map_mul representation g037 g004).trans
    ((congrArg₂ (· * ·) image_g037 image_g004).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g038 : max4Projection g038 = quot022 := by
  have h : quot021 * quot003 = quot022 := by decide +kernel
  exact (map_mul max4Projection g037 g004).trans
    ((congrArg₂ (· * ·) quotient_g037 quotient_g004).trans h)

@[expose] def g039 : max4Subgroup := g038 * g005
set_option maxRecDepth 2000 in
lemma image_g039 : representation g039 = decode rows037 := by
  exact (map_mul representation g038 g005).trans
    ((congrArg₂ (· * ·) image_g038 image_g005).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g039 : max4Projection g039 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g038 g005).trans
    ((congrArg₂ (· * ·) quotient_g038 quotient_g005).trans h)

@[expose] def g040 : max4Subgroup := g039 * g009
set_option maxRecDepth 2000 in
lemma image_g040 : representation g040 = decode rows038 := by
  exact (map_mul representation g039 g009).trans
    ((congrArg₂ (· * ·) image_g039 image_g009).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g040 : max4Projection g040 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g039 g009).trans
    ((congrArg₂ (· * ·) quotient_g039 quotient_g009).trans h)

@[expose] def g041 : max4Subgroup := g040 * g010
set_option maxRecDepth 2000 in
lemma image_g041 : representation g041 = decode rows039 := by
  exact (map_mul representation g040 g010).trans
    ((congrArg₂ (· * ·) image_g040 image_g010).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g041 : max4Projection g041 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g040 g010).trans
    ((congrArg₂ (· * ·) quotient_g040 quotient_g010).trans h)

@[expose] def g042 : max4Subgroup := g041 * g011
set_option maxRecDepth 2000 in
lemma image_g042 : representation g042 = decode rows040 := by
  exact (map_mul representation g041 g011).trans
    ((congrArg₂ (· * ·) image_g041 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g042 : max4Projection g042 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g041 g011).trans
    ((congrArg₂ (· * ·) quotient_g041 quotient_g011).trans h)

@[expose] def g043 : max4Subgroup := g042 * g014
set_option maxRecDepth 2000 in
lemma image_g043 : representation g043 = decode rows041 := by
  exact (map_mul representation g042 g014).trans
    ((congrArg₂ (· * ·) image_g042 image_g014).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g043 : max4Projection g043 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g042 g014).trans
    ((congrArg₂ (· * ·) quotient_g042 quotient_g014).trans h)

@[expose] def g044 : max4Subgroup := g043 * g015
set_option maxRecDepth 2000 in
lemma image_g044 : representation g044 = decode rows042 := by
  exact (map_mul representation g043 g015).trans
    ((congrArg₂ (· * ·) image_g043 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g044 : max4Projection g044 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g043 g015).trans
    ((congrArg₂ (· * ·) quotient_g043 quotient_g015).trans h)

@[expose] def g045 : max4Subgroup := g044 * g017
set_option maxRecDepth 2000 in
lemma image_g045 : representation g045 = decode rows043 := by
  exact (map_mul representation g044 g017).trans
    ((congrArg₂ (· * ·) image_g044 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g045 : max4Projection g045 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g044 g017).trans
    ((congrArg₂ (· * ·) quotient_g044 quotient_g017).trans h)

@[expose] def g046 : max4Subgroup := g045 * g005
set_option maxRecDepth 2000 in
lemma image_g046 : representation g046 = decode rows044 := by
  exact (map_mul representation g045 g005).trans
    ((congrArg₂ (· * ·) image_g045 image_g005).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g046 : max4Projection g046 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g045 g005).trans
    ((congrArg₂ (· * ·) quotient_g045 quotient_g005).trans h)

@[expose] def g047 : max4Subgroup := g046 * g006
set_option maxRecDepth 2000 in
lemma image_g047 : representation g047 = decode rows045 := by
  exact (map_mul representation g046 g006).trans
    ((congrArg₂ (· * ·) image_g046 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g047 : max4Projection g047 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g046 g006).trans
    ((congrArg₂ (· * ·) quotient_g046 quotient_g006).trans h)

@[expose] def g048 : max4Subgroup := g047 * g007
set_option maxRecDepth 2000 in
lemma image_g048 : representation g048 = decode rows046 := by
  exact (map_mul representation g047 g007).trans
    ((congrArg₂ (· * ·) image_g047 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g048 : max4Projection g048 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g047 g007).trans
    ((congrArg₂ (· * ·) quotient_g047 quotient_g007).trans h)

@[expose] def g049 : max4Subgroup := g048 * g010
set_option maxRecDepth 2000 in
lemma image_g049 : representation g049 = decode rows047 := by
  exact (map_mul representation g048 g010).trans
    ((congrArg₂ (· * ·) image_g048 image_g010).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g049 : max4Projection g049 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g048 g010).trans
    ((congrArg₂ (· * ·) quotient_g048 quotient_g010).trans h)

@[expose] def g050 : max4Subgroup := g049 * g007
set_option maxRecDepth 2000 in
lemma image_g050 : representation g050 = decode rows048 := by
  exact (map_mul representation g049 g007).trans
    ((congrArg₂ (· * ·) image_g049 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g050 : max4Projection g050 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g049 g007).trans
    ((congrArg₂ (· * ·) quotient_g049 quotient_g007).trans h)

@[expose] def g051 : max4Subgroup := g050 * g008
set_option maxRecDepth 2000 in
lemma image_g051 : representation g051 = decode rows049 := by
  exact (map_mul representation g050 g008).trans
    ((congrArg₂ (· * ·) image_g050 image_g008).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g051 : max4Projection g051 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g050 g008).trans
    ((congrArg₂ (· * ·) quotient_g050 quotient_g008).trans h)

@[expose] def g052 : max4Subgroup := g051 * g011
set_option maxRecDepth 2000 in
lemma image_g052 : representation g052 = decode rows050 := by
  exact (map_mul representation g051 g011).trans
    ((congrArg₂ (· * ·) image_g051 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g052 : max4Projection g052 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g051 g011).trans
    ((congrArg₂ (· * ·) quotient_g051 quotient_g011).trans h)

@[expose] def g053 : max4Subgroup := g052 * g015
set_option maxRecDepth 2000 in
lemma image_g053 : representation g053 = decode rows051 := by
  exact (map_mul representation g052 g015).trans
    ((congrArg₂ (· * ·) image_g052 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g053 : max4Projection g053 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g052 g015).trans
    ((congrArg₂ (· * ·) quotient_g052 quotient_g015).trans h)

@[expose] def g054 : max4Subgroup := g053 * g019
set_option maxRecDepth 2000 in
lemma image_g054 : representation g054 = decode rows052 := by
  exact (map_mul representation g053 g019).trans
    ((congrArg₂ (· * ·) image_g053 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g054 : max4Projection g054 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g053 g019).trans
    ((congrArg₂ (· * ·) quotient_g053 quotient_g019).trans h)

@[expose] def g055 : max4Subgroup := g054 * g018
set_option maxRecDepth 2000 in
lemma image_g055 : representation g055 = decode rows053 := by
  exact (map_mul representation g054 g018).trans
    ((congrArg₂ (· * ·) image_g054 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g055 : max4Projection g055 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g054 g018).trans
    ((congrArg₂ (· * ·) quotient_g054 quotient_g018).trans h)

@[expose] def g056 : max4Subgroup := g055 * g017
set_option maxRecDepth 2000 in
lemma image_g056 : representation g056 = decode rows054 := by
  exact (map_mul representation g055 g017).trans
    ((congrArg₂ (· * ·) image_g055 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g056 : max4Projection g056 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g055 g017).trans
    ((congrArg₂ (· * ·) quotient_g055 quotient_g017).trans h)

@[expose] def g057 : max4Subgroup := g056 * g019
set_option maxRecDepth 2000 in
lemma image_g057 : representation g057 = decode rows055 := by
  exact (map_mul representation g056 g019).trans
    ((congrArg₂ (· * ·) image_g056 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g057 : max4Projection g057 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g056 g019).trans
    ((congrArg₂ (· * ·) quotient_g056 quotient_g019).trans h)

@[expose] def g058 : max4Subgroup := g057 * g015
set_option maxRecDepth 2000 in
lemma image_g058 : representation g058 = decode rows056 := by
  exact (map_mul representation g057 g015).trans
    ((congrArg₂ (· * ·) image_g057 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g058 : max4Projection g058 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g057 g015).trans
    ((congrArg₂ (· * ·) quotient_g057 quotient_g015).trans h)

@[expose] def g059 : max4Subgroup := g058 * g006
set_option maxRecDepth 2000 in
lemma image_g059 : representation g059 = decode rows057 := by
  exact (map_mul representation g058 g006).trans
    ((congrArg₂ (· * ·) image_g058 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g059 : max4Projection g059 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g058 g006).trans
    ((congrArg₂ (· * ·) quotient_g058 quotient_g006).trans h)

@[expose] def g060 : max4Subgroup := g059 * g009
set_option maxRecDepth 2000 in
lemma image_g060 : representation g060 = decode rows058 := by
  exact (map_mul representation g059 g009).trans
    ((congrArg₂ (· * ·) image_g059 image_g009).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g060 : max4Projection g060 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g059 g009).trans
    ((congrArg₂ (· * ·) quotient_g059 quotient_g009).trans h)

@[expose] def g061 : max4Subgroup := g060 * g011
set_option maxRecDepth 2000 in
lemma image_g061 : representation g061 = decode rows059 := by
  exact (map_mul representation g060 g011).trans
    ((congrArg₂ (· * ·) image_g060 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g061 : max4Projection g061 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g060 g011).trans
    ((congrArg₂ (· * ·) quotient_g060 quotient_g011).trans h)

@[expose] def g062 : max4Subgroup := g061 * g012
set_option maxRecDepth 2000 in
lemma image_g062 : representation g062 = decode rows060 := by
  exact (map_mul representation g061 g012).trans
    ((congrArg₂ (· * ·) image_g061 image_g012).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g062 : max4Projection g062 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g061 g012).trans
    ((congrArg₂ (· * ·) quotient_g061 quotient_g012).trans h)

@[expose] def g063 : max4Subgroup := g062 * g005
set_option maxRecDepth 2000 in
lemma image_g063 : representation g063 = decode rows061 := by
  exact (map_mul representation g062 g005).trans
    ((congrArg₂ (· * ·) image_g062 image_g005).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g063 : max4Projection g063 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g062 g005).trans
    ((congrArg₂ (· * ·) quotient_g062 quotient_g005).trans h)

@[expose] def g064 : max4Subgroup := g063 * g006
set_option maxRecDepth 2000 in
lemma image_g064 : representation g064 = decode rows062 := by
  exact (map_mul representation g063 g006).trans
    ((congrArg₂ (· * ·) image_g063 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g064 : max4Projection g064 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g063 g006).trans
    ((congrArg₂ (· * ·) quotient_g063 quotient_g006).trans h)

@[expose] def g065 : max4Subgroup := g064 * g007
set_option maxRecDepth 2000 in
lemma image_g065 : representation g065 = decode rows063 := by
  exact (map_mul representation g064 g007).trans
    ((congrArg₂ (· * ·) image_g064 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g065 : max4Projection g065 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g064 g007).trans
    ((congrArg₂ (· * ·) quotient_g064 quotient_g007).trans h)

@[expose] def g066 : max4Subgroup := g065 * g010
set_option maxRecDepth 2000 in
lemma image_g066 : representation g066 = decode rows064 := by
  exact (map_mul representation g065 g010).trans
    ((congrArg₂ (· * ·) image_g065 image_g010).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g066 : max4Projection g066 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g065 g010).trans
    ((congrArg₂ (· * ·) quotient_g065 quotient_g010).trans h)

@[expose] def g067 : max4Subgroup := g066 * g007
set_option maxRecDepth 2000 in
lemma image_g067 : representation g067 = decode rows065 := by
  exact (map_mul representation g066 g007).trans
    ((congrArg₂ (· * ·) image_g066 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g067 : max4Projection g067 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g066 g007).trans
    ((congrArg₂ (· * ·) quotient_g066 quotient_g007).trans h)

@[expose] def g068 : max4Subgroup := g067 * g008
set_option maxRecDepth 2000 in
lemma image_g068 : representation g068 = decode rows066 := by
  exact (map_mul representation g067 g008).trans
    ((congrArg₂ (· * ·) image_g067 image_g008).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g068 : max4Projection g068 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g067 g008).trans
    ((congrArg₂ (· * ·) quotient_g067 quotient_g008).trans h)

@[expose] def g069 : max4Subgroup := g068 * g011
set_option maxRecDepth 2000 in
lemma image_g069 : representation g069 = decode rows067 := by
  exact (map_mul representation g068 g011).trans
    ((congrArg₂ (· * ·) image_g068 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g069 : max4Projection g069 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g068 g011).trans
    ((congrArg₂ (· * ·) quotient_g068 quotient_g011).trans h)

@[expose] def g070 : max4Subgroup := g069 * g015
set_option maxRecDepth 2000 in
lemma image_g070 : representation g070 = decode rows068 := by
  exact (map_mul representation g069 g015).trans
    ((congrArg₂ (· * ·) image_g069 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g070 : max4Projection g070 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g069 g015).trans
    ((congrArg₂ (· * ·) quotient_g069 quotient_g015).trans h)

@[expose] def g071 : max4Subgroup := g070 * g019
set_option maxRecDepth 2000 in
lemma image_g071 : representation g071 = decode rows069 := by
  exact (map_mul representation g070 g019).trans
    ((congrArg₂ (· * ·) image_g070 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g071 : max4Projection g071 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g070 g019).trans
    ((congrArg₂ (· * ·) quotient_g070 quotient_g019).trans h)

@[expose] def g072 : max4Subgroup := g071 * g018
set_option maxRecDepth 2000 in
lemma image_g072 : representation g072 = decode rows070 := by
  exact (map_mul representation g071 g018).trans
    ((congrArg₂ (· * ·) image_g071 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g072 : max4Projection g072 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g071 g018).trans
    ((congrArg₂ (· * ·) quotient_g071 quotient_g018).trans h)

@[expose] def g073 : max4Subgroup := g072 * g017
set_option maxRecDepth 2000 in
lemma image_g073 : representation g073 = decode rows071 := by
  exact (map_mul representation g072 g017).trans
    ((congrArg₂ (· * ·) image_g072 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g073 : max4Projection g073 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g072 g017).trans
    ((congrArg₂ (· * ·) quotient_g072 quotient_g017).trans h)

@[expose] def g074 : max4Subgroup := g073 * g019
set_option maxRecDepth 2000 in
lemma image_g074 : representation g074 = decode rows072 := by
  exact (map_mul representation g073 g019).trans
    ((congrArg₂ (· * ·) image_g073 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g074 : max4Projection g074 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g073 g019).trans
    ((congrArg₂ (· * ·) quotient_g073 quotient_g019).trans h)

@[expose] def g075 : max4Subgroup := g074 * g015
set_option maxRecDepth 2000 in
lemma image_g075 : representation g075 = decode rows073 := by
  exact (map_mul representation g074 g015).trans
    ((congrArg₂ (· * ·) image_g074 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g075 : max4Projection g075 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g074 g015).trans
    ((congrArg₂ (· * ·) quotient_g074 quotient_g015).trans h)

@[expose] def g076 : max4Subgroup := g075 * g006
set_option maxRecDepth 2000 in
lemma image_g076 : representation g076 = decode rows074 := by
  exact (map_mul representation g075 g006).trans
    ((congrArg₂ (· * ·) image_g075 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g076 : max4Projection g076 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g075 g006).trans
    ((congrArg₂ (· * ·) quotient_g075 quotient_g006).trans h)

@[expose] def g077 : max4Subgroup := g076 * g016
set_option maxRecDepth 2000 in
lemma image_g077 : representation g077 = decode rows075 := by
  exact (map_mul representation g076 g016).trans
    ((congrArg₂ (· * ·) image_g076 image_g016).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g077 : max4Projection g077 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g076 g016).trans
    ((congrArg₂ (· * ·) quotient_g076 quotient_g016).trans h)

@[expose] def g078 : max4Subgroup := g077 * g015
set_option maxRecDepth 2000 in
lemma image_g078 : representation g078 = decode rows076 := by
  exact (map_mul representation g077 g015).trans
    ((congrArg₂ (· * ·) image_g077 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g078 : max4Projection g078 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g077 g015).trans
    ((congrArg₂ (· * ·) quotient_g077 quotient_g015).trans h)

@[expose] def g079 : max4Subgroup := g078 * g019
set_option maxRecDepth 2000 in
lemma image_g079 : representation g079 = decode rows077 := by
  exact (map_mul representation g078 g019).trans
    ((congrArg₂ (· * ·) image_g078 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g079 : max4Projection g079 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g078 g019).trans
    ((congrArg₂ (· * ·) quotient_g078 quotient_g019).trans h)

@[expose] def g080 : max4Subgroup := g079 * g018
set_option maxRecDepth 2000 in
lemma image_g080 : representation g080 = decode rows078 := by
  exact (map_mul representation g079 g018).trans
    ((congrArg₂ (· * ·) image_g079 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g080 : max4Projection g080 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g079 g018).trans
    ((congrArg₂ (· * ·) quotient_g079 quotient_g018).trans h)

@[expose] def g081 : max4Subgroup := g080 * g018
set_option maxRecDepth 2000 in
lemma image_g081 : representation g081 = decode rows077 := by
  exact (map_mul representation g080 g018).trans
    ((congrArg₂ (· * ·) image_g080 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g081 : max4Projection g081 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g080 g018).trans
    ((congrArg₂ (· * ·) quotient_g080 quotient_g018).trans h)

@[expose] def g082 : max4Subgroup := g081 * g017
set_option maxRecDepth 2000 in
lemma image_g082 : representation g082 = decode rows079 := by
  exact (map_mul representation g081 g017).trans
    ((congrArg₂ (· * ·) image_g081 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g082 : max4Projection g082 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g081 g017).trans
    ((congrArg₂ (· * ·) quotient_g081 quotient_g017).trans h)

@[expose] def g083 : max4Subgroup := g001 * g002
set_option maxRecDepth 2000 in
lemma image_g083 : representation g083 = decode rows080 := by
  exact (map_mul representation g001 g002).trans
    ((congrArg₂ (· * ·) image_g001 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g083 : max4Projection g083 = quot023 := by
  have h : quot001 * quot002 = quot023 := by decide +kernel
  exact (map_mul max4Projection g001 g002).trans
    ((congrArg₂ (· * ·) quotient_g001 quotient_g002).trans h)

@[expose] def g084 : max4Subgroup := g083 * g002
set_option maxRecDepth 2000 in
lemma image_g084 : representation g084 = decode rows081 := by
  exact (map_mul representation g083 g002).trans
    ((congrArg₂ (· * ·) image_g083 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g084 : max4Projection g084 = quot024 := by
  have h : quot023 * quot002 = quot024 := by decide +kernel
  exact (map_mul max4Projection g083 g002).trans
    ((congrArg₂ (· * ·) quotient_g083 quotient_g002).trans h)

@[expose] def g085 : max4Subgroup := g084 * g001
set_option maxRecDepth 2000 in
lemma image_g085 : representation g085 = decode rows082 := by
  exact (map_mul representation g084 g001).trans
    ((congrArg₂ (· * ·) image_g084 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g085 : max4Projection g085 = quot025 := by
  have h : quot024 * quot001 = quot025 := by decide +kernel
  exact (map_mul max4Projection g084 g001).trans
    ((congrArg₂ (· * ·) quotient_g084 quotient_g001).trans h)

@[expose] def g086 : max4Subgroup := g085 * g002
set_option maxRecDepth 2000 in
lemma image_g086 : representation g086 = decode rows083 := by
  exact (map_mul representation g085 g002).trans
    ((congrArg₂ (· * ·) image_g085 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g086 : max4Projection g086 = quot026 := by
  have h : quot025 * quot002 = quot026 := by decide +kernel
  exact (map_mul max4Projection g085 g002).trans
    ((congrArg₂ (· * ·) quotient_g085 quotient_g002).trans h)

@[expose] def g087 : max4Subgroup := g086 * g001
set_option maxRecDepth 2000 in
lemma image_g087 : representation g087 = decode rows084 := by
  exact (map_mul representation g086 g001).trans
    ((congrArg₂ (· * ·) image_g086 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g087 : max4Projection g087 = quot027 := by
  have h : quot026 * quot001 = quot027 := by decide +kernel
  exact (map_mul max4Projection g086 g001).trans
    ((congrArg₂ (· * ·) quotient_g086 quotient_g001).trans h)

@[expose] def g088 : max4Subgroup := g087 * g002
set_option maxRecDepth 2000 in
lemma image_g088 : representation g088 = decode rows085 := by
  exact (map_mul representation g087 g002).trans
    ((congrArg₂ (· * ·) image_g087 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g088 : max4Projection g088 = quot028 := by
  have h : quot027 * quot002 = quot028 := by decide +kernel
  exact (map_mul max4Projection g087 g002).trans
    ((congrArg₂ (· * ·) quotient_g087 quotient_g002).trans h)

@[expose] def g089 : max4Subgroup := g088 * g002
set_option maxRecDepth 2000 in
lemma image_g089 : representation g089 = decode rows086 := by
  exact (map_mul representation g088 g002).trans
    ((congrArg₂ (· * ·) image_g088 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g089 : max4Projection g089 = quot029 := by
  have h : quot028 * quot002 = quot029 := by decide +kernel
  exact (map_mul max4Projection g088 g002).trans
    ((congrArg₂ (· * ·) quotient_g088 quotient_g002).trans h)

@[expose] def g090 : max4Subgroup := g089 * g001
set_option maxRecDepth 2000 in
lemma image_g090 : representation g090 = decode rows087 := by
  exact (map_mul representation g089 g001).trans
    ((congrArg₂ (· * ·) image_g089 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g090 : max4Projection g090 = quot030 := by
  have h : quot029 * quot001 = quot030 := by decide +kernel
  exact (map_mul max4Projection g089 g001).trans
    ((congrArg₂ (· * ·) quotient_g089 quotient_g001).trans h)

@[expose] def g091 : max4Subgroup := g090 * g002
set_option maxRecDepth 2000 in
lemma image_g091 : representation g091 = decode rows088 := by
  exact (map_mul representation g090 g002).trans
    ((congrArg₂ (· * ·) image_g090 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g091 : max4Projection g091 = quot031 := by
  have h : quot030 * quot002 = quot031 := by decide +kernel
  exact (map_mul max4Projection g090 g002).trans
    ((congrArg₂ (· * ·) quotient_g090 quotient_g002).trans h)

@[expose] def g092 : max4Subgroup := g091 * g002
set_option maxRecDepth 2000 in
lemma image_g092 : representation g092 = decode rows089 := by
  exact (map_mul representation g091 g002).trans
    ((congrArg₂ (· * ·) image_g091 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g092 : max4Projection g092 = quot032 := by
  have h : quot031 * quot002 = quot032 := by decide +kernel
  exact (map_mul max4Projection g091 g002).trans
    ((congrArg₂ (· * ·) quotient_g091 quotient_g002).trans h)

@[expose] def g093 : max4Subgroup := g092 * g001
set_option maxRecDepth 2000 in
lemma image_g093 : representation g093 = decode rows090 := by
  exact (map_mul representation g092 g001).trans
    ((congrArg₂ (· * ·) image_g092 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g093 : max4Projection g093 = quot033 := by
  have h : quot032 * quot001 = quot033 := by decide +kernel
  exact (map_mul max4Projection g092 g001).trans
    ((congrArg₂ (· * ·) quotient_g092 quotient_g001).trans h)

@[expose] def g094 : max4Subgroup := g093 * g004
set_option maxRecDepth 2000 in
lemma image_g094 : representation g094 = decode rows091 := by
  exact (map_mul representation g093 g004).trans
    ((congrArg₂ (· * ·) image_g093 image_g004).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g094 : max4Projection g094 = quot034 := by
  have h : quot033 * quot003 = quot034 := by decide +kernel
  exact (map_mul max4Projection g093 g004).trans
    ((congrArg₂ (· * ·) quotient_g093 quotient_g004).trans h)

@[expose] def g095 : max4Subgroup := g094 * g001
set_option maxRecDepth 2000 in
lemma image_g095 : representation g095 = decode rows092 := by
  exact (map_mul representation g094 g001).trans
    ((congrArg₂ (· * ·) image_g094 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g095 : max4Projection g095 = quot035 := by
  have h : quot034 * quot001 = quot035 := by decide +kernel
  exact (map_mul max4Projection g094 g001).trans
    ((congrArg₂ (· * ·) quotient_g094 quotient_g001).trans h)

@[expose] def g096 : max4Subgroup := g095 * g002
set_option maxRecDepth 2000 in
lemma image_g096 : representation g096 = decode rows093 := by
  exact (map_mul representation g095 g002).trans
    ((congrArg₂ (· * ·) image_g095 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g096 : max4Projection g096 = quot036 := by
  have h : quot035 * quot002 = quot036 := by decide +kernel
  exact (map_mul max4Projection g095 g002).trans
    ((congrArg₂ (· * ·) quotient_g095 quotient_g002).trans h)

@[expose] def g097 : max4Subgroup := g096 * g002
set_option maxRecDepth 2000 in
lemma image_g097 : representation g097 = decode rows094 := by
  exact (map_mul representation g096 g002).trans
    ((congrArg₂ (· * ·) image_g096 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g097 : max4Projection g097 = quot037 := by
  have h : quot036 * quot002 = quot037 := by decide +kernel
  exact (map_mul max4Projection g096 g002).trans
    ((congrArg₂ (· * ·) quotient_g096 quotient_g002).trans h)

@[expose] def g098 : max4Subgroup := g097 * g005
set_option maxRecDepth 2000 in
lemma image_g098 : representation g098 = decode rows095 := by
  exact (map_mul representation g097 g005).trans
    ((congrArg₂ (· * ·) image_g097 image_g005).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g098 : max4Projection g098 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g097 g005).trans
    ((congrArg₂ (· * ·) quotient_g097 quotient_g005).trans h)

@[expose] def g099 : max4Subgroup := g098 * g006
set_option maxRecDepth 2000 in
lemma image_g099 : representation g099 = decode rows096 := by
  exact (map_mul representation g098 g006).trans
    ((congrArg₂ (· * ·) image_g098 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g099 : max4Projection g099 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g098 g006).trans
    ((congrArg₂ (· * ·) quotient_g098 quotient_g006).trans h)

@[expose] def g100 : max4Subgroup := g099 * g007
set_option maxRecDepth 2000 in
lemma image_g100 : representation g100 = decode rows097 := by
  exact (map_mul representation g099 g007).trans
    ((congrArg₂ (· * ·) image_g099 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g100 : max4Projection g100 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g099 g007).trans
    ((congrArg₂ (· * ·) quotient_g099 quotient_g007).trans h)

@[expose] def g101 : max4Subgroup := g100 * g008
set_option maxRecDepth 2000 in
lemma image_g101 : representation g101 = decode rows098 := by
  exact (map_mul representation g100 g008).trans
    ((congrArg₂ (· * ·) image_g100 image_g008).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g101 : max4Projection g101 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g100 g008).trans
    ((congrArg₂ (· * ·) quotient_g100 quotient_g008).trans h)

@[expose] def g102 : max4Subgroup := g101 * g012
set_option maxRecDepth 2000 in
lemma image_g102 : representation g102 = decode rows099 := by
  exact (map_mul representation g101 g012).trans
    ((congrArg₂ (· * ·) image_g101 image_g012).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g102 : max4Projection g102 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g101 g012).trans
    ((congrArg₂ (· * ·) quotient_g101 quotient_g012).trans h)

@[expose] def g103 : max4Subgroup := g102 * g013
set_option maxRecDepth 2000 in
lemma image_g103 : representation g103 = decode rows100 := by
  exact (map_mul representation g102 g013).trans
    ((congrArg₂ (· * ·) image_g102 image_g013).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g103 : max4Projection g103 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g102 g013).trans
    ((congrArg₂ (· * ·) quotient_g102 quotient_g013).trans h)

@[expose] def g104 : max4Subgroup := g103 * g014
set_option maxRecDepth 2000 in
lemma image_g104 : representation g104 = decode rows101 := by
  exact (map_mul representation g103 g014).trans
    ((congrArg₂ (· * ·) image_g103 image_g014).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g104 : max4Projection g104 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g103 g014).trans
    ((congrArg₂ (· * ·) quotient_g103 quotient_g014).trans h)

@[expose] def g105 : max4Subgroup := g104 * g016
set_option maxRecDepth 2000 in
lemma image_g105 : representation g105 = decode rows102 := by
  exact (map_mul representation g104 g016).trans
    ((congrArg₂ (· * ·) image_g104 image_g016).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g105 : max4Projection g105 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g104 g016).trans
    ((congrArg₂ (· * ·) quotient_g104 quotient_g016).trans h)

@[expose] def g106 : max4Subgroup := g105 * g018
set_option maxRecDepth 2000 in
lemma image_g106 : representation g106 = decode rows103 := by
  exact (map_mul representation g105 g018).trans
    ((congrArg₂ (· * ·) image_g105 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g106 : max4Projection g106 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g105 g018).trans
    ((congrArg₂ (· * ·) quotient_g105 quotient_g018).trans h)

@[expose] def g107 : max4Subgroup := g106 * g019
set_option maxRecDepth 2000 in
lemma image_g107 : representation g107 = decode rows104 := by
  exact (map_mul representation g106 g019).trans
    ((congrArg₂ (· * ·) image_g106 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g107 : max4Projection g107 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g106 g019).trans
    ((congrArg₂ (· * ·) quotient_g106 quotient_g019).trans h)

@[expose] def g108 : max4Subgroup := g107 * g015
set_option maxRecDepth 2000 in
lemma image_g108 : representation g108 = decode rows105 := by
  exact (map_mul representation g107 g015).trans
    ((congrArg₂ (· * ·) image_g107 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g108 : max4Projection g108 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g107 g015).trans
    ((congrArg₂ (· * ·) quotient_g107 quotient_g015).trans h)

@[expose] def g109 : max4Subgroup := g108 * g019
set_option maxRecDepth 2000 in
lemma image_g109 : representation g109 = decode rows106 := by
  exact (map_mul representation g108 g019).trans
    ((congrArg₂ (· * ·) image_g108 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g109 : max4Projection g109 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g108 g019).trans
    ((congrArg₂ (· * ·) quotient_g108 quotient_g019).trans h)

@[expose] def g110 : max4Subgroup := g109 * g018
set_option maxRecDepth 2000 in
lemma image_g110 : representation g110 = decode rows107 := by
  exact (map_mul representation g109 g018).trans
    ((congrArg₂ (· * ·) image_g109 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g110 : max4Projection g110 = quot037 := by
  have h : quot037 * quot000 = quot037 := by decide +kernel
  exact (map_mul max4Projection g109 g018).trans
    ((congrArg₂ (· * ·) quotient_g109 quotient_g018).trans h)

@[expose] def g111 : max4Subgroup := g005 * g006
set_option maxRecDepth 2000 in
lemma image_g111 : representation g111 = decode rows108 := by
  exact (map_mul representation g005 g006).trans
    ((congrArg₂ (· * ·) image_g005 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g111 : max4Projection g111 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g005 g006).trans
    ((congrArg₂ (· * ·) quotient_g005 quotient_g006).trans h)

@[expose] def g112 : max4Subgroup := g111 * g007
set_option maxRecDepth 2000 in
lemma image_g112 : representation g112 = decode rows109 := by
  exact (map_mul representation g111 g007).trans
    ((congrArg₂ (· * ·) image_g111 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g112 : max4Projection g112 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g111 g007).trans
    ((congrArg₂ (· * ·) quotient_g111 quotient_g007).trans h)

@[expose] def g113 : max4Subgroup := g112 * g010
set_option maxRecDepth 2000 in
lemma image_g113 : representation g113 = decode rows110 := by
  exact (map_mul representation g112 g010).trans
    ((congrArg₂ (· * ·) image_g112 image_g010).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g113 : max4Projection g113 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g112 g010).trans
    ((congrArg₂ (· * ·) quotient_g112 quotient_g010).trans h)

@[expose] def g114 : max4Subgroup := g113 * g007
set_option maxRecDepth 2000 in
lemma image_g114 : representation g114 = decode rows111 := by
  exact (map_mul representation g113 g007).trans
    ((congrArg₂ (· * ·) image_g113 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g114 : max4Projection g114 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g113 g007).trans
    ((congrArg₂ (· * ·) quotient_g113 quotient_g007).trans h)

@[expose] def g115 : max4Subgroup := g114 * g008
set_option maxRecDepth 2000 in
lemma image_g115 : representation g115 = decode rows112 := by
  exact (map_mul representation g114 g008).trans
    ((congrArg₂ (· * ·) image_g114 image_g008).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g115 : max4Projection g115 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g114 g008).trans
    ((congrArg₂ (· * ·) quotient_g114 quotient_g008).trans h)

@[expose] def g116 : max4Subgroup := g115 * g011
set_option maxRecDepth 2000 in
lemma image_g116 : representation g116 = decode rows113 := by
  exact (map_mul representation g115 g011).trans
    ((congrArg₂ (· * ·) image_g115 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g116 : max4Projection g116 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g115 g011).trans
    ((congrArg₂ (· * ·) quotient_g115 quotient_g011).trans h)

@[expose] def g117 : max4Subgroup := g116 * g015
set_option maxRecDepth 2000 in
lemma image_g117 : representation g117 = decode rows114 := by
  exact (map_mul representation g116 g015).trans
    ((congrArg₂ (· * ·) image_g116 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g117 : max4Projection g117 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g116 g015).trans
    ((congrArg₂ (· * ·) quotient_g116 quotient_g015).trans h)

@[expose] def g118 : max4Subgroup := g117 * g019
set_option maxRecDepth 2000 in
lemma image_g118 : representation g118 = decode rows115 := by
  exact (map_mul representation g117 g019).trans
    ((congrArg₂ (· * ·) image_g117 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g118 : max4Projection g118 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g117 g019).trans
    ((congrArg₂ (· * ·) quotient_g117 quotient_g019).trans h)

@[expose] def g119 : max4Subgroup := g118 * g018
set_option maxRecDepth 2000 in
lemma image_g119 : representation g119 = decode rows116 := by
  exact (map_mul representation g118 g018).trans
    ((congrArg₂ (· * ·) image_g118 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g119 : max4Projection g119 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g118 g018).trans
    ((congrArg₂ (· * ·) quotient_g118 quotient_g018).trans h)

@[expose] def g120 : max4Subgroup := g119 * g017
set_option maxRecDepth 2000 in
lemma image_g120 : representation g120 = decode rows117 := by
  exact (map_mul representation g119 g017).trans
    ((congrArg₂ (· * ·) image_g119 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g120 : max4Projection g120 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g119 g017).trans
    ((congrArg₂ (· * ·) quotient_g119 quotient_g017).trans h)

@[expose] def g121 : max4Subgroup := g120 * g019
set_option maxRecDepth 2000 in
lemma image_g121 : representation g121 = decode rows118 := by
  exact (map_mul representation g120 g019).trans
    ((congrArg₂ (· * ·) image_g120 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g121 : max4Projection g121 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g120 g019).trans
    ((congrArg₂ (· * ·) quotient_g120 quotient_g019).trans h)

@[expose] def g122 : max4Subgroup := g006 * g016
set_option maxRecDepth 2000 in
lemma image_g122 : representation g122 = decode rows119 := by
  exact (map_mul representation g006 g016).trans
    ((congrArg₂ (· * ·) image_g006 image_g016).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g122 : max4Projection g122 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g006 g016).trans
    ((congrArg₂ (· * ·) quotient_g006 quotient_g016).trans h)

@[expose] def g123 : max4Subgroup := g122 * g015
set_option maxRecDepth 2000 in
lemma image_g123 : representation g123 = decode rows120 := by
  exact (map_mul representation g122 g015).trans
    ((congrArg₂ (· * ·) image_g122 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g123 : max4Projection g123 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g122 g015).trans
    ((congrArg₂ (· * ·) quotient_g122 quotient_g015).trans h)

@[expose] def g124 : max4Subgroup := g123 * g019
set_option maxRecDepth 2000 in
lemma image_g124 : representation g124 = decode rows121 := by
  exact (map_mul representation g123 g019).trans
    ((congrArg₂ (· * ·) image_g123 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g124 : max4Projection g124 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g123 g019).trans
    ((congrArg₂ (· * ·) quotient_g123 quotient_g019).trans h)

@[expose] def g125 : max4Subgroup := g124 * g018
set_option maxRecDepth 2000 in
lemma image_g125 : representation g125 = decode rows122 := by
  exact (map_mul representation g124 g018).trans
    ((congrArg₂ (· * ·) image_g124 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g125 : max4Projection g125 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g124 g018).trans
    ((congrArg₂ (· * ·) quotient_g124 quotient_g018).trans h)

@[expose] def g126 : max4Subgroup := g006 * g009
set_option maxRecDepth 2000 in
lemma image_g126 : representation g126 = decode rows123 := by
  exact (map_mul representation g006 g009).trans
    ((congrArg₂ (· * ·) image_g006 image_g009).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g126 : max4Projection g126 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g006 g009).trans
    ((congrArg₂ (· * ·) quotient_g006 quotient_g009).trans h)

@[expose] def g127 : max4Subgroup := g126 * g011
set_option maxRecDepth 2000 in
lemma image_g127 : representation g127 = decode rows124 := by
  exact (map_mul representation g126 g011).trans
    ((congrArg₂ (· * ·) image_g126 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g127 : max4Projection g127 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g126 g011).trans
    ((congrArg₂ (· * ·) quotient_g126 quotient_g011).trans h)

@[expose] def g128 : max4Subgroup := g127 * g012
set_option maxRecDepth 2000 in
lemma image_g128 : representation g128 = decode rows125 := by
  exact (map_mul representation g127 g012).trans
    ((congrArg₂ (· * ·) image_g127 image_g012).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g128 : max4Projection g128 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g127 g012).trans
    ((congrArg₂ (· * ·) quotient_g127 quotient_g012).trans h)

@[expose] def g129 : max4Subgroup := g128 * g005
set_option maxRecDepth 2000 in
lemma image_g129 : representation g129 = decode rows126 := by
  exact (map_mul representation g128 g005).trans
    ((congrArg₂ (· * ·) image_g128 image_g005).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g129 : max4Projection g129 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g128 g005).trans
    ((congrArg₂ (· * ·) quotient_g128 quotient_g005).trans h)

@[expose] def g130 : max4Subgroup := g129 * g006
set_option maxRecDepth 2000 in
lemma image_g130 : representation g130 = decode rows127 := by
  exact (map_mul representation g129 g006).trans
    ((congrArg₂ (· * ·) image_g129 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g130 : max4Projection g130 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g129 g006).trans
    ((congrArg₂ (· * ·) quotient_g129 quotient_g006).trans h)

@[expose] def g131 : max4Subgroup := g130 * g007
set_option maxRecDepth 2000 in
lemma image_g131 : representation g131 = decode rows128 := by
  exact (map_mul representation g130 g007).trans
    ((congrArg₂ (· * ·) image_g130 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g131 : max4Projection g131 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g130 g007).trans
    ((congrArg₂ (· * ·) quotient_g130 quotient_g007).trans h)

@[expose] def g132 : max4Subgroup := g131 * g010
set_option maxRecDepth 2000 in
lemma image_g132 : representation g132 = decode rows129 := by
  exact (map_mul representation g131 g010).trans
    ((congrArg₂ (· * ·) image_g131 image_g010).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g132 : max4Projection g132 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g131 g010).trans
    ((congrArg₂ (· * ·) quotient_g131 quotient_g010).trans h)

@[expose] def g133 : max4Subgroup := g132 * g007
set_option maxRecDepth 2000 in
lemma image_g133 : representation g133 = decode rows130 := by
  exact (map_mul representation g132 g007).trans
    ((congrArg₂ (· * ·) image_g132 image_g007).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g133 : max4Projection g133 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g132 g007).trans
    ((congrArg₂ (· * ·) quotient_g132 quotient_g007).trans h)

@[expose] def g134 : max4Subgroup := g133 * g008
set_option maxRecDepth 2000 in
lemma image_g134 : representation g134 = decode rows131 := by
  exact (map_mul representation g133 g008).trans
    ((congrArg₂ (· * ·) image_g133 image_g008).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g134 : max4Projection g134 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g133 g008).trans
    ((congrArg₂ (· * ·) quotient_g133 quotient_g008).trans h)

@[expose] def g135 : max4Subgroup := g134 * g011
set_option maxRecDepth 2000 in
lemma image_g135 : representation g135 = decode rows132 := by
  exact (map_mul representation g134 g011).trans
    ((congrArg₂ (· * ·) image_g134 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g135 : max4Projection g135 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g134 g011).trans
    ((congrArg₂ (· * ·) quotient_g134 quotient_g011).trans h)

@[expose] def g136 : max4Subgroup := g135 * g015
set_option maxRecDepth 2000 in
lemma image_g136 : representation g136 = decode rows133 := by
  exact (map_mul representation g135 g015).trans
    ((congrArg₂ (· * ·) image_g135 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g136 : max4Projection g136 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g135 g015).trans
    ((congrArg₂ (· * ·) quotient_g135 quotient_g015).trans h)

@[expose] def g137 : max4Subgroup := g136 * g019
set_option maxRecDepth 2000 in
lemma image_g137 : representation g137 = decode rows134 := by
  exact (map_mul representation g136 g019).trans
    ((congrArg₂ (· * ·) image_g136 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g137 : max4Projection g137 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g136 g019).trans
    ((congrArg₂ (· * ·) quotient_g136 quotient_g019).trans h)

@[expose] def g138 : max4Subgroup := g137 * g018
set_option maxRecDepth 2000 in
lemma image_g138 : representation g138 = decode rows135 := by
  exact (map_mul representation g137 g018).trans
    ((congrArg₂ (· * ·) image_g137 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g138 : max4Projection g138 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g137 g018).trans
    ((congrArg₂ (· * ·) quotient_g137 quotient_g018).trans h)

@[expose] def g139 : max4Subgroup := g138 * g017
set_option maxRecDepth 2000 in
lemma image_g139 : representation g139 = decode rows136 := by
  exact (map_mul representation g138 g017).trans
    ((congrArg₂ (· * ·) image_g138 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g139 : max4Projection g139 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g138 g017).trans
    ((congrArg₂ (· * ·) quotient_g138 quotient_g017).trans h)

@[expose] def g140 : max4Subgroup := g139 * g019
set_option maxRecDepth 2000 in
lemma image_g140 : representation g140 = decode rows137 := by
  exact (map_mul representation g139 g019).trans
    ((congrArg₂ (· * ·) image_g139 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g140 : max4Projection g140 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g139 g019).trans
    ((congrArg₂ (· * ·) quotient_g139 quotient_g019).trans h)

@[expose] def g141 : max4Subgroup := g140 * g015
set_option maxRecDepth 2000 in
lemma image_g141 : representation g141 = decode rows138 := by
  exact (map_mul representation g140 g015).trans
    ((congrArg₂ (· * ·) image_g140 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g141 : max4Projection g141 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g140 g015).trans
    ((congrArg₂ (· * ·) quotient_g140 quotient_g015).trans h)

@[expose] def g142 : max4Subgroup := g141 * g006
set_option maxRecDepth 2000 in
lemma image_g142 : representation g142 = decode rows139 := by
  exact (map_mul representation g141 g006).trans
    ((congrArg₂ (· * ·) image_g141 image_g006).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g142 : max4Projection g142 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g141 g006).trans
    ((congrArg₂ (· * ·) quotient_g141 quotient_g006).trans h)

@[expose] def g143 : max4Subgroup := g142 * g016
set_option maxRecDepth 2000 in
lemma image_g143 : representation g143 = decode rows140 := by
  exact (map_mul representation g142 g016).trans
    ((congrArg₂ (· * ·) image_g142 image_g016).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g143 : max4Projection g143 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g142 g016).trans
    ((congrArg₂ (· * ·) quotient_g142 quotient_g016).trans h)

@[expose] def g144 : max4Subgroup := g143 * g015
set_option maxRecDepth 2000 in
lemma image_g144 : representation g144 = decode rows141 := by
  exact (map_mul representation g143 g015).trans
    ((congrArg₂ (· * ·) image_g143 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g144 : max4Projection g144 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g143 g015).trans
    ((congrArg₂ (· * ·) quotient_g143 quotient_g015).trans h)

@[expose] def g145 : max4Subgroup := g144 * g019
set_option maxRecDepth 2000 in
lemma image_g145 : representation g145 = decode rows142 := by
  exact (map_mul representation g144 g019).trans
    ((congrArg₂ (· * ·) image_g144 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g145 : max4Projection g145 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g144 g019).trans
    ((congrArg₂ (· * ·) quotient_g144 quotient_g019).trans h)

@[expose] def g146 : max4Subgroup := g145 * g018
set_option maxRecDepth 2000 in
lemma image_g146 : representation g146 = decode rows143 := by
  exact (map_mul representation g145 g018).trans
    ((congrArg₂ (· * ·) image_g145 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g146 : max4Projection g146 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g145 g018).trans
    ((congrArg₂ (· * ·) quotient_g145 quotient_g018).trans h)

@[expose] def g147 : max4Subgroup := g146 * g018
set_option maxRecDepth 2000 in
lemma image_g147 : representation g147 = decode rows142 := by
  exact (map_mul representation g146 g018).trans
    ((congrArg₂ (· * ·) image_g146 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g147 : max4Projection g147 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g146 g018).trans
    ((congrArg₂ (· * ·) quotient_g146 quotient_g018).trans h)

@[expose] def g148 : max4Subgroup := g007 * g008
set_option maxRecDepth 2000 in
lemma image_g148 : representation g148 = decode rows144 := by
  exact (map_mul representation g007 g008).trans
    ((congrArg₂ (· * ·) image_g007 image_g008).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g148 : max4Projection g148 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g007 g008).trans
    ((congrArg₂ (· * ·) quotient_g007 quotient_g008).trans h)

@[expose] def g149 : max4Subgroup := g148 * g011
set_option maxRecDepth 2000 in
lemma image_g149 : representation g149 = decode rows145 := by
  exact (map_mul representation g148 g011).trans
    ((congrArg₂ (· * ·) image_g148 image_g011).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g149 : max4Projection g149 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g148 g011).trans
    ((congrArg₂ (· * ·) quotient_g148 quotient_g011).trans h)

@[expose] def g150 : max4Subgroup := g149 * g015
set_option maxRecDepth 2000 in
lemma image_g150 : representation g150 = decode rows146 := by
  exact (map_mul representation g149 g015).trans
    ((congrArg₂ (· * ·) image_g149 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g150 : max4Projection g150 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g149 g015).trans
    ((congrArg₂ (· * ·) quotient_g149 quotient_g015).trans h)

@[expose] def g151 : max4Subgroup := g150 * g019
set_option maxRecDepth 2000 in
lemma image_g151 : representation g151 = decode rows147 := by
  exact (map_mul representation g150 g019).trans
    ((congrArg₂ (· * ·) image_g150 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g151 : max4Projection g151 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g150 g019).trans
    ((congrArg₂ (· * ·) quotient_g150 quotient_g019).trans h)

@[expose] def g152 : max4Subgroup := g151 * g018
set_option maxRecDepth 2000 in
lemma image_g152 : representation g152 = decode rows148 := by
  exact (map_mul representation g151 g018).trans
    ((congrArg₂ (· * ·) image_g151 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g152 : max4Projection g152 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g151 g018).trans
    ((congrArg₂ (· * ·) quotient_g151 quotient_g018).trans h)

@[expose] def g153 : max4Subgroup := g152 * g017
set_option maxRecDepth 2000 in
lemma image_g153 : representation g153 = decode rows149 := by
  exact (map_mul representation g152 g017).trans
    ((congrArg₂ (· * ·) image_g152 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g153 : max4Projection g153 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g152 g017).trans
    ((congrArg₂ (· * ·) quotient_g152 quotient_g017).trans h)

@[expose] def g154 : max4Subgroup := g012 * g014
set_option maxRecDepth 2000 in
lemma image_g154 : representation g154 = decode rows150 := by
  exact (map_mul representation g012 g014).trans
    ((congrArg₂ (· * ·) image_g012 image_g014).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g154 : max4Projection g154 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g012 g014).trans
    ((congrArg₂ (· * ·) quotient_g012 quotient_g014).trans h)

@[expose] def g155 : max4Subgroup := g154 * g015
set_option maxRecDepth 2000 in
lemma image_g155 : representation g155 = decode rows151 := by
  exact (map_mul representation g154 g015).trans
    ((congrArg₂ (· * ·) image_g154 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g155 : max4Projection g155 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g154 g015).trans
    ((congrArg₂ (· * ·) quotient_g154 quotient_g015).trans h)

@[expose] def g156 : max4Subgroup := g155 * g018
set_option maxRecDepth 2000 in
lemma image_g156 : representation g156 = decode rows152 := by
  exact (map_mul representation g155 g018).trans
    ((congrArg₂ (· * ·) image_g155 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g156 : max4Projection g156 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g155 g018).trans
    ((congrArg₂ (· * ·) quotient_g155 quotient_g018).trans h)

@[expose] def g157 : max4Subgroup := g156 * g017
set_option maxRecDepth 2000 in
lemma image_g157 : representation g157 = decode rows153 := by
  exact (map_mul representation g156 g017).trans
    ((congrArg₂ (· * ·) image_g156 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g157 : max4Projection g157 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g156 g017).trans
    ((congrArg₂ (· * ·) quotient_g156 quotient_g017).trans h)

@[expose] def g158 : max4Subgroup := g002 * g002
set_option maxRecDepth 2000 in
lemma image_g158 : representation g158 = decode rows154 := by
  exact (map_mul representation g002 g002).trans
    ((congrArg₂ (· * ·) image_g002 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g158 : max4Projection g158 = quot038 := by
  have h : quot002 * quot002 = quot038 := by decide +kernel
  exact (map_mul max4Projection g002 g002).trans
    ((congrArg₂ (· * ·) quotient_g002 quotient_g002).trans h)

@[expose] def g159 : max4Subgroup := g004⁻¹
set_option maxRecDepth 2000 in
lemma image_g159 : representation g159 = decode rows001 := by
  apply inverse_image g004 _ _ image_g004
  exact (product _ _ _ (by decide +kernel : ∀ i : Fin 28, Simplicity.Elevens.BridgeCertificate.fastRow (rows002.get i) rows001.toList = identityRows.get i)).trans decode_identity
lemma quotient_g159 : max4Projection g159 = quot002 := by
  rw [g159, map_inv, quotient_g004]
  decide +kernel

@[expose] def g160 : max4Subgroup := g159 * g001
set_option maxRecDepth 2000 in
lemma image_g160 : representation g160 = decode rows018 := by
  exact (map_mul representation g159 g001).trans
    ((congrArg₂ (· * ·) image_g159 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g160 : max4Projection g160 = quot004 := by
  have h : quot002 * quot001 = quot004 := by decide +kernel
  exact (map_mul max4Projection g159 g001).trans
    ((congrArg₂ (· * ·) quotient_g159 quotient_g001).trans h)

@[expose] def g161 : max4Subgroup := g160 * g004
set_option maxRecDepth 2000 in
lemma image_g161 : representation g161 = decode rows155 := by
  exact (map_mul representation g160 g004).trans
    ((congrArg₂ (· * ·) image_g160 image_g004).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g161 : max4Projection g161 = quot039 := by
  have h : quot004 * quot003 = quot039 := by decide +kernel
  exact (map_mul max4Projection g160 g004).trans
    ((congrArg₂ (· * ·) quotient_g160 quotient_g004).trans h)

@[expose] def g162 : max4Subgroup := g004 * g001
set_option maxRecDepth 2000 in
lemma image_g162 : representation g162 = decode rows156 := by
  exact (map_mul representation g004 g001).trans
    ((congrArg₂ (· * ·) image_g004 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g162 : max4Projection g162 = quot040 := by
  have h : quot003 * quot001 = quot040 := by decide +kernel
  exact (map_mul max4Projection g004 g001).trans
    ((congrArg₂ (· * ·) quotient_g004 quotient_g001).trans h)

@[expose] def g163 : max4Subgroup := g162 * g002
set_option maxRecDepth 2000 in
lemma image_g163 : representation g163 = decode rows157 := by
  exact (map_mul representation g162 g002).trans
    ((congrArg₂ (· * ·) image_g162 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g163 : max4Projection g163 = quot041 := by
  have h : quot040 * quot002 = quot041 := by decide +kernel
  exact (map_mul max4Projection g162 g002).trans
    ((congrArg₂ (· * ·) quotient_g162 quotient_g002).trans h)

@[expose] def g164 : max4Subgroup := g158⁻¹
set_option maxRecDepth 2000 in
lemma image_g164 : representation g164 = decode rows154 := by
  apply inverse_image g158 _ _ image_g158
  exact (product _ _ _ (by decide +kernel : ∀ i : Fin 28, Simplicity.Elevens.BridgeCertificate.fastRow (rows154.get i) rows154.toList = identityRows.get i)).trans decode_identity
lemma quotient_g164 : max4Projection g164 = quot038 := by
  rw [g164, map_inv, quotient_g158]
  decide +kernel

@[expose] def g165 : max4Subgroup := g164 * g001
set_option maxRecDepth 2000 in
lemma image_g165 : representation g165 = decode rows158 := by
  exact (map_mul representation g164 g001).trans
    ((congrArg₂ (· * ·) image_g164 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g165 : max4Projection g165 = quot042 := by
  have h : quot038 * quot001 = quot042 := by decide +kernel
  exact (map_mul max4Projection g164 g001).trans
    ((congrArg₂ (· * ·) quotient_g164 quotient_g001).trans h)

@[expose] def g166 : max4Subgroup := g165 * g084
set_option maxRecDepth 2000 in
lemma image_g166 : representation g166 = decode identityRows := by
  exact (map_mul representation g165 g084).trans
    ((congrArg₂ (· * ·) image_g165 image_g084).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g166 : max4Projection g166 = quot000 := by
  have h : quot042 * quot024 = quot000 := by decide +kernel
  exact (map_mul max4Projection g165 g084).trans
    ((congrArg₂ (· * ·) quotient_g165 quotient_g084).trans h)

@[expose] def g167 : max4Subgroup := g084⁻¹
set_option maxRecDepth 2000 in
lemma image_g167 : representation g167 = decode rows158 := by
  apply inverse_image g084 _ _ image_g084
  exact (product _ _ _ (by decide +kernel : ∀ i : Fin 28, Simplicity.Elevens.BridgeCertificate.fastRow (rows081.get i) rows158.toList = identityRows.get i)).trans decode_identity
lemma quotient_g167 : max4Projection g167 = quot042 := by
  rw [g167, map_inv, quotient_g084]
  decide +kernel

@[expose] def g168 : max4Subgroup := g167 * g001
set_option maxRecDepth 2000 in
lemma image_g168 : representation g168 = decode rows154 := by
  exact (map_mul representation g167 g001).trans
    ((congrArg₂ (· * ·) image_g167 image_g001).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g168 : max4Projection g168 = quot038 := by
  have h : quot042 * quot001 = quot038 := by decide +kernel
  exact (map_mul max4Projection g167 g001).trans
    ((congrArg₂ (· * ·) quotient_g167 quotient_g001).trans h)

@[expose] def g169 : max4Subgroup := g168 * g158
set_option maxRecDepth 2000 in
lemma image_g169 : representation g169 = decode identityRows := by
  exact (map_mul representation g168 g158).trans
    ((congrArg₂ (· * ·) image_g168 image_g158).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g169 : max4Projection g169 = quot000 := by
  have h : quot038 * quot038 = quot000 := by decide +kernel
  exact (map_mul max4Projection g168 g158).trans
    ((congrArg₂ (· * ·) quotient_g168 quotient_g158).trans h)

@[expose] def g170 : max4Subgroup := g004 * g002
set_option maxRecDepth 2000 in
lemma image_g170 : representation g170 = decode identityRows := by
  exact (map_mul representation g004 g002).trans
    ((congrArg₂ (· * ·) image_g004 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g170 : max4Projection g170 = quot000 := by
  have h : quot003 * quot002 = quot000 := by decide +kernel
  exact (map_mul max4Projection g004 g002).trans
    ((congrArg₂ (· * ·) quotient_g004 quotient_g002).trans h)

@[expose] def g171 : max4Subgroup := g002 * g004
set_option maxRecDepth 2000 in
lemma image_g171 : representation g171 = decode identityRows := by
  exact (map_mul representation g002 g004).trans
    ((congrArg₂ (· * ·) image_g002 image_g004).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g171 : max4Projection g171 = quot000 := by
  have h : quot002 * quot003 = quot000 := by decide +kernel
  exact (map_mul max4Projection g002 g004).trans
    ((congrArg₂ (· * ·) quotient_g002 quotient_g004).trans h)

@[expose] def g172 : max4Subgroup := g164 * g002
set_option maxRecDepth 2000 in
lemma image_g172 : representation g172 = decode rows002 := by
  exact (map_mul representation g164 g002).trans
    ((congrArg₂ (· * ·) image_g164 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g172 : max4Projection g172 = quot003 := by
  have h : quot038 * quot002 = quot003 := by decide +kernel
  exact (map_mul max4Projection g164 g002).trans
    ((congrArg₂ (· * ·) quotient_g164 quotient_g002).trans h)

@[expose] def g173 : max4Subgroup := g172 * g002
set_option maxRecDepth 2000 in
lemma image_g173 : representation g173 = decode identityRows := by
  exact (map_mul representation g172 g002).trans
    ((congrArg₂ (· * ·) image_g172 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g173 : max4Projection g173 = quot000 := by
  have h : quot003 * quot002 = quot000 := by decide +kernel
  exact (map_mul max4Projection g172 g002).trans
    ((congrArg₂ (· * ·) quotient_g172 quotient_g002).trans h)

@[expose] def g174 : max4Subgroup := g167 * g002
set_option maxRecDepth 2000 in
lemma image_g174 : representation g174 = decode rows159 := by
  exact (map_mul representation g167 g002).trans
    ((congrArg₂ (· * ·) image_g167 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g174 : max4Projection g174 = quot043 := by
  have h : quot042 * quot002 = quot043 := by decide +kernel
  exact (map_mul max4Projection g167 g002).trans
    ((congrArg₂ (· * ·) quotient_g167 quotient_g002).trans h)

@[expose] def g175 : max4Subgroup := g174 * g084
set_option maxRecDepth 2000 in
lemma image_g175 : representation g175 = decode rows160 := by
  exact (map_mul representation g174 g084).trans
    ((congrArg₂ (· * ·) image_g174 image_g084).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g175 : max4Projection g175 = quot044 := by
  have h : quot043 * quot024 = quot044 := by decide +kernel
  exact (map_mul max4Projection g174 g084).trans
    ((congrArg₂ (· * ·) quotient_g174 quotient_g084).trans h)

@[expose] def g176 : max4Subgroup := g159 * g002
set_option maxRecDepth 2000 in
lemma image_g176 : representation g176 = decode rows154 := by
  exact (map_mul representation g159 g002).trans
    ((congrArg₂ (· * ·) image_g159 image_g002).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g176 : max4Projection g176 = quot038 := by
  have h : quot002 * quot002 = quot038 := by decide +kernel
  exact (map_mul max4Projection g159 g002).trans
    ((congrArg₂ (· * ·) quotient_g159 quotient_g002).trans h)

@[expose] def g177 : max4Subgroup := g176 * g158
set_option maxRecDepth 2000 in
lemma image_g177 : representation g177 = decode identityRows := by
  exact (map_mul representation g176 g158).trans
    ((congrArg₂ (· * ·) image_g176 image_g158).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g177 : max4Projection g177 = quot000 := by
  have h : quot038 * quot038 = quot000 := by decide +kernel
  exact (map_mul max4Projection g176 g158).trans
    ((congrArg₂ (· * ·) quotient_g176 quotient_g158).trans h)

@[expose] def g178 : max4Subgroup := g082 * g082
set_option maxRecDepth 2000 in
lemma image_g178 : representation g178 = decode identityRows := by
  exact (map_mul representation g082 g082).trans
    ((congrArg₂ (· * ·) image_g082 image_g082).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g178 : max4Projection g178 = quot000 := by
  have h : quot022 * quot022 = quot000 := by decide +kernel
  exact (map_mul max4Projection g082 g082).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g082).trans h)

@[expose] def g179 : max4Subgroup := g110 * g110
set_option maxRecDepth 2000 in
lemma image_g179 : representation g179 = decode identityRows := by
  exact (map_mul representation g110 g110).trans
    ((congrArg₂ (· * ·) image_g110 image_g110).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g179 : max4Projection g179 = quot000 := by
  have h : quot037 * quot037 = quot000 := by decide +kernel
  exact (map_mul max4Projection g110 g110).trans
    ((congrArg₂ (· * ·) quotient_g110 quotient_g110).trans h)

@[expose] def g180 : max4Subgroup := g121 * g121
set_option maxRecDepth 2000 in
lemma image_g180 : representation g180 = decode identityRows := by
  exact (map_mul representation g121 g121).trans
    ((congrArg₂ (· * ·) image_g121 image_g121).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g180 : max4Projection g180 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g121 g121).trans
    ((congrArg₂ (· * ·) quotient_g121 quotient_g121).trans h)

@[expose] def g181 : max4Subgroup := g015 * g015
set_option maxRecDepth 2000 in
lemma image_g181 : representation g181 = decode identityRows := by
  exact (map_mul representation g015 g015).trans
    ((congrArg₂ (· * ·) image_g015 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g181 : max4Projection g181 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g015 g015).trans
    ((congrArg₂ (· * ·) quotient_g015 quotient_g015).trans h)

@[expose] def g182 : max4Subgroup := g125 * g125
set_option maxRecDepth 2000 in
lemma image_g182 : representation g182 = decode identityRows := by
  exact (map_mul representation g125 g125).trans
    ((congrArg₂ (· * ·) image_g125 image_g125).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g182 : max4Projection g182 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g125 g125).trans
    ((congrArg₂ (· * ·) quotient_g125 quotient_g125).trans h)

@[expose] def g183 : max4Subgroup := g147 * g147
set_option maxRecDepth 2000 in
lemma image_g183 : representation g183 = decode identityRows := by
  exact (map_mul representation g147 g147).trans
    ((congrArg₂ (· * ·) image_g147 image_g147).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g183 : max4Projection g183 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g147 g147).trans
    ((congrArg₂ (· * ·) quotient_g147 quotient_g147).trans h)

@[expose] def g184 : max4Subgroup := g153 * g153
set_option maxRecDepth 2000 in
lemma image_g184 : representation g184 = decode identityRows := by
  exact (map_mul representation g153 g153).trans
    ((congrArg₂ (· * ·) image_g153 image_g153).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g184 : max4Projection g184 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g153 g153).trans
    ((congrArg₂ (· * ·) quotient_g153 quotient_g153).trans h)

@[expose] def g185 : max4Subgroup := g157 * g157
set_option maxRecDepth 2000 in
lemma image_g185 : representation g185 = decode identityRows := by
  exact (map_mul representation g157 g157).trans
    ((congrArg₂ (· * ·) image_g157 image_g157).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g185 : max4Projection g185 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g157 g157).trans
    ((congrArg₂ (· * ·) quotient_g157 quotient_g157).trans h)

@[expose] def g186 : max4Subgroup := g019 * g019
set_option maxRecDepth 2000 in
lemma image_g186 : representation g186 = decode identityRows := by
  exact (map_mul representation g019 g019).trans
    ((congrArg₂ (· * ·) image_g019 image_g019).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g186 : max4Projection g186 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g019 g019).trans
    ((congrArg₂ (· * ·) quotient_g019 quotient_g019).trans h)

@[expose] def g187 : max4Subgroup := g018 * g018
set_option maxRecDepth 2000 in
lemma image_g187 : representation g187 = decode identityRows := by
  exact (map_mul representation g018 g018).trans
    ((congrArg₂ (· * ·) image_g018 image_g018).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g187 : max4Projection g187 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g018 g018).trans
    ((congrArg₂ (· * ·) quotient_g018 quotient_g018).trans h)

@[expose] def g188 : max4Subgroup := g017 * g017
set_option maxRecDepth 2000 in
lemma image_g188 : representation g188 = decode identityRows := by
  exact (map_mul representation g017 g017).trans
    ((congrArg₂ (· * ·) image_g017 image_g017).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g188 : max4Projection g188 = quot000 := by
  have h : quot000 * quot000 = quot000 := by decide +kernel
  exact (map_mul max4Projection g017 g017).trans
    ((congrArg₂ (· * ·) quotient_g017 quotient_g017).trans h)

@[expose] def g189 : max4Subgroup := g082 * g110
set_option maxRecDepth 2000 in
lemma image_g189 : representation g189 = decode rows161 := by
  exact (map_mul representation g082 g110).trans
    ((congrArg₂ (· * ·) image_g082 image_g110).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g189 : max4Projection g189 = quot045 := by
  have h : quot022 * quot037 = quot045 := by decide +kernel
  exact (map_mul max4Projection g082 g110).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g110).trans h)

@[expose] def g190 : max4Subgroup := g110 * g082
set_option maxRecDepth 2000 in
lemma image_g190 : representation g190 = decode rows161 := by
  exact (map_mul representation g110 g082).trans
    ((congrArg₂ (· * ·) image_g110 image_g082).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g190 : max4Projection g190 = quot045 := by
  have h : quot037 * quot022 = quot045 := by decide +kernel
  exact (map_mul max4Projection g110 g082).trans
    ((congrArg₂ (· * ·) quotient_g110 quotient_g082).trans h)

@[expose] def g191 : max4Subgroup := g082 * g121
set_option maxRecDepth 2000 in
lemma image_g191 : representation g191 = decode rows162 := by
  exact (map_mul representation g082 g121).trans
    ((congrArg₂ (· * ·) image_g082 image_g121).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g191 : max4Projection g191 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g082 g121).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g121).trans h)

@[expose] def g192 : max4Subgroup := g121 * g082
set_option maxRecDepth 2000 in
lemma image_g192 : representation g192 = decode rows162 := by
  exact (map_mul representation g121 g082).trans
    ((congrArg₂ (· * ·) image_g121 image_g082).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g192 : max4Projection g192 = quot022 := by
  have h : quot000 * quot022 = quot022 := by decide +kernel
  exact (map_mul max4Projection g121 g082).trans
    ((congrArg₂ (· * ·) quotient_g121 quotient_g082).trans h)

@[expose] def g193 : max4Subgroup := g082 * g015
set_option maxRecDepth 2000 in
lemma image_g193 : representation g193 = decode rows163 := by
  exact (map_mul representation g082 g015).trans
    ((congrArg₂ (· * ·) image_g082 image_g015).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g193 : max4Projection g193 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g082 g015).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g015).trans h)

@[expose] def g194 : max4Subgroup := g015 * g082
set_option maxRecDepth 2000 in
lemma image_g194 : representation g194 = decode rows163 := by
  exact (map_mul representation g015 g082).trans
    ((congrArg₂ (· * ·) image_g015 image_g082).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g194 : max4Projection g194 = quot022 := by
  have h : quot000 * quot022 = quot022 := by decide +kernel
  exact (map_mul max4Projection g015 g082).trans
    ((congrArg₂ (· * ·) quotient_g015 quotient_g082).trans h)

@[expose] def g195 : max4Subgroup := g082 * g125
set_option maxRecDepth 2000 in
lemma image_g195 : representation g195 = decode rows067 := by
  exact (map_mul representation g082 g125).trans
    ((congrArg₂ (· * ·) image_g082 image_g125).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g195 : max4Projection g195 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g082 g125).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g125).trans h)

@[expose] def g196 : max4Subgroup := g125 * g082
set_option maxRecDepth 2000 in
lemma image_g196 : representation g196 = decode rows067 := by
  exact (map_mul representation g125 g082).trans
    ((congrArg₂ (· * ·) image_g125 image_g082).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g196 : max4Projection g196 = quot022 := by
  have h : quot000 * quot022 = quot022 := by decide +kernel
  exact (map_mul max4Projection g125 g082).trans
    ((congrArg₂ (· * ·) quotient_g125 quotient_g082).trans h)

@[expose] def g197 : max4Subgroup := g082 * g147
set_option maxRecDepth 2000 in
lemma image_g197 : representation g197 = decode rows164 := by
  exact (map_mul representation g082 g147).trans
    ((congrArg₂ (· * ·) image_g082 image_g147).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g197 : max4Projection g197 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g082 g147).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g147).trans h)

@[expose] def g198 : max4Subgroup := g147 * g082
set_option maxRecDepth 2000 in
lemma image_g198 : representation g198 = decode rows164 := by
  exact (map_mul representation g147 g082).trans
    ((congrArg₂ (· * ·) image_g147 image_g082).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g198 : max4Projection g198 = quot022 := by
  have h : quot000 * quot022 = quot022 := by decide +kernel
  exact (map_mul max4Projection g147 g082).trans
    ((congrArg₂ (· * ·) quotient_g147 quotient_g082).trans h)

@[expose] def g199 : max4Subgroup := g082 * g153
set_option maxRecDepth 2000 in
lemma image_g199 : representation g199 = decode rows165 := by
  exact (map_mul representation g082 g153).trans
    ((congrArg₂ (· * ·) image_g082 image_g153).trans (product _ _ _ (by decide +kernel)))
lemma quotient_g199 : max4Projection g199 = quot022 := by
  have h : quot022 * quot000 = quot022 := by decide +kernel
  exact (map_mul max4Projection g082 g153).trans
    ((congrArg₂ (· * ·) quotient_g082 quotient_g153).trans h)

end MathieuOverlap
end Janko4.LocalStructure.SymmetricLinear
