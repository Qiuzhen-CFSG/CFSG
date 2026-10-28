module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WordEvaluation.NodeTables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.WordEvaluation.Checking

/-!
# Checked shared Fi22 word nodes 677–684

Each product or proposed right inverse is checked on all 3510 letters.
The natural-number checker is proved equivalent to `mapCheck`, and each
bounded comparison is reduced by the Lean kernel. No external
calculation is trusted. `WordEvaluation.lean` consumes every equation
to identify these tables with the literal shared word nodes.

Source: `ImageContainmentCertificate/source/image-programs.json`, shared in
`ImageWords.lean`, for the Fi23 coordinate action in GLS3 Table 5.3u.
`WordEvaluation/source/generate.py` reproduces this file; its README records
attribution, checking conventions and measurements.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions.WordEvaluation
open Fi22.KernelCertificate

set_option Elab.async false

private def node677Check : Nat → Bool := mulCheck node676Table node112Table node677Table

set_option maxRecDepth 1000 in
private theorem node677Check0 : checkRange node677Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check1 : checkRange node677Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check2 : checkRange node677Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check3 : checkRange node677Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check4 : checkRange node677Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check5 : checkRange node677Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check6 : checkRange node677Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check7 : checkRange node677Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check8 : checkRange node677Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check9 : checkRange node677Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check10 : checkRange node677Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check11 : checkRange node677Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check12 : checkRange node677Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check13 : checkRange node677Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check14 : checkRange node677Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check15 : checkRange node677Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check16 : checkRange node677Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check17 : checkRange node677Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check18 : checkRange node677Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check19 : checkRange node677Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check20 : checkRange node677Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check21 : checkRange node677Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check22 : checkRange node677Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check23 : checkRange node677Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check24 : checkRange node677Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check25 : checkRange node677Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check26 : checkRange node677Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node677Check27 : checkRange node677Check 7 3456 = true := by
  decide +kernel

theorem node677_eq (x : Fin 3510) : (fun x => tableAction node676Table (tableAction node112Table x)) x = (tableAction node677Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node677Check0
  · exact node677Check1
  · exact node677Check2
  · exact node677Check3
  · exact node677Check4
  · exact node677Check5
  · exact node677Check6
  · exact node677Check7
  · exact node677Check8
  · exact node677Check9
  · exact node677Check10
  · exact node677Check11
  · exact node677Check12
  · exact node677Check13
  · exact node677Check14
  · exact node677Check15
  · exact node677Check16
  · exact node677Check17
  · exact node677Check18
  · exact node677Check19
  · exact node677Check20
  · exact node677Check21
  · exact node677Check22
  · exact node677Check23
  · exact node677Check24
  · exact node677Check25
  · exact node677Check26
  · exact node677Check27

private def node678Check : Nat → Bool := mulCheck node677Table node202Table node678Table

set_option maxRecDepth 1000 in
private theorem node678Check0 : checkRange node678Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check1 : checkRange node678Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check2 : checkRange node678Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check3 : checkRange node678Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check4 : checkRange node678Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check5 : checkRange node678Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check6 : checkRange node678Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check7 : checkRange node678Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check8 : checkRange node678Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check9 : checkRange node678Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check10 : checkRange node678Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check11 : checkRange node678Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check12 : checkRange node678Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check13 : checkRange node678Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check14 : checkRange node678Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check15 : checkRange node678Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check16 : checkRange node678Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check17 : checkRange node678Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check18 : checkRange node678Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check19 : checkRange node678Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check20 : checkRange node678Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check21 : checkRange node678Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check22 : checkRange node678Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check23 : checkRange node678Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check24 : checkRange node678Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check25 : checkRange node678Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check26 : checkRange node678Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node678Check27 : checkRange node678Check 7 3456 = true := by
  decide +kernel

theorem node678_eq (x : Fin 3510) : (fun x => tableAction node677Table (tableAction node202Table x)) x = (tableAction node678Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node678Check0
  · exact node678Check1
  · exact node678Check2
  · exact node678Check3
  · exact node678Check4
  · exact node678Check5
  · exact node678Check6
  · exact node678Check7
  · exact node678Check8
  · exact node678Check9
  · exact node678Check10
  · exact node678Check11
  · exact node678Check12
  · exact node678Check13
  · exact node678Check14
  · exact node678Check15
  · exact node678Check16
  · exact node678Check17
  · exact node678Check18
  · exact node678Check19
  · exact node678Check20
  · exact node678Check21
  · exact node678Check22
  · exact node678Check23
  · exact node678Check24
  · exact node678Check25
  · exact node678Check26
  · exact node678Check27

private def node679Check : Nat → Bool := mulCheck node678Table node376Table node679Table

set_option maxRecDepth 1000 in
private theorem node679Check0 : checkRange node679Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check1 : checkRange node679Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check2 : checkRange node679Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check3 : checkRange node679Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check4 : checkRange node679Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check5 : checkRange node679Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check6 : checkRange node679Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check7 : checkRange node679Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check8 : checkRange node679Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check9 : checkRange node679Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check10 : checkRange node679Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check11 : checkRange node679Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check12 : checkRange node679Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check13 : checkRange node679Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check14 : checkRange node679Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check15 : checkRange node679Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check16 : checkRange node679Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check17 : checkRange node679Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check18 : checkRange node679Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check19 : checkRange node679Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check20 : checkRange node679Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check21 : checkRange node679Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check22 : checkRange node679Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check23 : checkRange node679Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check24 : checkRange node679Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check25 : checkRange node679Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check26 : checkRange node679Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node679Check27 : checkRange node679Check 7 3456 = true := by
  decide +kernel

theorem node679_eq (x : Fin 3510) : (fun x => tableAction node678Table (tableAction node376Table x)) x = (tableAction node679Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node679Check0
  · exact node679Check1
  · exact node679Check2
  · exact node679Check3
  · exact node679Check4
  · exact node679Check5
  · exact node679Check6
  · exact node679Check7
  · exact node679Check8
  · exact node679Check9
  · exact node679Check10
  · exact node679Check11
  · exact node679Check12
  · exact node679Check13
  · exact node679Check14
  · exact node679Check15
  · exact node679Check16
  · exact node679Check17
  · exact node679Check18
  · exact node679Check19
  · exact node679Check20
  · exact node679Check21
  · exact node679Check22
  · exact node679Check23
  · exact node679Check24
  · exact node679Check25
  · exact node679Check26
  · exact node679Check27

private def node680Check : Nat → Bool := mulCheck node679Table node202Table node680Table

set_option maxRecDepth 1000 in
private theorem node680Check0 : checkRange node680Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check1 : checkRange node680Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check2 : checkRange node680Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check3 : checkRange node680Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check4 : checkRange node680Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check5 : checkRange node680Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check6 : checkRange node680Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check7 : checkRange node680Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check8 : checkRange node680Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check9 : checkRange node680Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check10 : checkRange node680Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check11 : checkRange node680Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check12 : checkRange node680Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check13 : checkRange node680Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check14 : checkRange node680Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check15 : checkRange node680Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check16 : checkRange node680Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check17 : checkRange node680Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check18 : checkRange node680Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check19 : checkRange node680Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check20 : checkRange node680Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check21 : checkRange node680Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check22 : checkRange node680Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check23 : checkRange node680Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check24 : checkRange node680Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check25 : checkRange node680Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check26 : checkRange node680Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node680Check27 : checkRange node680Check 7 3456 = true := by
  decide +kernel

theorem node680_eq (x : Fin 3510) : (fun x => tableAction node679Table (tableAction node202Table x)) x = (tableAction node680Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node680Check0
  · exact node680Check1
  · exact node680Check2
  · exact node680Check3
  · exact node680Check4
  · exact node680Check5
  · exact node680Check6
  · exact node680Check7
  · exact node680Check8
  · exact node680Check9
  · exact node680Check10
  · exact node680Check11
  · exact node680Check12
  · exact node680Check13
  · exact node680Check14
  · exact node680Check15
  · exact node680Check16
  · exact node680Check17
  · exact node680Check18
  · exact node680Check19
  · exact node680Check20
  · exact node680Check21
  · exact node680Check22
  · exact node680Check23
  · exact node680Check24
  · exact node680Check25
  · exact node680Check26
  · exact node680Check27

private def node681Check : Nat → Bool := mulCheck node680Table node242Table node681Table

set_option maxRecDepth 1000 in
private theorem node681Check0 : checkRange node681Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check1 : checkRange node681Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check2 : checkRange node681Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check3 : checkRange node681Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check4 : checkRange node681Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check5 : checkRange node681Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check6 : checkRange node681Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check7 : checkRange node681Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check8 : checkRange node681Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check9 : checkRange node681Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check10 : checkRange node681Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check11 : checkRange node681Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check12 : checkRange node681Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check13 : checkRange node681Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check14 : checkRange node681Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check15 : checkRange node681Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check16 : checkRange node681Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check17 : checkRange node681Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check18 : checkRange node681Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check19 : checkRange node681Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check20 : checkRange node681Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check21 : checkRange node681Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check22 : checkRange node681Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check23 : checkRange node681Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check24 : checkRange node681Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check25 : checkRange node681Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check26 : checkRange node681Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node681Check27 : checkRange node681Check 7 3456 = true := by
  decide +kernel

theorem node681_eq (x : Fin 3510) : (fun x => tableAction node680Table (tableAction node242Table x)) x = (tableAction node681Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node681Check0
  · exact node681Check1
  · exact node681Check2
  · exact node681Check3
  · exact node681Check4
  · exact node681Check5
  · exact node681Check6
  · exact node681Check7
  · exact node681Check8
  · exact node681Check9
  · exact node681Check10
  · exact node681Check11
  · exact node681Check12
  · exact node681Check13
  · exact node681Check14
  · exact node681Check15
  · exact node681Check16
  · exact node681Check17
  · exact node681Check18
  · exact node681Check19
  · exact node681Check20
  · exact node681Check21
  · exact node681Check22
  · exact node681Check23
  · exact node681Check24
  · exact node681Check25
  · exact node681Check26
  · exact node681Check27

private def node682Check : Nat → Bool := mulCheck node681Table node477Table node682Table

set_option maxRecDepth 1000 in
private theorem node682Check0 : checkRange node682Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check1 : checkRange node682Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check2 : checkRange node682Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check3 : checkRange node682Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check4 : checkRange node682Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check5 : checkRange node682Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check6 : checkRange node682Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check7 : checkRange node682Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check8 : checkRange node682Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check9 : checkRange node682Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check10 : checkRange node682Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check11 : checkRange node682Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check12 : checkRange node682Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check13 : checkRange node682Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check14 : checkRange node682Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check15 : checkRange node682Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check16 : checkRange node682Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check17 : checkRange node682Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check18 : checkRange node682Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check19 : checkRange node682Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check20 : checkRange node682Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check21 : checkRange node682Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check22 : checkRange node682Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check23 : checkRange node682Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check24 : checkRange node682Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check25 : checkRange node682Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check26 : checkRange node682Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node682Check27 : checkRange node682Check 7 3456 = true := by
  decide +kernel

theorem node682_eq (x : Fin 3510) : (fun x => tableAction node681Table (tableAction node477Table x)) x = (tableAction node682Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node682Check0
  · exact node682Check1
  · exact node682Check2
  · exact node682Check3
  · exact node682Check4
  · exact node682Check5
  · exact node682Check6
  · exact node682Check7
  · exact node682Check8
  · exact node682Check9
  · exact node682Check10
  · exact node682Check11
  · exact node682Check12
  · exact node682Check13
  · exact node682Check14
  · exact node682Check15
  · exact node682Check16
  · exact node682Check17
  · exact node682Check18
  · exact node682Check19
  · exact node682Check20
  · exact node682Check21
  · exact node682Check22
  · exact node682Check23
  · exact node682Check24
  · exact node682Check25
  · exact node682Check26
  · exact node682Check27

private def node683Check : Nat → Bool := mulCheck node682Table node159Table node683Table

set_option maxRecDepth 1000 in
private theorem node683Check0 : checkRange node683Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check1 : checkRange node683Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check2 : checkRange node683Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check3 : checkRange node683Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check4 : checkRange node683Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check5 : checkRange node683Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check6 : checkRange node683Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check7 : checkRange node683Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check8 : checkRange node683Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check9 : checkRange node683Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check10 : checkRange node683Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check11 : checkRange node683Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check12 : checkRange node683Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check13 : checkRange node683Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check14 : checkRange node683Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check15 : checkRange node683Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check16 : checkRange node683Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check17 : checkRange node683Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check18 : checkRange node683Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check19 : checkRange node683Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check20 : checkRange node683Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check21 : checkRange node683Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check22 : checkRange node683Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check23 : checkRange node683Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check24 : checkRange node683Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check25 : checkRange node683Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check26 : checkRange node683Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node683Check27 : checkRange node683Check 7 3456 = true := by
  decide +kernel

theorem node683_eq (x : Fin 3510) : (fun x => tableAction node682Table (tableAction node159Table x)) x = (tableAction node683Table) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_mul_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node683Check0
  · exact node683Check1
  · exact node683Check2
  · exact node683Check3
  · exact node683Check4
  · exact node683Check5
  · exact node683Check6
  · exact node683Check7
  · exact node683Check8
  · exact node683Check9
  · exact node683Check10
  · exact node683Check11
  · exact node683Check12
  · exact node683Check13
  · exact node683Check14
  · exact node683Check15
  · exact node683Check16
  · exact node683Check17
  · exact node683Check18
  · exact node683Check19
  · exact node683Check20
  · exact node683Check21
  · exact node683Check22
  · exact node683Check23
  · exact node683Check24
  · exact node683Check25
  · exact node683Check26
  · exact node683Check27

private def node684Check : Nat → Bool := invCheck node683Table imageTable7

set_option maxRecDepth 1000 in
private theorem node684Check0 : checkRange node684Check 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check1 : checkRange node684Check 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check2 : checkRange node684Check 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check3 : checkRange node684Check 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check4 : checkRange node684Check 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check5 : checkRange node684Check 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check6 : checkRange node684Check 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check7 : checkRange node684Check 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check8 : checkRange node684Check 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check9 : checkRange node684Check 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check10 : checkRange node684Check 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check11 : checkRange node684Check 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check12 : checkRange node684Check 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check13 : checkRange node684Check 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check14 : checkRange node684Check 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check15 : checkRange node684Check 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check16 : checkRange node684Check 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check17 : checkRange node684Check 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check18 : checkRange node684Check 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check19 : checkRange node684Check 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check20 : checkRange node684Check 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check21 : checkRange node684Check 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check22 : checkRange node684Check 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check23 : checkRange node684Check 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check24 : checkRange node684Check 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check25 : checkRange node684Check 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check26 : checkRange node684Check 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem node684Check27 : checkRange node684Check 7 3456 = true := by
  decide +kernel

theorem node684_eq (x : Fin 3510) : (fun x => tableAction node683Table (tableAction imageTable7 x)) x = (fun x : Fin 3510 => x) x := by
  apply map_eq_of_checks (by decide) _ _ ?_ x
  rw [mapCheck_inv_eq]
  intro b
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact node684Check0
  · exact node684Check1
  · exact node684Check2
  · exact node684Check3
  · exact node684Check4
  · exact node684Check5
  · exact node684Check6
  · exact node684Check7
  · exact node684Check8
  · exact node684Check9
  · exact node684Check10
  · exact node684Check11
  · exact node684Check12
  · exact node684Check13
  · exact node684Check14
  · exact node684Check15
  · exact node684Check16
  · exact node684Check17
  · exact node684Check18
  · exact node684Check19
  · exact node684Check20
  · exact node684Check21
  · exact node684Check22
  · exact node684Check23
  · exact node684Check24
  · exact node684Check25
  · exact node684Check26
  · exact node684Check27

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions.WordEvaluation
