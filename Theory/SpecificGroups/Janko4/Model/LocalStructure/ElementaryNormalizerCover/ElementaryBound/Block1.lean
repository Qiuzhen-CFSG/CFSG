module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock1 : (List.finRange 16).all (fun a => pointCheck (actor 1 a)) = true := by decide +kernel

theorem rowBlock1 : (List.finRange 16).all (fun a => rowCheck (actor 1 a)) = true := by decide +kernel

theorem fixedBlock1 : (List.finRange 16).all (fun a => fastFixedCheck (actor 1 a)) = true := by decide +kernel

theorem codeBlock1 : (List.finRange 16).all (fun a => codeCheck (actor 1 a)) = true := by decide +kernel

theorem compatibleBlock1 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 1 a) w)) = true := by decide +kernel

theorem coverageBlock1 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (1,b,c))) = true := by decide +kernel

theorem coverageBlock13 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (13,b,c))) = true := by decide +kernel

theorem lowBlock1 : (List.finRange 16).all (fun a => lowCheck (actor 1 a)) = true := by decide +kernel

theorem highBlock1 : (List.finRange 16).all (fun a => highCheck (actor 1 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
