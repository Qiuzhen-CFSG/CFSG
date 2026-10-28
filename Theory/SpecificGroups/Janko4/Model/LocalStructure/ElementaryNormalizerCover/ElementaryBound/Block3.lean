module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock3 : (List.finRange 16).all (fun a => pointCheck (actor 3 a)) = true := by decide +kernel

theorem rowBlock3 : (List.finRange 16).all (fun a => rowCheck (actor 3 a)) = true := by decide +kernel

theorem fixedBlock3 : (List.finRange 16).all (fun a => fastFixedCheck (actor 3 a)) = true := by decide +kernel

theorem codeBlock3 : (List.finRange 16).all (fun a => codeCheck (actor 3 a)) = true := by decide +kernel

theorem compatibleBlock3 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 3 a) w)) = true := by decide +kernel

theorem coverageBlock3 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (3,b,c))) = true := by decide +kernel

theorem coverageBlock15 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (15,b,c))) = true := by decide +kernel

theorem lowBlock3 : (List.finRange 16).all (fun a => lowCheck (actor 3 a)) = true := by decide +kernel

theorem highBlock3 : (List.finRange 16).all (fun a => highCheck (actor 3 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
