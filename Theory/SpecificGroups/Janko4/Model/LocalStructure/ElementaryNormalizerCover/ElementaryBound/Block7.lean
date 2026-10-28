module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock7 : (List.finRange 16).all (fun a => pointCheck (actor 7 a)) = true := by decide +kernel

theorem rowBlock7 : (List.finRange 16).all (fun a => rowCheck (actor 7 a)) = true := by decide +kernel

theorem fixedBlock7 : (List.finRange 16).all (fun a => fastFixedCheck (actor 7 a)) = true := by decide +kernel

theorem codeBlock7 : (List.finRange 16).all (fun a => codeCheck (actor 7 a)) = true := by decide +kernel

theorem compatibleBlock7 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 7 a) w)) = true := by decide +kernel

theorem coverageBlock7 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (7,b,c))) = true := by decide +kernel

theorem lowBlock7 : (List.finRange 16).all (fun a => lowCheck (actor 7 a)) = true := by decide +kernel

theorem highBlock7 : (List.finRange 16).all (fun a => highCheck (actor 7 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
