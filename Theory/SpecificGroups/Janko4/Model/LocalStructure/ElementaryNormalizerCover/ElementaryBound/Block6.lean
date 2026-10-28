module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock6 : (List.finRange 16).all (fun a => pointCheck (actor 6 a)) = true := by decide +kernel

theorem rowBlock6 : (List.finRange 16).all (fun a => rowCheck (actor 6 a)) = true := by decide +kernel

theorem fixedBlock6 : (List.finRange 16).all (fun a => fastFixedCheck (actor 6 a)) = true := by decide +kernel

theorem codeBlock6 : (List.finRange 16).all (fun a => codeCheck (actor 6 a)) = true := by decide +kernel

theorem compatibleBlock6 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 6 a) w)) = true := by decide +kernel

theorem coverageBlock6 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (6,b,c))) = true := by decide +kernel

theorem lowBlock6 : (List.finRange 16).all (fun a => lowCheck (actor 6 a)) = true := by decide +kernel

theorem highBlock6 : (List.finRange 16).all (fun a => highCheck (actor 6 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
