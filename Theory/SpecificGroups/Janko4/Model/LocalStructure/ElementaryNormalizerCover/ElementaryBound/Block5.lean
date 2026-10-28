module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock5 : (List.finRange 16).all (fun a => pointCheck (actor 5 a)) = true := by decide +kernel

theorem rowBlock5 : (List.finRange 16).all (fun a => rowCheck (actor 5 a)) = true := by decide +kernel

theorem fixedBlock5 : (List.finRange 16).all (fun a => fastFixedCheck (actor 5 a)) = true := by decide +kernel

theorem codeBlock5 : (List.finRange 16).all (fun a => codeCheck (actor 5 a)) = true := by decide +kernel

theorem compatibleBlock5 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 5 a) w)) = true := by decide +kernel

theorem coverageBlock5 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (5,b,c))) = true := by decide +kernel

theorem lowBlock5 : (List.finRange 16).all (fun a => lowCheck (actor 5 a)) = true := by decide +kernel

theorem highBlock5 : (List.finRange 16).all (fun a => highCheck (actor 5 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
