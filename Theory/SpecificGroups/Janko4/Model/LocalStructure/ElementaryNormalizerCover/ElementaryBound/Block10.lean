module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock10 : (List.finRange 16).all (fun a => pointCheck (actor 10 a)) = true := by decide +kernel

theorem rowBlock10 : (List.finRange 16).all (fun a => rowCheck (actor 10 a)) = true := by decide +kernel

theorem fixedBlock10 : (List.finRange 16).all (fun a => fastFixedCheck (actor 10 a)) = true := by decide +kernel

theorem codeBlock10 : (List.finRange 16).all (fun a => codeCheck (actor 10 a)) = true := by decide +kernel

theorem compatibleBlock10 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 10 a) w)) = true := by decide +kernel

theorem coverageBlock10 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (10,b,c))) = true := by decide +kernel

theorem lowBlock10 : (List.finRange 16).all (fun a => lowCheck (actor 10 a)) = true := by decide +kernel

theorem highBlock10 : (List.finRange 16).all (fun a => highCheck (actor 10 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
