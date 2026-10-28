module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock8 : (List.finRange 16).all (fun a => pointCheck (actor 8 a)) = true := by decide +kernel

theorem rowBlock8 : (List.finRange 16).all (fun a => rowCheck (actor 8 a)) = true := by decide +kernel

theorem fixedBlock8 : (List.finRange 16).all (fun a => fastFixedCheck (actor 8 a)) = true := by decide +kernel

theorem codeBlock8 : (List.finRange 16).all (fun a => codeCheck (actor 8 a)) = true := by decide +kernel

theorem compatibleBlock8 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 8 a) w)) = true := by decide +kernel

theorem coverageBlock8 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (8,b,c))) = true := by decide +kernel

theorem lowBlock8 : (List.finRange 16).all (fun a => lowCheck (actor 8 a)) = true := by decide +kernel

theorem highBlock8 : (List.finRange 16).all (fun a => highCheck (actor 8 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
