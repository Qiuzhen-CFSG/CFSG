module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock0 : (List.finRange 16).all (fun a => pointCheck (actor 0 a)) = true := by decide +kernel

theorem rowBlock0 : (List.finRange 16).all (fun a => rowCheck (actor 0 a)) = true := by decide +kernel

theorem fixedBlock0 : (List.finRange 16).all (fun a => fastFixedCheck (actor 0 a)) = true := by decide +kernel

theorem codeBlock0 : (List.finRange 16).all (fun a => codeCheck (actor 0 a)) = true := by decide +kernel

theorem compatibleBlock0 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 0 a) w)) = true := by decide +kernel

theorem coverageBlock0 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (0,b,c))) = true := by decide +kernel

theorem coverageBlock12 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (12,b,c))) = true := by decide +kernel

theorem lowBlock0 : (List.finRange 16).all (fun a => lowCheck (actor 0 a)) = true := by decide +kernel

theorem highBlock0 : (List.finRange 16).all (fun a => highCheck (actor 0 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
