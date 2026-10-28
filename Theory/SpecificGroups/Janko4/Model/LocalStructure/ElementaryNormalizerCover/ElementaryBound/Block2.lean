module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock2 : (List.finRange 16).all (fun a => pointCheck (actor 2 a)) = true := by decide +kernel

theorem rowBlock2 : (List.finRange 16).all (fun a => rowCheck (actor 2 a)) = true := by decide +kernel

theorem fixedBlock2 : (List.finRange 16).all (fun a => fastFixedCheck (actor 2 a)) = true := by decide +kernel

theorem codeBlock2 : (List.finRange 16).all (fun a => codeCheck (actor 2 a)) = true := by decide +kernel

theorem compatibleBlock2 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 2 a) w)) = true := by decide +kernel

theorem coverageBlock2 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (2,b,c))) = true := by decide +kernel

theorem coverageBlock14 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (14,b,c))) = true := by decide +kernel

theorem lowBlock2 : (List.finRange 16).all (fun a => lowCheck (actor 2 a)) = true := by decide +kernel

theorem highBlock2 : (List.finRange 16).all (fun a => highCheck (actor 2 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
