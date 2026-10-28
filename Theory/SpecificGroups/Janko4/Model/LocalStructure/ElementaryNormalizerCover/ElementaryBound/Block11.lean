module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock11 : (List.finRange 16).all (fun a => pointCheck (actor 11 a)) = true := by decide +kernel

theorem rowBlock11 : (List.finRange 16).all (fun a => rowCheck (actor 11 a)) = true := by decide +kernel

theorem fixedBlock11 : (List.finRange 16).all (fun a => fastFixedCheck (actor 11 a)) = true := by decide +kernel

theorem codeBlock11 : (List.finRange 16).all (fun a => codeCheck (actor 11 a)) = true := by decide +kernel

theorem compatibleBlock11 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 11 a) w)) = true := by decide +kernel

theorem coverageBlock11 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (11,b,c))) = true := by decide +kernel

theorem lowBlock11 : (List.finRange 16).all (fun a => lowCheck (actor 11 a)) = true := by decide +kernel

theorem highBlock11 : (List.finRange 16).all (fun a => highCheck (actor 11 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
