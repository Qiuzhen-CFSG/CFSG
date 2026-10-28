module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Tests

/-! Kernel checks for one block of sixteen native square-one vertices. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
theorem pointBlock9 : (List.finRange 16).all (fun a => pointCheck (actor 9 a)) = true := by decide +kernel

theorem rowBlock9 : (List.finRange 16).all (fun a => rowCheck (actor 9 a)) = true := by decide +kernel

theorem fixedBlock9 : (List.finRange 16).all (fun a => fastFixedCheck (actor 9 a)) = true := by decide +kernel

theorem codeBlock9 : (List.finRange 16).all (fun a => codeCheck (actor 9 a)) = true := by decide +kernel

theorem compatibleBlock9 : (List.finRange 16).all (fun a => (List.finRange 192).all (fun w => compatibleCheck (actor 9 a) w)) = true := by decide +kernel

theorem coverageBlock9 : (List.finRange 8).all (fun b => (List.finRange 8).all (fun c => coverageCheck (9,b,c))) = true := by decide +kernel

theorem lowBlock9 : (List.finRange 16).all (fun a => lowCheck (actor 9 a)) = true := by decide +kernel

theorem highBlock9 : (List.finRange 16).all (fun a => highCheck (actor 9 a)) = true := by decide +kernel

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
