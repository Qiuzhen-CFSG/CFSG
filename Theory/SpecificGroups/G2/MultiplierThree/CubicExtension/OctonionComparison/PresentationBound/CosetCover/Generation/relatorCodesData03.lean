module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.DataBase

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

def relatorCodes3072 : Nat → Nat :=
  (lookup 3092 (lookup 3082 (lookup 3077 (lookup 3074 (lookup 3073 (fun _ => 269632) (fun _ => 269696)) (lookup 3075 (fun _ => 269760) (lookup 3076 (fun _ => 269954) (fun _ => 270017)))) (lookup 3079 (lookup 3078 (fun _ => 270212) (fun _ => 270336)) (lookup 3080 (fun _ => 270722) (lookup 3081 (fun _ => 271104) (fun _ => 271168))))) (lookup 3087 (lookup 3084 (lookup 3083 (fun _ => 271811) (fun _ => 271872)) (lookup 3085 (fun _ => 272064) (lookup 3086 (fun _ => 272256) (fun _ => 272640)))) (lookup 3089 (lookup 3088 (fun _ => 272832) (fun _ => 273408)) (lookup 3090 (fun _ => 273600) (lookup 3091 (fun _ => 273793) (fun _ => 273991)))))) (lookup 3102 (lookup 3097 (lookup 3094 (lookup 3093 (fun _ => 274114) (fun _ => 274120)) (lookup 3095 (fun _ => 274176) (lookup 3096 (fun _ => 274368) (fun _ => 274944)))) (lookup 3099 (lookup 3098 (fun _ => 275072) (fun _ => 275136)) (lookup 3100 (fun _ => 275584) (lookup 3101 (fun _ => 275660) (fun _ => 275712))))) (lookup 3107 (lookup 3104 (lookup 3103 (fun _ => 276480) (fun _ => 277248)) (lookup 3105 (fun _ => 277504) (lookup 3106 (fun _ => 277568) (fun _ => 278016)))) (lookup 3110 (lookup 3108 (fun _ => 278208) (lookup 3109 (fun _ => 278784) (fun _ => 278976))) (lookup 3111 (fun _ => 279378) (lookup 3112 (fun _ => 279552) (fun _ => 279680)))))))

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
