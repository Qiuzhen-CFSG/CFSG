module
import Stellmacher.SectionsOneToFourDefs
#check Matrix.SpecialLinearGroup
example : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by infer_instance
example : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by infer_instance
