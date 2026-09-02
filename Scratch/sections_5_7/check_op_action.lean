module
import Stellmacher.SectionFiveToSeven.Defs
open scoped Pointwise
#check (show MulOpposite.op (1 : ℤ) • ({1} : Set ℤ) = ({1} : Set ℤ) from by simp)
#check MulOpposite.smul_def
#check smul_set_eq_image
