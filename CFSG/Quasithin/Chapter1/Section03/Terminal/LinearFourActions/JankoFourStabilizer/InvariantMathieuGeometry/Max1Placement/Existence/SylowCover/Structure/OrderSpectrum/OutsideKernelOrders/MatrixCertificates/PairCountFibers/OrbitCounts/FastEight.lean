module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Tables8.Definitions

/-!
# Evaluating the same row-eight conjugation maps with literal lists

The original vector of eight images is compared with a literal list, for all
21 generators. Folding that list gives exactly the existing coordinate action.
This avoids repeated vector-index reductions in finite plane checking; the
conjugation equations and canonical-step proposition are unchanged.
Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
def orbitFastImages8 (j : Fin 21) : List (Fin 256) := (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [211,2,236,136,144,32,192,128] else [193,98,4,168,208,32,64,128]) else (if j.val < 3 then [17,18,36,8,16,224,64,128] else (if j.val < 4 then [33,130,100,8,144,32,64,128] else [1,130,4,72,16,32,64,128]))) else (if j.val < 7 then (if j.val < 6 then [163,130,4,8,16,160,192,128] else [1,2,196,8,16,32,64,128]) else (if j.val < 8 then [97,98,4,8,208,32,64,128] else (if j.val < 9 then [17,130,4,8,16,160,64,128] else [1,2,4,8,16,32,64,128])))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then [193,130,4,136,16,32,64,128] else [1,2,132,8,16,32,64,128]) else (if j.val < 13 then [97,2,4,8,144,32,64,128] else (if j.val < 14 then [65,130,4,8,16,32,64,128] else [1,2,4,8,16,32,64,128]))) else (if j.val < 18 then (if j.val < 16 then [1,2,4,8,16,32,64,128] else (if j.val < 17 then [1,2,4,8,16,32,64,128] else [1,2,4,8,16,32,64,128])) else (if j.val < 19 then [1,2,4,8,16,32,64,128] else (if j.val < 20 then [1,2,4,8,16,32,64,128] else [1,2,4,8,16,32,64,128])))))

theorem orbitImages8_list (j : Fin 21) :
    List.ofFn (orbitImages8 j) = orbitFastImages8 j :=
  (by decide +kernel : ∀ j : Fin 21, List.ofFn (orbitImages8 j) = orbitFastImages8 j) j

def orbitFastAction8 (j : Fin 21) (n : Fin 256) : Fin 256 :=
  orbitFold 8 (orbitFastImages8 j) n.val

theorem orbitAction8_eq_fast (j : Fin 21) (n : Fin 256) :
    orbitAction8 j n = orbitFastAction8 j n :=
  congrArg (fun l => orbitFold 8 l n.val) (orbitImages8_list j)

def orbitFastCanonical8 (a b : Fin 256) : Bool :=
  orbitCanonicalCheck 8 representativeLeft8 representativeRight8 orbitValues8
    orbitFastAction8 orbitWitness8 a b

theorem orbitCanonical8_eq_fast (a b : Fin 256) :
    orbitCanonical8 a b = orbitFastCanonical8 a b := by
  have he : orbitAction8 = orbitFastAction8 := funext fun j => funext fun n => orbitAction8_eq_fast j n
  exact congrArg (fun action => orbitCanonicalCheck 8 representativeLeft8 representativeRight8
    orbitValues8 action orbitWitness8 a b) he
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
