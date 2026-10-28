module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Tactic.FinCases
/-!
# A finite conjugacy certificate in the tetrad stabilizer

The sixty rows encode the linear factor of the pointwise tetrad stabilizer.
Three-bit entries are packed into natural numbers to keep kernel reduction
small. `PointStabilizer` proves that these rows are actual hexacode
symmetries and exhaust that factor. `certificate` checks conjugation of
all fixed-point-free involutions in the marked-swap coset to one of two
representatives, using only the 960 affine parameters.

The coordinate conventions and local letter maps are those of the
attributed ATLAS ports `Codes.HexacodeGenerators` and
`Mathieu.TetradPointwiseStabilizer`. The table is a checked computation,
not an additional group-theoretic assumption. This supports the Mathieu
input to the Leech fusion calculation in Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, pp.283–284.
-/

@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.MathieuInvolutions
def forward (k : Fin 60) (i : Fin 6) : Fin 6 :=
  ⟨((2114563659023521757360967146413297133146113982192843866782116398076509391531677704319877461872203175712561123820128947430047464346345656177160349332805863043066831698104836187744389332940693598953681872643666309996631986662423778062172243481917075687573200998809406135892130528602452801616013778991225013147844298807571564168 >>> (3 * (6*k.val+i.val))) % 8) % 6, Nat.mod_lt _ (by decide)⟩
def backward (k : Fin 60) (i : Fin 6) : Fin 6 :=
  ⟨((2114558855952307701961162993990232045563774623725908802972939705712751639337234619605997776591571900506837163505672509131902085473704334135757044794561678952822662919827027335813390387837394237933006534789199330943970125023043547941320990319566140734945974748501170586295022624431222971612503402780142118417004691686403786376 >>> (3 * (6*k.val+i.val))) % 8) % 6, Nat.mod_lt _ (by decide)⟩
def letters (k : Fin 60) (i : Fin 6) : Fin 6 :=
  ⟨((9122366131497425358747978843579526282736762310230795863463785691115094501998079613121989723028973380380421962594068238066662116194790048006937872231591613468190079370745105426173044812378232161895326777482343123244395068317084923210336189787952119137141007173156963438792956646664823459406081792676205828611860742091428593664 >>> (3 * (6*k.val+i.val))) % 8) % 6, Nat.mod_lt _ (by decide)⟩

def localRows : Fin 6 → Fin 4 → Fin 4 := ![![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,3,2,1],![0,2,3,1],![0,3,1,2]]
abbrev Point := Fin 6 × Fin 4
abbrev Index := Fin 4 × Fin 4 × Fin 60
def translationRows (u v : Fin 4) : Fin 6 → Fin 4 :=
  ![0,u,v,u ^^^ localRows 1 v,localRows 2 u ^^^ v,localRows 4 u ^^^ localRows 1 v]
def act (a : Index) (x : Point) : Point :=
  let i := forward a.2.2 x.1
  (i, localRows (letters a.2.2 i) x.2 ^^^ translationRows a.1 a.2.1 i)
def swap (x : Point) : Point := (x.1,x.2 ^^^ 2)
def norm (a : Index) (x : Point) : Point := swap (act a x)
def badIndex : Index := (0,0,2)
def witness (a : Index) : Bool × Index :=
  match a.1.val, a.2.1.val, a.2.2.val with
  | 0,0,0 => (false,0,0,0)
  | 0,0,2 => (true,0,0,0)
  | 0,0,20 => (true,0,0,27)
  | 0,0,25 => (true,0,0,20)
  | 0,0,47 => (true,0,0,25)
  | 0,0,50 => (true,0,0,21)
  | 0,1,0 => (false,0,0,1)
  | 0,1,2 => (true,0,0,1)
  | 0,1,12 => (true,0,0,22)
  | 0,1,31 => (true,0,0,26)
  | 0,1,38 => (true,0,0,23)
  | 0,1,53 => (true,0,0,24)
  | 0,2,2 => (true,1,0,0)
  | 0,2,34 => (true,1,0,33)
  | 0,2,59 => (true,1,0,34)
  | 0,3,2 => (true,1,0,1)
  | 0,3,16 => (true,1,0,35)
  | 0,3,41 => (true,1,0,32)
  | 1,0,1 => (true,1,0,9)
  | 1,0,12 => (true,1,0,31)
  | 1,0,25 => (true,1,0,28)
  | 1,1,0 => (false,0,0,8)
  | 1,1,1 => (true,0,0,8)
  | 1,1,16 => (true,0,0,35)
  | 1,1,34 => (true,0,0,33)
  | 1,1,47 => (true,0,0,13)
  | 1,1,53 => (true,0,0,12)
  | 1,2,1 => (true,1,0,8)
  | 1,2,38 => (true,1,0,30)
  | 1,2,50 => (true,1,0,29)
  | 1,3,0 => (false,0,0,9)
  | 1,3,1 => (true,0,0,9)
  | 1,3,20 => (true,0,0,14)
  | 1,3,31 => (true,0,0,15)
  | 1,3,41 => (true,0,0,32)
  | 1,3,59 => (true,0,0,34)
  | 2,0,25 => (true,1,0,20)
  | 2,0,31 => (true,1,0,15)
  | 2,0,34 => (true,1,0,17)
  | 2,1,50 => (true,1,0,21)
  | 2,1,53 => (true,1,0,12)
  | 2,1,59 => (true,1,0,19)
  | 2,2,12 => (true,1,0,22)
  | 2,2,16 => (true,1,0,18)
  | 2,2,20 => (true,1,0,14)
  | 2,3,38 => (true,1,0,23)
  | 2,3,41 => (true,1,0,16)
  | 2,3,47 => (true,1,0,13)
  | 3,0,0 => (false,0,0,5)
  | 3,0,3 => (true,0,0,5)
  | 3,0,16 => (true,0,0,18)
  | 3,0,25 => (true,0,0,28)
  | 3,0,38 => (true,0,0,30)
  | 3,0,59 => (true,0,0,19)
  | 3,1,3 => (true,1,0,5)
  | 3,1,20 => (true,1,0,27)
  | 3,1,53 => (true,1,0,24)
  | 3,2,3 => (true,1,0,4)
  | 3,2,31 => (true,1,0,26)
  | 3,2,47 => (true,1,0,25)
  | 3,3,0 => (false,0,0,4)
  | 3,3,3 => (true,0,0,4)
  | 3,3,12 => (true,0,0,31)
  | 3,3,34 => (true,0,0,17)
  | 3,3,41 => (true,0,0,16)
  | 3,3,50 => (true,0,0,29)
  | _,_,_ => (false,0,0,0)
theorem certificate : ∀ a : Index,
    (∀ x, norm a (norm a x) = x) → (∀ x, norm a x ≠ x) →
    ∀ x, act (witness a).2 (norm a x) =
      (if (witness a).1 then norm badIndex else swap) (act (witness a).2 x) := by
  rintro ⟨u,v,j⟩
  revert j
  fin_cases u <;> fin_cases v <;> decide +kernel

theorem left_inv : ∀ k i, backward k (forward k i) = i := by intro k; fin_cases k <;> decide
theorem right_inv : ∀ k i, forward k (backward k i) = i := by intro k; fin_cases k <;> decide
theorem forward_injective : ∀ i j, (∀ k, forward i k = forward j k) → i = j := by intro k; fin_cases k <;> decide

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.MathieuInvolutions
