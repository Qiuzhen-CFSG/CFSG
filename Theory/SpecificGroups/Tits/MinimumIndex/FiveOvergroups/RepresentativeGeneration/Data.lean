module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.Representatives
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.RepresentativeGeneration.Packed

/-!
# Short recovery words for the five-overgroup representatives

The first family uses the ordered generators `v,u,r*v/r,r*u/r`; the second
uses the two literal max4 generators and the representative. A signed letter
is stored as an index and a Boolean (true means positive). Row 5 of max8
recovers the two max4 generators conjugated by `exceptionalConjugator`.
All other max8 rows and all nonzero max4 rows recover the standard Atlas pair.

The words were discovered by a bidirectional search on the certified
three-point base. They are witnesses only; `Certificates.lean` checks their
actual values in the kernel. Source and regeneration are in `source/`.
-/

@[expose] public section
namespace Tits.MinimumIndexFiveOvergroups.RepresentativeGeneration
open Subgroup FiveFrobenius MinimumIndexCandidates

def eval {n : Nat} {G : Type*} [Group G] (a : Fin n → G)
    (w : List (Fin n × Bool)) : G :=
  (w.map fun k => if k.2 then a k.1 else (a k.1)⁻¹).prod

theorem map_eval {n : Nat} {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a : Fin n → G) (w : List (Fin n × Bool)) :
    f (eval a w) = eval (fun k => f (a k)) w := by
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨k, b⟩ _
  cases b <;> simp

def standard : Fin 2 → Atlas1600Group :=
  ![⟨atlas1600A, atlas1600A_mem⟩, ⟨atlas1600B, atlas1600B_mem⟩]

def pairInput {G : Type*} [Group G] (v u r : G) : Fin 4 → G :=
  ![v, u, r * v * r⁻¹, r * u * r⁻¹]

def pair (i : Fin 25) : Fin 4 → Atlas1600Group := pairInput v u (max8Rep i)

def extension (i : Fin 7) : Fin 3 → Atlas1600Group :=
  ![max4Generators.1, max4Generators.2, max4Rep i]

def conjugatorWord : List (Fin 2 × Bool) :=
  [(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true)]

def exceptionalConjugator : Atlas1600Group := eval standard conjugatorWord

def recovery8 : Fin 24 → Fin 2 → List (Fin 4 × Bool) :=
  ![![[(2, false), (0, false), (2, false), (1, true), (2, true), (1, true), (3, false), (2, true), (0, true), (3, false)],
      [(0, true), (3, true), (0, false), (1, true), (2, true), (1, false), (0, true), (3, false), (0, true)]],
    ![[(0, false), (3, true), (1, true), (1, true), (2, true), (1, true), (3, false), (2, true), (0, true), (3, true), (0, true)],
      [(2, false), (2, false), (0, true), (1, true), (2, true), (0, true), (2, false), (3, true)]],
    ![[(2, true), (0, true), (3, false), (1, true), (3, false), (2, true), (1, false), (3, false), (2, false), (1, true), (2, true)],
      [(3, false), (0, true), (3, true), (3, true), (0, true), (3, false), (0, true), (2, true), (0, true)]],
    ![[(1, true), (2, true), (1, false), (3, true), (1, false), (0, false), (3, true), (0, true), (3, true), (2, true), (0, false)],
      [(0, false), (2, true), (0, false), (2, false), (3, false), (1, true), (2, true), (1, false), (3, true), (1, true), (0, true)]],
    ![[(2, false), (1, false), (0, true), (3, false), (3, false), (0, false)],
      [(0, false), (0, false), (3, true), (1, false), (2, false), (0, true)]],
    ![[(2, true), (1, false), (2, true), (1, false), (3, false), (1, false), (0, true), (2, true), (1, true), (1, true), (2, true)],
      [(0, false), (1, true), (3, true), (0, true), (2, false), (0, false), (2, false), (3, true), (0, true), (2, true)]],
    ![[(0, false), (2, false), (0, false), (0, false), (2, false), (3, false), (0, false), (0, false), (3, false), (0, true)],
      [(1, false), (2, true), (2, true), (0, true), (2, false), (3, true), (0, false), (2, true), (1, true), (1, true)]],
    ![[(2, false), (0, false), (1, true), (2, false), (2, false), (3, true), (3, true), (0, false), (1, true), (3, false)],
      [(1, false), (2, true), (0, false), (1, false), (3, false), (1, true), (2, true), (2, true), (0, true)]],
    ![[(3, true), (0, false), (3, false), (1, true), (3, false), (2, true), (1, false), (3, true), (3, true), (2, true), (0, true)],
      [(2, false), (0, true), (3, true), (3, true), (1, true), (0, true), (2, true), (0, true), (0, true)]],
    ![[(0, false), (2, false), (3, true), (0, false), (0, false), (1, true), (1, true), (2, false), (3, true), (1, false)],
      [(1, false), (3, false), (0, true), (2, true), (1, false), (1, false), (2, false), (0, true), (3, false), (2, true)]],
    ![[(2, false), (0, true), (2, true), (0, true), (3, false), (1, true), (2, false), (0, true), (2, true), (1, true), (2, true)],
      [(0, false), (3, true), (1, false), (2, false), (3, false), (2, false), (0, true), (3, true), (3, true), (1, true), (0, true)]],
    ![[(0, true), (3, false), (0, false), (3, false), (0, false), (2, true), (1, true), (3, false), (0, false), (2, false)],
      [(1, false), (1, false), (3, true), (1, true), (1, true), (2, true), (0, true), (3, false), (1, false), (2, false)]],
    ![[(0, true), (2, true), (1, true), (3, true), (1, true), (1, true), (3, false), (2, false), (1, true), (2, false), (3, true)],
      [(2, false), (2, false), (1, false), (2, false), (0, false), (2, false), (2, false), (1, true), (0, true), (3, false)]],
    ![[(2, false), (1, true), (2, false), (2, false), (3, false), (1, false), (3, true), (1, false), (0, true), (3, false)],
      [(3, true), (0, false), (2, true), (0, false), (0, false), (2, false), (3, true), (0, false), (2, false), (0, false)]],
    ![[(0, true), (2, true), (2, true), (0, false), (3, true), (1, false), (1, false), (2, true), (1, false), (3, true), (3, true)],
      [(1, true), (2, false), (2, false), (1, true), (2, false), (3, true), (1, false), (0, true), (3, false), (1, false)]],
    ![[(2, false), (0, false), (1, true), (2, true), (1, true), (2, false), (3, true), (1, false), (1, false), (3, false)],
      [(0, false), (3, true), (0, true), (2, false), (0, true), (2, true), (2, true), (1, false), (3, false), (2, true)]],
    ![[(0, false), (3, true), (3, true), (0, true), (3, true), (1, false), (0, false), (2, true), (2, true), (1, true)],
      [(1, true), (2, false), (0, false), (3, true), (3, true), (0, false), (1, true), (3, false)]],
    ![[(2, false), (0, true), (2, false), (0, false), (2, false), (3, true), (0, true), (2, false), (0, false), (3, true)],
      [(1, false), (2, false), (3, true), (0, true), (3, false), (0, false), (3, true), (0, true), (3, false), (0, false)]],
    ![[(2, true), (0, false), (3, false), (3, false), (2, true), (1, false), (3, true), (2, true), (1, true)],
      [(1, false), (3, false), (1, false), (2, true), (3, true), (1, true), (3, false), (1, true), (0, true), (3, true), (0, true)]],
    ![[(2, true), (0, false), (3, false), (0, true), (3, false), (2, false), (2, false), (0, true), (0, true)],
      [(1, false), (2, false), (0, true), (2, true), (1, false), (0, true), (2, true), (0, true), (2, false)]],
    ![[(0, false), (2, true), (0, true), (0, true), (2, true), (3, true), (1, false), (0, true), (3, false), (1, false)],
      [(0, false), (3, false), (1, false), (2, false), (0, false), (2, true), (1, true), (2, false), (2, false), (1, true)]],
    ![[(3, true), (1, false), (2, true), (3, true), (1, false), (2, false), (0, false), (2, true), (1, true), (3, false), (1, true)],
      [(3, false), (0, true), (2, false), (1, false), (3, false), (2, true), (0, false), (2, true), (0, false)]],
    ![[(3, true), (1, true), (2, false), (3, false), (0, true), (2, false), (1, false), (0, true), (3, false)],
      [(3, true), (3, true), (0, true), (1, true), (3, true), (2, true), (2, true), (0, true)]],
    ![[(3, true), (0, true), (2, true), (0, true), (0, true), (3, false), (1, false), (0, true), (0, true), (2, true), (0, true)],
      [(1, false), (2, true), (0, true), (3, false), (3, false), (1, false), (2, true), (2, true), (1, true), (2, false)]]]

def recovery4 : Fin 6 → Fin 2 → List (Fin 3 × Bool) :=
  ![![[(1, false), (1, false), (0, false), (1, true), (2, false), (1, true), (0, false), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (2, true), (1, true), (0, true), (1, true)],
      [(2, false), (0, false), (1, true), (0, false), (1, false), (2, false), (0, false), (2, false), (1, true), (2, true), (1, true), (1, true), (0, true), (1, true), (0, true), (2, true), (0, true)]],
    ![[(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (2, false), (0, false), (2, true), (1, false), (2, true), (1, false), (2, true), (1, false), (2, true), (0, true), (1, false)],
      [(1, false), (2, false), (0, false), (2, false), (0, false), (1, true), (0, false), (1, false), (0, true), (2, true), (1, true), (2, true), (0, true), (1, true), (1, true)]],
    ![[(0, false), (2, false), (0, false), (2, true), (0, true), (2, false)],
      [(1, true), (2, false), (1, true), (0, false), (1, true), (0, false), (2, true), (0, true), (2, false), (1, true), (2, false), (0, true), (1, false)]],
    ![[(1, true), (0, false), (1, true), (2, false), (1, false), (0, false), (2, false), (1, true), (0, true), (2, true), (1, true), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true)],
      [(2, false), (1, false), (2, false), (0, false), (2, false), (0, false), (2, false), (1, true), (2, true), (0, true), (1, false), (0, true), (2, true), (1, true), (0, true)]],
    ![[(1, false), (2, false), (1, true), (2, false), (0, false), (1, false), (2, true), (1, false), (2, false), (1, false), (2, false), (1, false), (2, false), (2, false)],
      [(1, true), (2, false), (0, false), (2, false), (0, false), (1, true), (2, false), (1, false), (2, false), (2, false), (0, true), (2, false)]],
    ![[(1, true), (0, false), (2, true), (1, false), (0, false), (1, false), (2, false), (2, false), (1, false), (2, true), (1, true)],
      [(1, true), (2, false), (0, false), (1, false), (0, false), (2, true), (1, true), (2, true), (1, false), (0, true), (2, true), (1, true), (1, true)]]]

def target8 (i : Fin 24) (j : Fin 2) : Atlas1600Group :=
  if i = 4 then
    exceptionalConjugator * (![max4Generators.1, max4Generators.2] j) *
      exceptionalConjugator⁻¹
  else standard j

end Tits.MinimumIndexFiveOvergroups.RepresentativeGeneration
end
