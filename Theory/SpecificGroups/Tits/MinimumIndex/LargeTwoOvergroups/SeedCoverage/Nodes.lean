module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Arithmetic

/-!
# Intermediate nodes for binary descent in the marked Tits Sylow subgroup

These are closures of explicit normal-form generators. The five levels have
1, 3, 7, 22, and 60 candidate nodes. Level five uses the original published
seed rows verbatim. No order or coverage assertion is part of these definitions.

Source: Parrott (1972), §5, p.683; untrusted discovery is saved in `source/`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
open Theory.GroupTheory.SubgroupEnumeration

def indices0 : Fin 1 → List (Fin 2048) :=
  ![[4, 1860]]

def indices1 : Fin 3 → List (Fin 2048) :=
  ![[1, 865, 1860],
    [1, 1864],
    [4, 877]]

def indices2 : Fin 7 → List (Fin 2048) :=
  ![[1, 82, 165, 1860],
    [1, 528, 865],
    [4, 165, 528],
    [83, 529, 864, 1860],
    [83, 865, 1860],
    [601, 1864],
    [864, 1861]]

def indices3 : Fin 22 → List (Fin 2048) :=
  ![[1, 4, 528],
    [1, 4, 756],
    [1, 82, 165, 528, 707],
    [1, 82, 1860],
    [1, 165, 727],
    [1, 165, 1821],
    [1, 165, 1860],
    [4, 165, 211],
    [81, 83, 434, 1860],
    [82, 164, 706, 1860],
    [82, 164, 1861],
    [83, 164, 1860],
    [83, 165, 529, 1860],
    [83, 165, 1861],
    [83, 528, 865],
    [83, 529, 864],
    [83, 529, 865],
    [83, 1864],
    [90, 529, 864, 1860],
    [529, 819, 1860],
    [865, 1821],
    [865, 1861]]

def indices4 : Fin 60 → List (Fin 2048) :=
  ![[1, 4, 81, 211],
    [1, 82, 165, 528],
    [1, 82, 528, 707],
    [1, 82, 727],
    [1, 165, 578, 707],
    [1, 252, 1860],
    [1, 578, 1860],
    [1, 578, 1977],
    [1, 1821],
    [1, 2027],
    [2, 434, 1822],
    [2, 434, 1860],
    [4, 81, 165],
    [4, 529],
    [4, 756],
    [16, 160, 528],
    [16, 727, 756],
    [81, 82, 164, 1860],
    [81, 83, 90, 757, 1860],
    [81, 90, 128, 434, 1860],
    [81, 90, 481, 1860],
    [81, 90, 819, 1860],
    [81, 253, 578, 706, 1860],
    [81, 434, 1820],
    [81, 528, 865],
    [82, 165, 529, 707],
    [83, 90, 211, 864],
    [83, 164, 528, 707],
    [83, 164, 529, 706],
    [83, 165, 528, 707],
    [83, 165, 529, 706],
    [83, 165, 529, 707],
    [83, 165, 1860],
    [83, 211, 865],
    [83, 434, 1822],
    [83, 434, 1860],
    [83, 529, 1860],
    [83, 1861],
    [90, 165, 529, 1860],
    [90, 529, 819],
    [128, 1864],
    [164, 656, 1860],
    [164, 706, 1821],
    [164, 706, 1860],
    [164, 1820],
    [164, 1861],
    [165, 578, 1860],
    [165, 727],
    [165, 1821],
    [165, 1861],
    [252, 579, 1860],
    [253, 529, 1860],
    [253, 578, 1820],
    [253, 578, 1861],
    [529, 826, 1860],
    [529, 864, 1860],
    [578, 865],
    [579, 819],
    [587, 826, 1860],
    [587, 864, 1860]]

abbrev nodeCount : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 7
  | 3 => 22
  | 4 => 60
  | _ + 5 => 122

def nodeIndices : (l : Nat) → Fin (nodeCount l) → List (Fin 2048)
  | 0 => indices0
  | 1 => indices1
  | 2 => indices2
  | 3 => indices3
  | 4 => indices4
  | _ + 5 => seedIndices

def generator (l : Nat) (i : Fin (nodeCount l)) :
    Fin (nodeIndices l i).length → S := fun k => element ((nodeIndices l i)[k])

def fastGenerator (l : Nat) (i : Fin (nodeCount l)) :
    Fin (nodeIndices l i).length → Equiv.Perm (Fin 1600) :=
  fun k => perm ((nodeIndices l i)[k])

theorem pointHom_generator (l : Nat) (i : Fin (nodeCount l))
    (k : Fin (nodeIndices l i).length) :
    pointHom (generator l i k) = fastGenerator l i k := pointHom_element _

def node (l : Nat) (i : Fin (nodeCount l)) : Subgroup S :=
  Subgroup.closure (Set.range (generator l i))

end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
end
