module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.Data
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
/-!
# A concrete lower bound for the marked Held M₁ image

The words in the three actual generators produce orbit lower bounds
136, 60, 40, 3 and 2 in successive point stabilizers at Lean points
261, 1651, 149, 4 and 25. All points lie in the 136-point orbit containing
Lean point 4. Each orbit tree has distinct vertices; each edge and each
child generator's stabilizer membership is checked by kernel reduction.
An injection from orbit representatives times the stabilizer into the group
then gives `136 * 60 * 40 * 3 * 2 = 1958400` as a lower bound.

The generators are exactly `a`, `a^(b²)` and `a^(b⁻²)`, with
`x^g = g⁻¹*x*g`. Inversion of the retained ATLAS permutations converts
GAP's right action to Lean's left action, preserving the order of words.
No faithfulness of the 136-point action, abstract presentation bound,
relator lifting or order assertion from GAP is needed.

Sources: John Bray's `Held/Model/Source/HeG1-P1.M` and the two retained
ATLAS `HeG1-p2058B0` permutations. The discovery words are in
`M1Restriction/source/lower_levels.json`; `LowerBound/source/generate.py`
reproduces the certificate tables and the checked word expressions.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
private theorem orbit_lower {G X : Type*} [Group G] [MulAction G X]
    [Finite G] {m : ℕ} (b : X) (point : Fin m → X)
    (hi : Function.Injective point)
    (hr : ∀ i, ∃ g : G, g • b = point i) :
    m * Nat.card (MulAction.stabilizer G b) ≤ Nat.card G := by
  classical
  choose rep hrep using hr
  have hinj : Function.Injective (fun z : Fin m × MulAction.stabilizer G b =>
      rep z.1 * z.2.val) := by
    rintro ⟨i, g⟩ ⟨j, h⟩ heq
    have hij : i = j := hi (by
      have he := congrArg (fun k : G => k • b) heq
      simpa only [mul_smul, MulAction.mem_stabilizer_iff.mp g.property,
        MulAction.mem_stabilizer_iff.mp h.property, hrep] using he)
    subst j
    have hgh : g = h := Subtype.ext (mul_left_cancel heq)
    subst h
    rfl
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective _ hinj

private theorem orbit_tree {G X : Type*} [Group G] [MulAction G X]
    {m r : ℕ} [NeZero m] (gen : Fin r → G) (b : X) (point : Fin m → X)
    (parent : Fin m → Fin m) (step : Fin m → Fin r) (depth : Fin m → ℕ)
    (root : Fin m) (hbase : point root = b)
    (hstep : ∀ i, i = root ∨ (depth (parent i) < depth i ∧
      gen (step i) • point (parent i) = point i)) :
    ∀ i, ∃ g : G, g • b = point i := by
  suffices h : ∀ n : ℕ, ∀ i, depth i = n → ∃ g : G, g • b = point i from
    fun i => h (depth i) i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hi
    rcases hstep i with rfl | ⟨hd, hs⟩
    · exact ⟨1, by simpa using hbase.symm⟩
    · obtain ⟨g, hg⟩ := ih (depth (parent i)) (by omega) (parent i) rfl
      exact ⟨gen (step i) * g, by rw [mul_smul, hg, hs]⟩



-- BEGIN GENERATED ORBIT CERTIFICATE
private abbrev S0 := ↥concreteSubgroup
private def gen0 (i : Fin 3) : S0 :=
  ⟨match i with
    | 0 => a
    | 1 => (b ^ 2)⁻¹ * a * b ^ 2
    | 2 => b ^ 2 * a * (b ^ 2)⁻¹, by
      have hm : concreteGenerator i ∈ concreteSubgroup :=
        Subgroup.subset_closure ⟨i, rfl⟩
      fin_cases i <;> simpa only [concreteGenerator_eq] using hm⟩
private def signedGen0 (i : Fin 6) : S0 :=
  (if i.val < 3 then (if i.val < 1 then gen0 0 else (if i.val < 2 then gen0 1 else gen0 2)) else (if i.val < 4 then (gen0 0)⁻¹ else (if i.val < 5 then (gen0 1)⁻¹ else (gen0 2)⁻¹)))

private def point0 (i : Fin 136) : Fin 2058 :=
  (if i.val < 68 then (if i.val < 34 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 6) else (if i.val < 3 then 25 else 29)) else (if i.val < 6 then (if i.val < 5 then 51 else 81) else (if i.val < 7 then 91 else 136))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 149 else 174) else (if i.val < 11 then 227 else 230)) else (if i.val < 14 then (if i.val < 13 then 237 else 260) else (if i.val < 15 then 261 else (if i.val < 16 then 268 else 275))))) else (if i.val < 25 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then 279 else 293) else (if i.val < 20 then 302 else 307)) else (if i.val < 23 then (if i.val < 22 then 339 else 365) else (if i.val < 24 then 377 else 388))) else (if i.val < 29 then (if i.val < 27 then (if i.val < 26 then 396 else 416) else (if i.val < 28 then 417 else 431)) else (if i.val < 31 then (if i.val < 30 then 439 else 453) else (if i.val < 32 then 473 else (if i.val < 33 then 476 else 505)))))) else (if i.val < 51 then (if i.val < 42 then (if i.val < 38 then (if i.val < 36 then (if i.val < 35 then 521 else 604) else (if i.val < 37 then 617 else 680)) else (if i.val < 40 then (if i.val < 39 then 720 else 726) else (if i.val < 41 then 776 else 786))) else (if i.val < 46 then (if i.val < 44 then (if i.val < 43 then 795 else 801) else (if i.val < 45 then 803 else 811)) else (if i.val < 48 then (if i.val < 47 then 827 else 833) else (if i.val < 49 then 837 else (if i.val < 50 then 839 else 874))))) else (if i.val < 59 then (if i.val < 55 then (if i.val < 53 then (if i.val < 52 then 914 else 923) else (if i.val < 54 then 960 else 984)) else (if i.val < 57 then (if i.val < 56 then 988 else 992) else (if i.val < 58 then 993 else 1008))) else (if i.val < 63 then (if i.val < 61 then (if i.val < 60 then 1018 else 1022) else (if i.val < 62 then 1024 else 1038)) else (if i.val < 65 then (if i.val < 64 then 1042 else 1069) else (if i.val < 66 then 1074 else (if i.val < 67 then 1081 else 1100))))))) else (if i.val < 102 then (if i.val < 85 then (if i.val < 76 then (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then 1109 else 1110) else (if i.val < 71 then 1150 else 1158)) else (if i.val < 74 then (if i.val < 73 then 1171 else 1203) else (if i.val < 75 then 1224 else 1259))) else (if i.val < 80 then (if i.val < 78 then (if i.val < 77 then 1282 else 1285) else (if i.val < 79 then 1287 else 1294)) else (if i.val < 82 then (if i.val < 81 then 1306 else 1335) else (if i.val < 83 then 1344 else (if i.val < 84 then 1367 else 1385))))) else (if i.val < 93 then (if i.val < 89 then (if i.val < 87 then (if i.val < 86 then 1406 else 1409) else (if i.val < 88 then 1418 else 1430)) else (if i.val < 91 then (if i.val < 90 then 1434 else 1441) else (if i.val < 92 then 1467 else 1477))) else (if i.val < 97 then (if i.val < 95 then (if i.val < 94 then 1486 else 1490) else (if i.val < 96 then 1492 else 1495)) else (if i.val < 99 then (if i.val < 98 then 1508 else 1540) else (if i.val < 100 then 1597 else (if i.val < 101 then 1607 else 1610)))))) else (if i.val < 119 then (if i.val < 110 then (if i.val < 106 then (if i.val < 104 then (if i.val < 103 then 1611 else 1617) else (if i.val < 105 then 1619 else 1645)) else (if i.val < 108 then (if i.val < 107 then 1651 else 1704) else (if i.val < 109 then 1714 else 1719))) else (if i.val < 114 then (if i.val < 112 then (if i.val < 111 then 1737 else 1742) else (if i.val < 113 then 1747 else 1765)) else (if i.val < 116 then (if i.val < 115 then 1812 else 1824) else (if i.val < 117 then 1826 else (if i.val < 118 then 1834 else 1839))))) else (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then (if i.val < 120 then 1843 else 1855) else (if i.val < 122 then 1865 else 1871)) else (if i.val < 125 then (if i.val < 124 then 1880 else 1888) else (if i.val < 126 then 1894 else 1905))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then 1917 else 1933) else (if i.val < 130 then 1967 else 1991)) else (if i.val < 133 then (if i.val < 132 then 2001 else 2002) else (if i.val < 134 then 2008 else (if i.val < 135 then 2020 else 2035))))))))

private def parent0 (i : Fin 136) : Fin 136 :=
  (if i.val < 68 then (if i.val < 34 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 70 else 80) else (if i.val < 3 then 92 else 16)) else (if i.val < 6 then (if i.val < 5 then 129 else 81) else (if i.val < 7 then 73 else 37))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 14 else 71) else (if i.val < 11 then 85 else 113)) else (if i.val < 14 then (if i.val < 13 then 63 else 35) else (if i.val < 15 then 14 else (if i.val < 16 then 65 else 68))))) else (if i.val < 25 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then 47 else 50) else (if i.val < 20 then 131 else 17)) else (if i.val < 23 then (if i.val < 22 then 132 else 15) else (if i.val < 24 then 31 else 49))) else (if i.val < 29 then (if i.val < 27 then (if i.val < 26 then 85 else 72) else (if i.val < 28 then 8 else 55)) else (if i.val < 31 then (if i.val < 30 then 92 else 40) else (if i.val < 32 then 107 else (if i.val < 33 then 23 else 77)))))) else (if i.val < 51 then (if i.val < 42 then (if i.val < 38 then (if i.val < 36 then (if i.val < 35 then 66 else 102) else (if i.val < 37 then 61 else 11)) else (if i.val < 40 then (if i.val < 39 then 90 else 84) else (if i.val < 41 then 106 else 20))) else (if i.val < 46 then (if i.val < 44 then (if i.val < 43 then 47 else 80) else (if i.val < 45 then 52 else 42)) else (if i.val < 48 then (if i.val < 47 then 13 else 93) else (if i.val < 49 then 87 else (if i.val < 50 then 31 else 133))))) else (if i.val < 59 then (if i.val < 55 then (if i.val < 53 then (if i.val < 52 then 119 else 104) else (if i.val < 54 then 70 else 4)) else (if i.val < 57 then (if i.val < 56 then 57 else 42) else (if i.val < 58 then 89 else 24))) else (if i.val < 63 then (if i.val < 61 then (if i.val < 60 then 37 else 21) else (if i.val < 62 then 132 else 64)) else (if i.val < 65 then (if i.val < 64 then 59 else 72) else (if i.val < 66 then 40 else (if i.val < 67 then 107 else 27))))))) else (if i.val < 102 then (if i.val < 85 then (if i.val < 76 then (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then 26 else 122) else (if i.val < 71 then 108 else 101)) else (if i.val < 74 then (if i.val < 73 then 101 else 133) else (if i.val < 75 then 13 else 96))) else (if i.val < 80 then (if i.val < 78 then (if i.val < 77 then 65 else 7) else (if i.val < 79 then 63 else 7)) else (if i.val < 82 then (if i.val < 81 then 94 else 78) else (if i.val < 83 then 54 else (if i.val < 84 then 109 else 52))))) else (if i.val < 93 then (if i.val < 89 then (if i.val < 87 then (if i.val < 86 then 8 else 29) else (if i.val < 88 then 100 else 22)) else (if i.val < 91 then (if i.val < 90 then 44 else 54) else (if i.val < 92 then 99 else 27))) else (if i.val < 97 then (if i.val < 95 then (if i.val < 94 then 109 else 123) else (if i.val < 96 then 81 else 93)) else (if i.val < 99 then (if i.val < 98 then 55 else 105) else (if i.val < 100 then 25 else (if i.val < 101 then 105 else 35)))))) else (if i.val < 119 then (if i.val < 110 then (if i.val < 106 then (if i.val < 104 then (if i.val < 103 then 113 else 84) else (if i.val < 105 then 119 else 74)) else (if i.val < 108 then (if i.val < 107 then 25 else 131) else (if i.val < 109 then 134 else 108))) else (if i.val < 114 then (if i.val < 112 then (if i.val < 111 then 111 else 112) else (if i.val < 113 then 15 else 10)) else (if i.val < 116 then (if i.val < 115 then 39 else 60) else (if i.val < 117 then 103 else (if i.val < 118 then 123 else 129))))) else (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then (if i.val < 120 then 67 else 128) else (if i.val < 122 then 10 else 89)) else (if i.val < 125 then (if i.val < 124 then 0 else 77) else (if i.val < 126 then 115 else 41))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then 30 else 53) else (if i.val < 130 then 76 else 21)) else (if i.val < 133 then (if i.val < 132 then 104 else 127) else (if i.val < 134 then 79 else (if i.val < 135 then 67 else 128))))))))

private def step0 (i : Fin 136) : Fin 6 :=
  (if i.val < 68 then (if i.val < 34 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 2 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 0 else (if i.val < 16 then 1 else 2))))) else (if i.val < 25 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then 2 else 2) else (if i.val < 20 then 2 else 0)) else (if i.val < 23 then (if i.val < 22 then 2 else 2) else (if i.val < 24 then 0 else 0))) else (if i.val < 29 then (if i.val < 27 then (if i.val < 26 then 2 else 1) else (if i.val < 28 then 2 else 0)) else (if i.val < 31 then (if i.val < 30 then 0 else 1) else (if i.val < 32 then 2 else (if i.val < 33 then 2 else 0)))))) else (if i.val < 51 then (if i.val < 42 then (if i.val < 38 then (if i.val < 36 then (if i.val < 35 then 2 else 1) else (if i.val < 37 then 2 else 2)) else (if i.val < 40 then (if i.val < 39 then 2 else 1) else (if i.val < 41 then 0 else 1))) else (if i.val < 46 then (if i.val < 44 then (if i.val < 43 then 0 else 2) else (if i.val < 45 then 0 else 1)) else (if i.val < 48 then (if i.val < 47 then 1 else 1) else (if i.val < 49 then 2 else (if i.val < 50 then 1 else 0))))) else (if i.val < 59 then (if i.val < 55 then (if i.val < 53 then (if i.val < 52 then 0 else 1) else (if i.val < 54 then 1 else 0)) else (if i.val < 57 then (if i.val < 56 then 2 else 2) else (if i.val < 58 then 1 else 2))) else (if i.val < 63 then (if i.val < 61 then (if i.val < 60 then 0 else 0) else (if i.val < 62 then 0 else 1)) else (if i.val < 65 then (if i.val < 64 then 1 else 0) else (if i.val < 66 then 2 else (if i.val < 67 then 0 else 0))))))) else (if i.val < 102 then (if i.val < 85 then (if i.val < 76 then (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then 0 else 2) else (if i.val < 71 then 2 else 1)) else (if i.val < 74 then (if i.val < 73 then 2 else 1) else (if i.val < 75 then 0 else 1))) else (if i.val < 80 then (if i.val < 78 then (if i.val < 77 then 0 else 2) else (if i.val < 79 then 2 else 0)) else (if i.val < 82 then (if i.val < 81 then 1 else 0) else (if i.val < 83 then 2 else (if i.val < 84 then 1 else 2))))) else (if i.val < 93 then (if i.val < 89 then (if i.val < 87 then (if i.val < 86 then 0 else 2) else (if i.val < 88 then 0 else 1)) else (if i.val < 91 then (if i.val < 90 then 2 else 1) else (if i.val < 92 then 2 else 1))) else (if i.val < 97 then (if i.val < 95 then (if i.val < 94 then 2 else 2) else (if i.val < 96 then 1 else 0)) else (if i.val < 99 then (if i.val < 98 then 1 else 0) else (if i.val < 100 then 0 else (if i.val < 101 then 2 else 0)))))) else (if i.val < 119 then (if i.val < 110 then (if i.val < 106 then (if i.val < 104 then (if i.val < 103 then 2 else 0) else (if i.val < 105 then 2 else 1)) else (if i.val < 108 then (if i.val < 107 then 1 else 1) else (if i.val < 109 then 1 else 0))) else (if i.val < 114 then (if i.val < 112 then (if i.val < 111 then 0 else 2) else (if i.val < 113 then 0 else 0)) else (if i.val < 116 then (if i.val < 115 then 0 else 1) else (if i.val < 117 then 1 else (if i.val < 118 then 0 else 0))))) else (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then (if i.val < 120 then 1 else 2) else (if i.val < 122 then 2 else 0)) else (if i.val < 125 then (if i.val < 124 then 1 else 1) else (if i.val < 126 then 2 else 0))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then 2 else 0) else (if i.val < 130 then 1 else 1)) else (if i.val < 133 then (if i.val < 132 then 0 else 1) else (if i.val < 134 then 2 else (if i.val < 135 then 2 else 1))))))))

private def depth0 (i : Fin 136) : ℕ :=
  (if i.val < 68 then (if i.val < 34 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 11) else (if i.val < 3 then 4 else 12)) else (if i.val < 6 then (if i.val < 5 then 9 else 11) else (if i.val < 7 then 11 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 9) else (if i.val < 11 then 3 else 5)) else (if i.val < 14 then (if i.val < 13 then 9 else 7) else (if i.val < 15 then 0 else (if i.val < 16 then 7 else 11))))) else (if i.val < 25 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then 9 else 11) else (if i.val < 20 then 7 else 10)) else (if i.val < 23 then (if i.val < 22 then 9 else 8) else (if i.val < 24 then 9 else 10))) else (if i.val < 29 then (if i.val < 27 then (if i.val < 26 then 3 else 9) else (if i.val < 28 then 2 else 11)) else (if i.val < 31 then (if i.val < 30 then 4 else 6) else (if i.val < 32 then 8 else (if i.val < 33 then 10 else 9)))))) else (if i.val < 51 then (if i.val < 42 then (if i.val < 38 then (if i.val < 36 then (if i.val < 35 then 9 else 6) else (if i.val < 37 then 10 else 6)) else (if i.val < 40 then (if i.val < 39 then 12 else 8) else (if i.val < 41 then 5 else 11))) else (if i.val < 46 then (if i.val < 44 then (if i.val < 43 then 9 else 11) else (if i.val < 45 then 7 else 10)) else (if i.val < 48 then (if i.val < 47 then 8 else 8) else (if i.val < 49 then 12 else (if i.val < 50 then 9 else 10))))) else (if i.val < 59 then (if i.val < 55 then (if i.val < 53 then (if i.val < 52 then 5 else 6) else (if i.val < 54 then 7 else 10)) else (if i.val < 57 then (if i.val < 56 then 10 else 10) else (if i.val < 58 then 9 else 11))) else (if i.val < 63 then (if i.val < 61 then (if i.val < 60 then 7 else 10) else (if i.val < 62 then 9 else 10)) else (if i.val < 65 then (if i.val < 64 then 8 else 9) else (if i.val < 66 then 6 else (if i.val < 67 then 8 else 3))))))) else (if i.val < 102 then (if i.val < 85 then (if i.val < 76 then (if i.val < 72 then (if i.val < 70 then (if i.val < 69 then 10 else 10) else (if i.val < 71 then 6 else 8)) else (if i.val < 74 then (if i.val < 73 then 8 else 10) else (if i.val < 75 then 8 else 9))) else (if i.val < 80 then (if i.val < 78 then (if i.val < 77 then 7 else 8) else (if i.val < 79 then 9 else 8)) else (if i.val < 82 then (if i.val < 81 then 10 else 10) else (if i.val < 83 then 11 else (if i.val < 84 then 7 else 7))))) else (if i.val < 93 then (if i.val < 89 then (if i.val < 87 then (if i.val < 86 then 2 else 5) else (if i.val < 88 then 11 else 9)) else (if i.val < 91 then (if i.val < 90 then 8 else 11) else (if i.val < 92 then 5 else 3))) else (if i.val < 97 then (if i.val < 95 then (if i.val < 94 then 7 else 9) else (if i.val < 96 then 11 else 8)) else (if i.val < 99 then (if i.val < 98 then 11 else 10) else (if i.val < 100 then 4 else (if i.val < 101 then 10 else 7)))))) else (if i.val < 119 then (if i.val < 110 then (if i.val < 106 then (if i.val < 104 then (if i.val < 103 then 5 else 8) else (if i.val < 105 then 5 else 9)) else (if i.val < 108 then (if i.val < 107 then 4 else 7) else (if i.val < 109 then 5 else 6))) else (if i.val < 114 then (if i.val < 112 then (if i.val < 111 then 10 else 9) else (if i.val < 113 then 8 else 4)) else (if i.val < 116 then (if i.val < 115 then 9 else 11) else (if i.val < 117 then 9 else (if i.val < 118 then 9 else 9))))) else (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then (if i.val < 120 then 4 else 9) else (if i.val < 122 then 4 else 9)) else (if i.val < 125 then (if i.val < 124 then 8 else 9) else (if i.val < 126 then 12 else 12))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then 7 else 8) else (if i.val < 130 then 8 else 10)) else (if i.val < 133 then (if i.val < 132 then 6 else 8) else (if i.val < 134 then 9 else (if i.val < 135 then 4 else 9))))))))

private theorem point0_injective : Function.Injective point0 := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem tree0_valid : ∀ i, i = 14 ∨
    (depth0 (parent0 i) < depth0 i ∧
      signedGen0 (step0 i) • point0 (parent0 i) = point0 i) := by
  decide +kernel
private theorem reach0 : ∀ i, ∃ g : S0, g • (261 : Fin 2058) = point0 i :=
  orbit_tree signedGen0 261 point0 parent0 step0 depth0 14
    (by decide +kernel) tree0_valid

private abbrev S1 := ↥(MulAction.stabilizer S0 (261 : Fin 2058))

private def rawGen1 (i : Fin 7) : S0 :=
  (if i.val < 3 then (if i.val < 1 then (gen0 0) else (if i.val < 2 then (gen0 2) else (gen0 1) * (gen0 2) * (gen0 0) * (gen0 2) * (gen0 0) * (gen0 2)⁻¹ * (gen0 1)⁻¹ * (gen0 0)⁻¹ * (gen0 1)⁻¹)) else (if i.val < 5 then (if i.val < 4 then (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) * (gen0 1) * (gen0 2)⁻¹ * (gen0 1)⁻¹ * (gen0 0)⁻¹ * (gen0 1)⁻¹ * (gen0 0) else (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) * (gen0 0) * (gen0 2)⁻¹ * (gen0 0)⁻¹ * (gen0 2)⁻¹ * (gen0 1)⁻¹ * (gen0 0)) else (if i.val < 6 then (gen0 1) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 2) * (gen0 2) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 0) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 2) * (gen0 0) * (gen0 2) * (gen0 0) * (gen0 0) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) * (gen0 1) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) else (gen0 1) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 2) * (gen0 2) * (gen0 2) * (gen0 1) * (gen0 1) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 0) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 2) * (gen0 0) * (gen0 2) * (gen0 0) * (gen0 0) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) * (gen0 1) * (gen0 2) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) * (gen0 1) * (gen0 2) * (gen0 0) * (gen0 1) * (gen0 0) * (gen0 1) * (gen0 2) * (gen0 0) * (gen0 2) * (gen0 0) * (gen0 2) * (gen0 1) * (gen0 2) * (gen0 1))))

private theorem rawGen1_fix : ∀ i, rawGen1 i ∈ MulAction.stabilizer S0 (261 : Fin 2058) := by
  decide +kernel
private def gen1 (i : Fin 7) : S1 := by
  refine ⟨rawGen1 i, ?_⟩
  exact rawGen1_fix i

private def signedGen1 (i : Fin 14) : S1 :=
  (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then gen1 0 else (if i.val < 2 then gen1 1 else gen1 2)) else (if i.val < 5 then (if i.val < 4 then gen1 3 else gen1 4) else (if i.val < 6 then gen1 5 else gen1 6))) else (if i.val < 10 then (if i.val < 8 then (gen1 0)⁻¹ else (if i.val < 9 then (gen1 1)⁻¹ else (gen1 2)⁻¹)) else (if i.val < 12 then (if i.val < 11 then (gen1 3)⁻¹ else (gen1 4)⁻¹) else (if i.val < 13 then (gen1 5)⁻¹ else (gen1 6)⁻¹))))

private def point1 (i : Fin 60) : Fin 2058 :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 6 else (if i.val < 2 then 29 else 51)) else (if i.val < 5 then (if i.val < 4 then 81 else 91) else (if i.val < 6 then 136 else 174))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 237 else 279) else (if i.val < 10 then 293 else 302)) else (if i.val < 13 then (if i.val < 12 then 307 else 388) else (if i.val < 14 then 505 else 776)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 786 else (if i.val < 17 then 795 else 801)) else (if i.val < 20 then (if i.val < 19 then 803 else 833) else (if i.val < 21 then 837 else 839))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 874 else 914) else (if i.val < 25 then 923 else 984)) else (if i.val < 28 then (if i.val < 27 then 992 else 1008) else (if i.val < 29 then 1042 else 1074))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 1110 else (if i.val < 32 then 1158 else 1203)) else (if i.val < 35 then (if i.val < 34 then 1282 else 1285) else (if i.val < 36 then 1287 else 1294))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 1306 else 1335) else (if i.val < 40 then 1344 else 1367)) else (if i.val < 43 then (if i.val < 42 then 1385 else 1418) else (if i.val < 44 then 1434 else 1492)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 1540 else (if i.val < 47 then 1607 else 1617)) else (if i.val < 50 then (if i.val < 49 then 1619 else 1645) else (if i.val < 51 then 1651 else 1824))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 1839 else 1843) else (if i.val < 55 then 1871 else 1894)) else (if i.val < 58 then (if i.val < 57 then 1905 else 1967) else (if i.val < 59 then 2001 else 2008))))))

private def parent1 (i : Fin 60) : Fin 60 :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 29 else 57)) else (if i.val < 5 then (if i.val < 4 then 18 else 32) else (if i.val < 6 then 33 else 24))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 47 else 33) else (if i.val < 10 then 49 else 14)) else (if i.val < 13 then (if i.val < 12 then 45 else 29) else (if i.val < 14 then 26 else 50)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 40 else (if i.val < 17 then 58 else 12)) else (if i.val < 20 then (if i.val < 19 then 10 else 31) else (if i.val < 21 then 44 else 29))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 24 else 6) else (if i.val < 25 then 40 else 36)) else (if i.val < 28 then (if i.val < 27 then 18 else 12) else (if i.val < 29 then 12 else 14))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 22 else (if i.val < 32 then 33 else 33)) else (if i.val < 35 then (if i.val < 34 then 29 else 5) else (if i.val < 36 then 57 else 29))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 12 else 10) else (if i.val < 40 then 46 else 50)) else (if i.val < 43 then (if i.val < 42 then 14 else 47) else (if i.val < 44 then 18 else 29)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 41 else (if i.val < 47 then 40 else 14)) else (if i.val < 50 then (if i.val < 49 then 33 else 40) else (if i.val < 51 then 50 else 31))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 57 else 31) else (if i.val < 55 then 56 else 44)) else (if i.val < 58 then (if i.val < 57 then 10 else 10) else (if i.val < 59 then 10 else 15))))))

private def step1 (i : Fin 60) : Fin 14 :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 9 else (if i.val < 2 then 5 else 1)) else (if i.val < 5 then (if i.val < 4 then 5 else 1) else (if i.val < 6 then 3 else 5))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 1 else 12) else (if i.val < 10 then 9 else 2)) else (if i.val < 13 then (if i.val < 12 then 1 else 2) else (if i.val < 14 then 9 else 0)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 3 else (if i.val < 17 then 10 else 3)) else (if i.val < 20 then (if i.val < 19 then 3 else 12) else (if i.val < 21 then 5 else 4))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 2 else 9) else (if i.val < 25 then 10 else 9)) else (if i.val < 28 then (if i.val < 27 then 12 else 1) else (if i.val < 29 then 10 else 1))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 12 else (if i.val < 32 then 1 else 2)) else (if i.val < 35 then (if i.val < 34 then 0 else 1) else (if i.val < 36 then 2 else 10))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 5 else 12) else (if i.val < 40 then 9 else 9)) else (if i.val < 43 then (if i.val < 42 then 12 else 2) else (if i.val < 44 then 1 else 9)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 2 else (if i.val < 47 then 12 else 5)) else (if i.val < 50 then (if i.val < 49 then 5 else 5) else (if i.val < 51 then 0 else 5))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 0 else 2) else (if i.val < 55 then 5 else 3)) else (if i.val < 58 then (if i.val < 57 then 10 else 5) else (if i.val < 59 then 1 else 3))))))

private def depth1 (i : Fin 60) : ℕ :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 4 else (if i.val < 2 then 3 else 4)) else (if i.val < 5 then (if i.val < 4 then 4 else 5) else (if i.val < 6 then 4 else 3))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 3 else 4) else (if i.val < 10 then 3 else 2)) else (if i.val < 13 then (if i.val < 12 then 4 else 3) else (if i.val < 14 then 5 else 1)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 2 else (if i.val < 17 then 4 else 4)) else (if i.val < 20 then (if i.val < 19 then 3 else 5) else (if i.val < 21 then 4 else 3))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 3 else 4) else (if i.val < 25 then 2 else 4)) else (if i.val < 28 then (if i.val < 27 then 4 else 4) else (if i.val < 29 then 4 else 2))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 4 else (if i.val < 32 then 4 else 4)) else (if i.val < 35 then (if i.val < 34 then 3 else 5) else (if i.val < 36 then 4 else 3))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 4 else 3) else (if i.val < 40 then 3 else 1)) else (if i.val < 43 then (if i.val < 42 then 2 else 3) else (if i.val < 44 then 4 else 3)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 3 else (if i.val < 47 then 2 else 2)) else (if i.val < 50 then (if i.val < 49 then 4 else 2) else (if i.val < 51 then 0 else 5))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 4 else 5) else (if i.val < 55 then 4 else 4)) else (if i.val < 58 then (if i.val < 57 then 3 else 3) else (if i.val < 59 then 3 else 3))))))

private theorem point1_injective : Function.Injective point1 := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem tree1_valid : ∀ i, i = 50 ∨
    (depth1 (parent1 i) < depth1 i ∧
      signedGen1 (step1 i) • point1 (parent1 i) = point1 i) := by
  decide +kernel
private theorem reach1 : ∀ i, ∃ g : S1, g • (1651 : Fin 2058) = point1 i :=
  orbit_tree signedGen1 1651 point1 parent1 step1 depth1 50
    (by decide +kernel) tree1_valid

private abbrev S2 := ↥(MulAction.stabilizer S1 (1651 : Fin 2058))

private def rawGen2 (i : Fin 5) : S1 :=
  (if i.val < 2 then (if i.val < 1 then (gen1 1) else (gen1 3)) else (if i.val < 3 then (gen1 4) else (if i.val < 4 then (gen1 5) else (gen1 6))))

private theorem rawGen2_fix : ∀ i, rawGen2 i ∈ MulAction.stabilizer S1 (1651 : Fin 2058) := by
  decide +kernel
private def gen2 (i : Fin 5) : S2 := by
  refine ⟨rawGen2 i, ?_⟩
  exact rawGen2_fix i

private def signedGen2 (i : Fin 10) : S2 :=
  (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then gen2 0 else gen2 1) else (if i.val < 3 then gen2 2 else (if i.val < 4 then gen2 3 else gen2 4))) else (if i.val < 7 then (if i.val < 6 then (gen2 0)⁻¹ else (gen2 1)⁻¹) else (if i.val < 8 then (gen2 2)⁻¹ else (if i.val < 9 then (gen2 3)⁻¹ else (gen2 4)⁻¹))))

private def point2 (i : Fin 40) : Fin 2058 :=
  (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 25 else 149) else (if i.val < 3 then 227 else (if i.val < 4 then 230 else 260))) else (if i.val < 7 then (if i.val < 6 then 268 else 365) else (if i.val < 8 then 396 else (if i.val < 9 then 416 else 417)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 439 else 473) else (if i.val < 13 then 521 else (if i.val < 14 then 604 else 617))) else (if i.val < 17 then (if i.val < 16 then 680 else 720) else (if i.val < 18 then 811 else (if i.val < 19 then 1024 else 1038))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 1081 else 1100) else (if i.val < 23 then 1150 else (if i.val < 24 then 1171 else 1406))) else (if i.val < 27 then (if i.val < 26 then 1409 else 1430) else (if i.val < 28 then 1441 else (if i.val < 29 then 1477 else 1490)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 1610 else 1704) else (if i.val < 33 then 1714 else (if i.val < 34 then 1737 else 1826))) else (if i.val < 37 then (if i.val < 36 then 1834 else 1865) else (if i.val < 38 then 1880 else (if i.val < 39 then 1991 else 2020))))))

private def parent2 (i : Fin 40) : Fin 40 :=
  (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 13 else (if i.val < 4 then 28 else 9))) else (if i.val < 7 then (if i.val < 6 then 6 else 1) else (if i.val < 8 then 24 else (if i.val < 9 then 6 else 1)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 13 else 21) else (if i.val < 13 then 6 else (if i.val < 14 then 9 else 18))) else (if i.val < 17 then (if i.val < 16 then 8 else 30) else (if i.val < 18 then 39 else (if i.val < 19 then 0 else 39))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 12 else 9) else (if i.val < 23 then 9 else (if i.val < 24 then 4 else 6))) else (if i.val < 27 then (if i.val < 26 then 30 else 22) else (if i.val < 28 then 34 else (if i.val < 29 then 0 else 19)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 13 else 11) else (if i.val < 33 then 13 else (if i.val < 34 then 32 else 39))) else (if i.val < 37 then (if i.val < 36 then 8 else 2) else (if i.val < 38 then 8 else (if i.val < 39 then 39 else 9))))))

private def step2 (i : Fin 40) : Fin 10 :=
  (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 6 else 0) else (if i.val < 3 then 8 else (if i.val < 4 then 1 else 3))) else (if i.val < 7 then (if i.val < 6 then 0 else 1) else (if i.val < 8 then 0 else (if i.val < 9 then 2 else 0)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 2 else 8) else (if i.val < 13 then 3 else (if i.val < 14 then 1 else 0))) else (if i.val < 17 then (if i.val < 16 then 6 else 3) else (if i.val < 18 then 6 else (if i.val < 19 then 2 else 3))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 0 else 6) else (if i.val < 23 then 8 else (if i.val < 24 then 1 else 1))) else (if i.val < 27 then (if i.val < 26 then 2 else 6) else (if i.val < 28 then 8 else (if i.val < 29 then 0 else 1)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 1 else 0) else (if i.val < 33 then 3 else (if i.val < 34 then 1 else 1))) else (if i.val < 37 then (if i.val < 36 then 0 else 0) else (if i.val < 38 then 8 else (if i.val < 39 then 8 else 2))))))

private def depth2 (i : Fin 40) : ℕ :=
  (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 3 else (if i.val < 4 then 3 else 2))) else (if i.val < 7 then (if i.val < 6 then 2 else 1) else (if i.val < 8 then 3 else (if i.val < 9 then 2 else 1)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 3 else 3) else (if i.val < 13 then 2 else (if i.val < 14 then 2 else 3))) else (if i.val < 17 then (if i.val < 16 then 3 else 4) else (if i.val < 18 then 3 else (if i.val < 19 then 2 else 3))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 2 else (if i.val < 24 then 3 else 2))) else (if i.val < 27 then (if i.val < 26 then 4 else 3) else (if i.val < 28 then 4 else (if i.val < 29 then 2 else 4)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 3 else 4) else (if i.val < 33 then 3 else (if i.val < 34 then 4 else 3))) else (if i.val < 37 then (if i.val < 36 then 3 else 4) else (if i.val < 38 then 3 else (if i.val < 39 then 3 else 2))))))

private theorem point2_injective : Function.Injective point2 := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem tree2_valid : ∀ i, i = 1 ∨
    (depth2 (parent2 i) < depth2 i ∧
      signedGen2 (step2 i) • point2 (parent2 i) = point2 i) := by
  decide +kernel
private theorem reach2 : ∀ i, ∃ g : S2, g • (149 : Fin 2058) = point2 i :=
  orbit_tree signedGen2 149 point2 parent2 step2 depth2 1
    (by decide +kernel) tree2_valid

private abbrev S3 := ↥(MulAction.stabilizer S2 (149 : Fin 2058))

private def rawGen3 (i : Fin 3) : S2 :=
  (if i.val < 1 then (gen2 2) else (if i.val < 2 then (gen2 3) else (gen2 4)))

private theorem rawGen3_fix : ∀ i, rawGen3 i ∈ MulAction.stabilizer S2 (149 : Fin 2058) := by
  decide +kernel
private def gen3 (i : Fin 3) : S3 := by
  refine ⟨rawGen3 i, ?_⟩
  exact rawGen3_fix i

private def signedGen3 (i : Fin 6) : S3 :=
  (if i.val < 3 then (if i.val < 1 then gen3 0 else (if i.val < 2 then gen3 1 else gen3 2)) else (if i.val < 4 then (gen3 0)⁻¹ else (if i.val < 5 then (gen3 1)⁻¹ else (gen3 2)⁻¹)))

private def point3 (i : Fin 3) : Fin 2058 :=
  (if i.val < 1 then 4 else (if i.val < 2 then 1747 else 1812))

private def parent3 (i : Fin 3) : Fin 3 :=
  (if i.val < 1 then 0 else (if i.val < 2 then 0 else 0))

private def step3 (i : Fin 3) : Fin 6 :=
  (if i.val < 1 then 0 else (if i.val < 2 then 4 else 0))

private def depth3 (i : Fin 3) : ℕ :=
  (if i.val < 1 then 0 else (if i.val < 2 then 1 else 1))

private theorem point3_injective : Function.Injective point3 := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem tree3_valid : ∀ i, i = 0 ∨
    (depth3 (parent3 i) < depth3 i ∧
      signedGen3 (step3 i) • point3 (parent3 i) = point3 i) := by
  decide +kernel
private theorem reach3 : ∀ i, ∃ g : S3, g • (4 : Fin 2058) = point3 i :=
  orbit_tree signedGen3 4 point3 parent3 step3 depth3 0
    (by decide +kernel) tree3_valid

private abbrev S4 := ↥(MulAction.stabilizer S3 (4 : Fin 2058))

-- Keep elaboration from expanding this long nested word at each membership use.
-- Kernel reduction still checks its complete definition below.
@[irreducible] private def rawGen4 (_i : Fin 1) : S3 :=
  (gen3 1) * (gen3 1) * (gen3 0)

private theorem rawGen4_fix : ∀ i, rawGen4 i ∈ MulAction.stabilizer S3 (4 : Fin 2058) := by
  decide +kernel
private def gen4 (i : Fin 1) : S4 := by
  refine ⟨rawGen4 i, ?_⟩
  exact rawGen4_fix i

private def signedGen4 (i : Fin 2) : S4 :=
  (if i.val < 1 then gen4 0 else (gen4 0)⁻¹)

private def point4 (i : Fin 2) : Fin 2058 :=
  (if i.val < 1 then 25 else 416)

private def parent4 (i : Fin 2) : Fin 2 :=
  (if i.val < 1 then 0 else 0)

private def step4 (i : Fin 2) : Fin 2 :=
  (if i.val < 1 then 0 else 0)

private def depth4 (i : Fin 2) : ℕ :=
  (if i.val < 1 then 0 else 1)

private theorem point4_injective : Function.Injective point4 := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel
private theorem tree4_valid : ∀ i, i = 0 ∨
    (depth4 (parent4 i) < depth4 i ∧
      signedGen4 (step4 i) • point4 (parent4 i) = point4 i) := by
  decide +kernel
private theorem reach4 : ∀ i, ∃ g : S4, g • (25 : Fin 2058) = point4 i :=
  orbit_tree signedGen4 25 point4 parent4 step4 depth4 0
    (by decide +kernel) tree4_valid

-- END GENERATED ORBIT CERTIFICATE

/-- The actual image of the marked M₁ generators contains at least 1,958,400 elements. -/
public theorem concrete_lower_bound : ConcreteLowerBound := by
  have h0 := orbit_lower (G := S0) (261 : Fin 2058) point0 point0_injective reach0
  have h1 := orbit_lower (G := S1) (1651 : Fin 2058) point1 point1_injective reach1
  have h2 := orbit_lower (G := S2) (149 : Fin 2058) point2 point2_injective reach2
  have h3 := orbit_lower (G := S3) (4 : Fin 2058) point3 point3_injective reach3
  have h4 := orbit_lower (G := S4) (25 : Fin 2058) point4 point4_injective reach4
  have hp : 0 < Nat.card (MulAction.stabilizer S4 (25 : Fin 2058)) := Nat.card_pos
  change 136 * Nat.card S1 ≤ Nat.card S0 at h0
  change 60 * Nat.card S2 ≤ Nat.card S1 at h1
  change 40 * Nat.card S3 ≤ Nat.card S2 at h2
  change 3 * Nat.card S4 ≤ Nat.card S3 at h3
  change 1958400 ≤ Nat.card S0
  omega

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
