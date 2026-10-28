module

public import Theory.SpecificGroups.Held.TwoRank.Coloring.Action

/-!
# Exhaustive Held extension-coloring certificates

The 2048 indices are checked in blocks of 32; the 64 color rows are checked
separately. All checks use `decide +kernel`. The action and soundness lemmas
are in `Action`; these checks make no assumption about rank or realization.
Source: the ATLAS degree-2058 carrier; regenerate with `Source/generate.py`.
-/

namespace Held.TwoRank.Coloring

set_option maxRecDepth 8192 in
private theorem cover00 : ∀ j : Fin 32,
    coverCheck ⟨0 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover01 : ∀ j : Fin 32,
    coverCheck ⟨1 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover02 : ∀ j : Fin 32,
    coverCheck ⟨2 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover03 : ∀ j : Fin 32,
    coverCheck ⟨3 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover04 : ∀ j : Fin 32,
    coverCheck ⟨4 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover05 : ∀ j : Fin 32,
    coverCheck ⟨5 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover06 : ∀ j : Fin 32,
    coverCheck ⟨6 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover07 : ∀ j : Fin 32,
    coverCheck ⟨7 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover08 : ∀ j : Fin 32,
    coverCheck ⟨8 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover09 : ∀ j : Fin 32,
    coverCheck ⟨9 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover10 : ∀ j : Fin 32,
    coverCheck ⟨10 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover11 : ∀ j : Fin 32,
    coverCheck ⟨11 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover12 : ∀ j : Fin 32,
    coverCheck ⟨12 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover13 : ∀ j : Fin 32,
    coverCheck ⟨13 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover14 : ∀ j : Fin 32,
    coverCheck ⟨14 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover15 : ∀ j : Fin 32,
    coverCheck ⟨15 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover16 : ∀ j : Fin 32,
    coverCheck ⟨16 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover17 : ∀ j : Fin 32,
    coverCheck ⟨17 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover18 : ∀ j : Fin 32,
    coverCheck ⟨18 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover19 : ∀ j : Fin 32,
    coverCheck ⟨19 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover20 : ∀ j : Fin 32,
    coverCheck ⟨20 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover21 : ∀ j : Fin 32,
    coverCheck ⟨21 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover22 : ∀ j : Fin 32,
    coverCheck ⟨22 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover23 : ∀ j : Fin 32,
    coverCheck ⟨23 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover24 : ∀ j : Fin 32,
    coverCheck ⟨24 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover25 : ∀ j : Fin 32,
    coverCheck ⟨25 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover26 : ∀ j : Fin 32,
    coverCheck ⟨26 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover27 : ∀ j : Fin 32,
    coverCheck ⟨27 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover28 : ∀ j : Fin 32,
    coverCheck ⟨28 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover29 : ∀ j : Fin 32,
    coverCheck ⟨29 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover30 : ∀ j : Fin 32,
    coverCheck ⟨30 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover31 : ∀ j : Fin 32,
    coverCheck ⟨31 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover32 : ∀ j : Fin 32,
    coverCheck ⟨32 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover33 : ∀ j : Fin 32,
    coverCheck ⟨33 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover34 : ∀ j : Fin 32,
    coverCheck ⟨34 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover35 : ∀ j : Fin 32,
    coverCheck ⟨35 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover36 : ∀ j : Fin 32,
    coverCheck ⟨36 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover37 : ∀ j : Fin 32,
    coverCheck ⟨37 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover38 : ∀ j : Fin 32,
    coverCheck ⟨38 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover39 : ∀ j : Fin 32,
    coverCheck ⟨39 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover40 : ∀ j : Fin 32,
    coverCheck ⟨40 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover41 : ∀ j : Fin 32,
    coverCheck ⟨41 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover42 : ∀ j : Fin 32,
    coverCheck ⟨42 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover43 : ∀ j : Fin 32,
    coverCheck ⟨43 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover44 : ∀ j : Fin 32,
    coverCheck ⟨44 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover45 : ∀ j : Fin 32,
    coverCheck ⟨45 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover46 : ∀ j : Fin 32,
    coverCheck ⟨46 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover47 : ∀ j : Fin 32,
    coverCheck ⟨47 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover48 : ∀ j : Fin 32,
    coverCheck ⟨48 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover49 : ∀ j : Fin 32,
    coverCheck ⟨49 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover50 : ∀ j : Fin 32,
    coverCheck ⟨50 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover51 : ∀ j : Fin 32,
    coverCheck ⟨51 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover52 : ∀ j : Fin 32,
    coverCheck ⟨52 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover53 : ∀ j : Fin 32,
    coverCheck ⟨53 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover54 : ∀ j : Fin 32,
    coverCheck ⟨54 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover55 : ∀ j : Fin 32,
    coverCheck ⟨55 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover56 : ∀ j : Fin 32,
    coverCheck ⟨56 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover57 : ∀ j : Fin 32,
    coverCheck ⟨57 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover58 : ∀ j : Fin 32,
    coverCheck ⟨58 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover59 : ∀ j : Fin 32,
    coverCheck ⟨59 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover60 : ∀ j : Fin 32,
    coverCheck ⟨60 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover61 : ∀ j : Fin 32,
    coverCheck ⟨61 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover62 : ∀ j : Fin 32,
    coverCheck ⟨62 * 32 + j.val, by omega⟩ = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cover63 : ∀ j : Fin 32,
    coverCheck ⟨63 * 32 + j.val, by omega⟩ = true := by decide +kernel

private theorem coverBlock (i : Fin 64) : ∀ j : Fin 32,
    coverCheck ⟨i.val * 32 + j.val, by omega⟩ = true := by
  fin_cases i
  · exact cover00
  · exact cover01
  · exact cover02
  · exact cover03
  · exact cover04
  · exact cover05
  · exact cover06
  · exact cover07
  · exact cover08
  · exact cover09
  · exact cover10
  · exact cover11
  · exact cover12
  · exact cover13
  · exact cover14
  · exact cover15
  · exact cover16
  · exact cover17
  · exact cover18
  · exact cover19
  · exact cover20
  · exact cover21
  · exact cover22
  · exact cover23
  · exact cover24
  · exact cover25
  · exact cover26
  · exact cover27
  · exact cover28
  · exact cover29
  · exact cover30
  · exact cover31
  · exact cover32
  · exact cover33
  · exact cover34
  · exact cover35
  · exact cover36
  · exact cover37
  · exact cover38
  · exact cover39
  · exact cover40
  · exact cover41
  · exact cover42
  · exact cover43
  · exact cover44
  · exact cover45
  · exact cover46
  · exact cover47
  · exact cover48
  · exact cover49
  · exact cover50
  · exact cover51
  · exact cover52
  · exact cover53
  · exact cover54
  · exact cover55
  · exact cover56
  · exact cover57
  · exact cover58
  · exact cover59
  · exact cover60
  · exact cover61
  · exact cover62
  · exact cover63

public theorem coverChecks (n : Fin 2048) : coverCheck n = true := by
  have h := coverBlock ⟨n.val / 32, by omega⟩ ⟨n.val % 32, Nat.mod_lt _ (by decide)⟩
  have hi : n.val / 32 * 32 + n.val % 32 = n.val := by omega
  simpa only [hi] using h

set_option maxRecDepth 8192 in
private theorem separation00 : ∀ i j : Fin 12,
    separationCheck 0 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation01 : ∀ i j : Fin 12,
    separationCheck 1 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation02 : ∀ i j : Fin 12,
    separationCheck 2 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation03 : ∀ i j : Fin 12,
    separationCheck 3 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation04 : ∀ i j : Fin 12,
    separationCheck 4 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation05 : ∀ i j : Fin 12,
    separationCheck 5 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation06 : ∀ i j : Fin 12,
    separationCheck 6 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation07 : ∀ i j : Fin 12,
    separationCheck 7 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation08 : ∀ i j : Fin 12,
    separationCheck 8 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation09 : ∀ i j : Fin 12,
    separationCheck 9 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation10 : ∀ i j : Fin 12,
    separationCheck 10 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation11 : ∀ i j : Fin 12,
    separationCheck 11 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation12 : ∀ i j : Fin 12,
    separationCheck 12 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation13 : ∀ i j : Fin 12,
    separationCheck 13 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation14 : ∀ i j : Fin 12,
    separationCheck 14 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation15 : ∀ i j : Fin 12,
    separationCheck 15 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation16 : ∀ i j : Fin 12,
    separationCheck 16 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation17 : ∀ i j : Fin 12,
    separationCheck 17 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation18 : ∀ i j : Fin 12,
    separationCheck 18 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation19 : ∀ i j : Fin 12,
    separationCheck 19 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation20 : ∀ i j : Fin 12,
    separationCheck 20 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation21 : ∀ i j : Fin 12,
    separationCheck 21 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation22 : ∀ i j : Fin 12,
    separationCheck 22 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation23 : ∀ i j : Fin 12,
    separationCheck 23 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation24 : ∀ i j : Fin 12,
    separationCheck 24 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation25 : ∀ i j : Fin 12,
    separationCheck 25 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation26 : ∀ i j : Fin 12,
    separationCheck 26 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation27 : ∀ i j : Fin 12,
    separationCheck 27 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation28 : ∀ i j : Fin 12,
    separationCheck 28 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation29 : ∀ i j : Fin 12,
    separationCheck 29 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation30 : ∀ i j : Fin 12,
    separationCheck 30 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation31 : ∀ i j : Fin 12,
    separationCheck 31 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation32 : ∀ i j : Fin 12,
    separationCheck 32 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation33 : ∀ i j : Fin 12,
    separationCheck 33 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation34 : ∀ i j : Fin 12,
    separationCheck 34 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation35 : ∀ i j : Fin 12,
    separationCheck 35 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation36 : ∀ i j : Fin 12,
    separationCheck 36 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation37 : ∀ i j : Fin 12,
    separationCheck 37 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation38 : ∀ i j : Fin 12,
    separationCheck 38 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation39 : ∀ i j : Fin 12,
    separationCheck 39 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation40 : ∀ i j : Fin 12,
    separationCheck 40 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation41 : ∀ i j : Fin 12,
    separationCheck 41 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation42 : ∀ i j : Fin 12,
    separationCheck 42 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation43 : ∀ i j : Fin 12,
    separationCheck 43 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation44 : ∀ i j : Fin 12,
    separationCheck 44 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation45 : ∀ i j : Fin 12,
    separationCheck 45 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation46 : ∀ i j : Fin 12,
    separationCheck 46 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation47 : ∀ i j : Fin 12,
    separationCheck 47 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation48 : ∀ i j : Fin 12,
    separationCheck 48 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation49 : ∀ i j : Fin 12,
    separationCheck 49 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation50 : ∀ i j : Fin 12,
    separationCheck 50 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation51 : ∀ i j : Fin 12,
    separationCheck 51 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation52 : ∀ i j : Fin 12,
    separationCheck 52 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation53 : ∀ i j : Fin 12,
    separationCheck 53 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation54 : ∀ i j : Fin 12,
    separationCheck 54 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation55 : ∀ i j : Fin 12,
    separationCheck 55 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation56 : ∀ i j : Fin 12,
    separationCheck 56 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation57 : ∀ i j : Fin 12,
    separationCheck 57 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation58 : ∀ i j : Fin 12,
    separationCheck 58 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation59 : ∀ i j : Fin 12,
    separationCheck 59 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation60 : ∀ i j : Fin 12,
    separationCheck 60 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation61 : ∀ i j : Fin 12,
    separationCheck 61 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation62 : ∀ i j : Fin 12,
    separationCheck 62 i j = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem separation63 : ∀ i j : Fin 12,
    separationCheck 63 i j = true := by decide +kernel

public theorem separationChecks (c : Fin 64) : ∀ i j : Fin 12,
    separationCheck c i j = true := by
  fin_cases c
  · exact separation00
  · exact separation01
  · exact separation02
  · exact separation03
  · exact separation04
  · exact separation05
  · exact separation06
  · exact separation07
  · exact separation08
  · exact separation09
  · exact separation10
  · exact separation11
  · exact separation12
  · exact separation13
  · exact separation14
  · exact separation15
  · exact separation16
  · exact separation17
  · exact separation18
  · exact separation19
  · exact separation20
  · exact separation21
  · exact separation22
  · exact separation23
  · exact separation24
  · exact separation25
  · exact separation26
  · exact separation27
  · exact separation28
  · exact separation29
  · exact separation30
  · exact separation31
  · exact separation32
  · exact separation33
  · exact separation34
  · exact separation35
  · exact separation36
  · exact separation37
  · exact separation38
  · exact separation39
  · exact separation40
  · exact separation41
  · exact separation42
  · exact separation43
  · exact separation44
  · exact separation45
  · exact separation46
  · exact separation47
  · exact separation48
  · exact separation49
  · exact separation50
  · exact separation51
  · exact separation52
  · exact separation53
  · exact separation54
  · exact separation55
  · exact separation56
  · exact separation57
  · exact separation58
  · exact separation59
  · exact separation60
  · exact separation61
  · exact separation62
  · exact separation63

end Held.TwoRank.Coloring
