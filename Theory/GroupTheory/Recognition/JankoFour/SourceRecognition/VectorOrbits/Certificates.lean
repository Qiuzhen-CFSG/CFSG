module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits.Data

/-!
# Checked native vector-orbit forest

The finite checks verify descent and generator edges for every vector, as
well as invariance of the root label under both native generators. Thus the
forest proves both orbit coverage and orbit separation. Counts refer to the
literal fibers of this invariant, not to assumed group or stabilizer orders.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), p.597, DOI 10.1007/BF01232280.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits

private def wordAt (i : Fin 128) (j : Fin 32) : Word := ⟨32*i.val+j.val, by omega⟩

private theorem forall_word (P : Word → Prop) (h : ∀ i j, P (wordAt i j)) : ∀ n, P n := by
  intro n
  have he : wordAt ⟨n.val/32, by omega⟩ ⟨n.val%32, Nat.mod_lt _ (by decide)⟩ = n := by
    apply Fin.ext
    dsimp [wordAt]
    omega
  exact he ▸ h _ _


private def nextWord (b : Bool) (n : Word) : Word := ⟨next b n % 4096, Nat.mod_lt _ (by decide)⟩

private def Valid (n : Word) : Prop :=
    ((treeRow n).root = 0 ∨ (treeRow n).root = 1 ∨
      (treeRow n).root = 4 ∨ (treeRow n).root = 7) ∧
    ((treeRow n).root = 0 ↔ n = 0) ∧
    ((treeRow n).depth = 0 → n = (treeRow n).root) ∧
    ((treeRow n).depth ≠ 0 →
      (treeRow (treeRow n).parent).depth < (treeRow n).depth ∧
      (treeRow (treeRow n).parent).root = (treeRow n).root ∧
      next (treeRow n).useB (treeRow n).parent = n.val) ∧
    (∀ b : Bool, next b n < 4096 ∧ (treeRow (nextWord b n)).root = (treeRow n).root)

private instance (n : Word) : Decidable (Valid n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

set_option Elab.async false

private theorem block000 : ∀ j : Fin 32, Valid (wordAt 0 j) := by
  decide +kernel

private theorem block001 : ∀ j : Fin 32, Valid (wordAt 1 j) := by
  decide +kernel

private theorem block002 : ∀ j : Fin 32, Valid (wordAt 2 j) := by
  decide +kernel

private theorem block003 : ∀ j : Fin 32, Valid (wordAt 3 j) := by
  decide +kernel

private theorem block004 : ∀ j : Fin 32, Valid (wordAt 4 j) := by
  decide +kernel

private theorem block005 : ∀ j : Fin 32, Valid (wordAt 5 j) := by
  decide +kernel

private theorem block006 : ∀ j : Fin 32, Valid (wordAt 6 j) := by
  decide +kernel

private theorem block007 : ∀ j : Fin 32, Valid (wordAt 7 j) := by
  decide +kernel

private theorem block008 : ∀ j : Fin 32, Valid (wordAt 8 j) := by
  decide +kernel

private theorem block009 : ∀ j : Fin 32, Valid (wordAt 9 j) := by
  decide +kernel

private theorem block010 : ∀ j : Fin 32, Valid (wordAt 10 j) := by
  decide +kernel

private theorem block011 : ∀ j : Fin 32, Valid (wordAt 11 j) := by
  decide +kernel

private theorem block012 : ∀ j : Fin 32, Valid (wordAt 12 j) := by
  decide +kernel

private theorem block013 : ∀ j : Fin 32, Valid (wordAt 13 j) := by
  decide +kernel

private theorem block014 : ∀ j : Fin 32, Valid (wordAt 14 j) := by
  decide +kernel

private theorem block015 : ∀ j : Fin 32, Valid (wordAt 15 j) := by
  decide +kernel

private theorem block016 : ∀ j : Fin 32, Valid (wordAt 16 j) := by
  decide +kernel

private theorem block017 : ∀ j : Fin 32, Valid (wordAt 17 j) := by
  decide +kernel

private theorem block018 : ∀ j : Fin 32, Valid (wordAt 18 j) := by
  decide +kernel

private theorem block019 : ∀ j : Fin 32, Valid (wordAt 19 j) := by
  decide +kernel

private theorem block020 : ∀ j : Fin 32, Valid (wordAt 20 j) := by
  decide +kernel

private theorem block021 : ∀ j : Fin 32, Valid (wordAt 21 j) := by
  decide +kernel

private theorem block022 : ∀ j : Fin 32, Valid (wordAt 22 j) := by
  decide +kernel

private theorem block023 : ∀ j : Fin 32, Valid (wordAt 23 j) := by
  decide +kernel

private theorem block024 : ∀ j : Fin 32, Valid (wordAt 24 j) := by
  decide +kernel

private theorem block025 : ∀ j : Fin 32, Valid (wordAt 25 j) := by
  decide +kernel

private theorem block026 : ∀ j : Fin 32, Valid (wordAt 26 j) := by
  decide +kernel

private theorem block027 : ∀ j : Fin 32, Valid (wordAt 27 j) := by
  decide +kernel

private theorem block028 : ∀ j : Fin 32, Valid (wordAt 28 j) := by
  decide +kernel

private theorem block029 : ∀ j : Fin 32, Valid (wordAt 29 j) := by
  decide +kernel

private theorem block030 : ∀ j : Fin 32, Valid (wordAt 30 j) := by
  decide +kernel

private theorem block031 : ∀ j : Fin 32, Valid (wordAt 31 j) := by
  decide +kernel

private theorem block032 : ∀ j : Fin 32, Valid (wordAt 32 j) := by
  decide +kernel

private theorem block033 : ∀ j : Fin 32, Valid (wordAt 33 j) := by
  decide +kernel

private theorem block034 : ∀ j : Fin 32, Valid (wordAt 34 j) := by
  decide +kernel

private theorem block035 : ∀ j : Fin 32, Valid (wordAt 35 j) := by
  decide +kernel

private theorem block036 : ∀ j : Fin 32, Valid (wordAt 36 j) := by
  decide +kernel

private theorem block037 : ∀ j : Fin 32, Valid (wordAt 37 j) := by
  decide +kernel

private theorem block038 : ∀ j : Fin 32, Valid (wordAt 38 j) := by
  decide +kernel

private theorem block039 : ∀ j : Fin 32, Valid (wordAt 39 j) := by
  decide +kernel

private theorem block040 : ∀ j : Fin 32, Valid (wordAt 40 j) := by
  decide +kernel

private theorem block041 : ∀ j : Fin 32, Valid (wordAt 41 j) := by
  decide +kernel

private theorem block042 : ∀ j : Fin 32, Valid (wordAt 42 j) := by
  decide +kernel

private theorem block043 : ∀ j : Fin 32, Valid (wordAt 43 j) := by
  decide +kernel

private theorem block044 : ∀ j : Fin 32, Valid (wordAt 44 j) := by
  decide +kernel

private theorem block045 : ∀ j : Fin 32, Valid (wordAt 45 j) := by
  decide +kernel

private theorem block046 : ∀ j : Fin 32, Valid (wordAt 46 j) := by
  decide +kernel

private theorem block047 : ∀ j : Fin 32, Valid (wordAt 47 j) := by
  decide +kernel

private theorem block048 : ∀ j : Fin 32, Valid (wordAt 48 j) := by
  decide +kernel

private theorem block049 : ∀ j : Fin 32, Valid (wordAt 49 j) := by
  decide +kernel

private theorem block050 : ∀ j : Fin 32, Valid (wordAt 50 j) := by
  decide +kernel

private theorem block051 : ∀ j : Fin 32, Valid (wordAt 51 j) := by
  decide +kernel

private theorem block052 : ∀ j : Fin 32, Valid (wordAt 52 j) := by
  decide +kernel

private theorem block053 : ∀ j : Fin 32, Valid (wordAt 53 j) := by
  decide +kernel

private theorem block054 : ∀ j : Fin 32, Valid (wordAt 54 j) := by
  decide +kernel

private theorem block055 : ∀ j : Fin 32, Valid (wordAt 55 j) := by
  decide +kernel

private theorem block056 : ∀ j : Fin 32, Valid (wordAt 56 j) := by
  decide +kernel

private theorem block057 : ∀ j : Fin 32, Valid (wordAt 57 j) := by
  decide +kernel

private theorem block058 : ∀ j : Fin 32, Valid (wordAt 58 j) := by
  decide +kernel

private theorem block059 : ∀ j : Fin 32, Valid (wordAt 59 j) := by
  decide +kernel

private theorem block060 : ∀ j : Fin 32, Valid (wordAt 60 j) := by
  decide +kernel

private theorem block061 : ∀ j : Fin 32, Valid (wordAt 61 j) := by
  decide +kernel

private theorem block062 : ∀ j : Fin 32, Valid (wordAt 62 j) := by
  decide +kernel

private theorem block063 : ∀ j : Fin 32, Valid (wordAt 63 j) := by
  decide +kernel

private theorem block064 : ∀ j : Fin 32, Valid (wordAt 64 j) := by
  decide +kernel

private theorem block065 : ∀ j : Fin 32, Valid (wordAt 65 j) := by
  decide +kernel

private theorem block066 : ∀ j : Fin 32, Valid (wordAt 66 j) := by
  decide +kernel

private theorem block067 : ∀ j : Fin 32, Valid (wordAt 67 j) := by
  decide +kernel

private theorem block068 : ∀ j : Fin 32, Valid (wordAt 68 j) := by
  decide +kernel

private theorem block069 : ∀ j : Fin 32, Valid (wordAt 69 j) := by
  decide +kernel

private theorem block070 : ∀ j : Fin 32, Valid (wordAt 70 j) := by
  decide +kernel

private theorem block071 : ∀ j : Fin 32, Valid (wordAt 71 j) := by
  decide +kernel

private theorem block072 : ∀ j : Fin 32, Valid (wordAt 72 j) := by
  decide +kernel

private theorem block073 : ∀ j : Fin 32, Valid (wordAt 73 j) := by
  decide +kernel

private theorem block074 : ∀ j : Fin 32, Valid (wordAt 74 j) := by
  decide +kernel

private theorem block075 : ∀ j : Fin 32, Valid (wordAt 75 j) := by
  decide +kernel

private theorem block076 : ∀ j : Fin 32, Valid (wordAt 76 j) := by
  decide +kernel

private theorem block077 : ∀ j : Fin 32, Valid (wordAt 77 j) := by
  decide +kernel

private theorem block078 : ∀ j : Fin 32, Valid (wordAt 78 j) := by
  decide +kernel

private theorem block079 : ∀ j : Fin 32, Valid (wordAt 79 j) := by
  decide +kernel

private theorem block080 : ∀ j : Fin 32, Valid (wordAt 80 j) := by
  decide +kernel

private theorem block081 : ∀ j : Fin 32, Valid (wordAt 81 j) := by
  decide +kernel

private theorem block082 : ∀ j : Fin 32, Valid (wordAt 82 j) := by
  decide +kernel

private theorem block083 : ∀ j : Fin 32, Valid (wordAt 83 j) := by
  decide +kernel

private theorem block084 : ∀ j : Fin 32, Valid (wordAt 84 j) := by
  decide +kernel

private theorem block085 : ∀ j : Fin 32, Valid (wordAt 85 j) := by
  decide +kernel

private theorem block086 : ∀ j : Fin 32, Valid (wordAt 86 j) := by
  decide +kernel

private theorem block087 : ∀ j : Fin 32, Valid (wordAt 87 j) := by
  decide +kernel

private theorem block088 : ∀ j : Fin 32, Valid (wordAt 88 j) := by
  decide +kernel

private theorem block089 : ∀ j : Fin 32, Valid (wordAt 89 j) := by
  decide +kernel

private theorem block090 : ∀ j : Fin 32, Valid (wordAt 90 j) := by
  decide +kernel

private theorem block091 : ∀ j : Fin 32, Valid (wordAt 91 j) := by
  decide +kernel

private theorem block092 : ∀ j : Fin 32, Valid (wordAt 92 j) := by
  decide +kernel

private theorem block093 : ∀ j : Fin 32, Valid (wordAt 93 j) := by
  decide +kernel

private theorem block094 : ∀ j : Fin 32, Valid (wordAt 94 j) := by
  decide +kernel

private theorem block095 : ∀ j : Fin 32, Valid (wordAt 95 j) := by
  decide +kernel

private theorem block096 : ∀ j : Fin 32, Valid (wordAt 96 j) := by
  decide +kernel

private theorem block097 : ∀ j : Fin 32, Valid (wordAt 97 j) := by
  decide +kernel

private theorem block098 : ∀ j : Fin 32, Valid (wordAt 98 j) := by
  decide +kernel

private theorem block099 : ∀ j : Fin 32, Valid (wordAt 99 j) := by
  decide +kernel

private theorem block100 : ∀ j : Fin 32, Valid (wordAt 100 j) := by
  decide +kernel

private theorem block101 : ∀ j : Fin 32, Valid (wordAt 101 j) := by
  decide +kernel

private theorem block102 : ∀ j : Fin 32, Valid (wordAt 102 j) := by
  decide +kernel

private theorem block103 : ∀ j : Fin 32, Valid (wordAt 103 j) := by
  decide +kernel

private theorem block104 : ∀ j : Fin 32, Valid (wordAt 104 j) := by
  decide +kernel

private theorem block105 : ∀ j : Fin 32, Valid (wordAt 105 j) := by
  decide +kernel

private theorem block106 : ∀ j : Fin 32, Valid (wordAt 106 j) := by
  decide +kernel

private theorem block107 : ∀ j : Fin 32, Valid (wordAt 107 j) := by
  decide +kernel

private theorem block108 : ∀ j : Fin 32, Valid (wordAt 108 j) := by
  decide +kernel

private theorem block109 : ∀ j : Fin 32, Valid (wordAt 109 j) := by
  decide +kernel

private theorem block110 : ∀ j : Fin 32, Valid (wordAt 110 j) := by
  decide +kernel

private theorem block111 : ∀ j : Fin 32, Valid (wordAt 111 j) := by
  decide +kernel

private theorem block112 : ∀ j : Fin 32, Valid (wordAt 112 j) := by
  decide +kernel

private theorem block113 : ∀ j : Fin 32, Valid (wordAt 113 j) := by
  decide +kernel

private theorem block114 : ∀ j : Fin 32, Valid (wordAt 114 j) := by
  decide +kernel

private theorem block115 : ∀ j : Fin 32, Valid (wordAt 115 j) := by
  decide +kernel

private theorem block116 : ∀ j : Fin 32, Valid (wordAt 116 j) := by
  decide +kernel

private theorem block117 : ∀ j : Fin 32, Valid (wordAt 117 j) := by
  decide +kernel

private theorem block118 : ∀ j : Fin 32, Valid (wordAt 118 j) := by
  decide +kernel

private theorem block119 : ∀ j : Fin 32, Valid (wordAt 119 j) := by
  decide +kernel

private theorem block120 : ∀ j : Fin 32, Valid (wordAt 120 j) := by
  decide +kernel

private theorem block121 : ∀ j : Fin 32, Valid (wordAt 121 j) := by
  decide +kernel

private theorem block122 : ∀ j : Fin 32, Valid (wordAt 122 j) := by
  decide +kernel

private theorem block123 : ∀ j : Fin 32, Valid (wordAt 123 j) := by
  decide +kernel

private theorem block124 : ∀ j : Fin 32, Valid (wordAt 124 j) := by
  decide +kernel

private theorem block125 : ∀ j : Fin 32, Valid (wordAt 125 j) := by
  decide +kernel

private theorem block126 : ∀ j : Fin 32, Valid (wordAt 126 j) := by
  decide +kernel

private theorem block127 : ∀ j : Fin 32, Valid (wordAt 127 j) := by
  decide +kernel

private theorem forall_blocks (P : Fin 128 → Prop)
    (h000 : P 0)
    (h001 : P 1)
    (h002 : P 2)
    (h003 : P 3)
    (h004 : P 4)
    (h005 : P 5)
    (h006 : P 6)
    (h007 : P 7)
    (h008 : P 8)
    (h009 : P 9)
    (h010 : P 10)
    (h011 : P 11)
    (h012 : P 12)
    (h013 : P 13)
    (h014 : P 14)
    (h015 : P 15)
    (h016 : P 16)
    (h017 : P 17)
    (h018 : P 18)
    (h019 : P 19)
    (h020 : P 20)
    (h021 : P 21)
    (h022 : P 22)
    (h023 : P 23)
    (h024 : P 24)
    (h025 : P 25)
    (h026 : P 26)
    (h027 : P 27)
    (h028 : P 28)
    (h029 : P 29)
    (h030 : P 30)
    (h031 : P 31)
    (h032 : P 32)
    (h033 : P 33)
    (h034 : P 34)
    (h035 : P 35)
    (h036 : P 36)
    (h037 : P 37)
    (h038 : P 38)
    (h039 : P 39)
    (h040 : P 40)
    (h041 : P 41)
    (h042 : P 42)
    (h043 : P 43)
    (h044 : P 44)
    (h045 : P 45)
    (h046 : P 46)
    (h047 : P 47)
    (h048 : P 48)
    (h049 : P 49)
    (h050 : P 50)
    (h051 : P 51)
    (h052 : P 52)
    (h053 : P 53)
    (h054 : P 54)
    (h055 : P 55)
    (h056 : P 56)
    (h057 : P 57)
    (h058 : P 58)
    (h059 : P 59)
    (h060 : P 60)
    (h061 : P 61)
    (h062 : P 62)
    (h063 : P 63)
    (h064 : P 64)
    (h065 : P 65)
    (h066 : P 66)
    (h067 : P 67)
    (h068 : P 68)
    (h069 : P 69)
    (h070 : P 70)
    (h071 : P 71)
    (h072 : P 72)
    (h073 : P 73)
    (h074 : P 74)
    (h075 : P 75)
    (h076 : P 76)
    (h077 : P 77)
    (h078 : P 78)
    (h079 : P 79)
    (h080 : P 80)
    (h081 : P 81)
    (h082 : P 82)
    (h083 : P 83)
    (h084 : P 84)
    (h085 : P 85)
    (h086 : P 86)
    (h087 : P 87)
    (h088 : P 88)
    (h089 : P 89)
    (h090 : P 90)
    (h091 : P 91)
    (h092 : P 92)
    (h093 : P 93)
    (h094 : P 94)
    (h095 : P 95)
    (h096 : P 96)
    (h097 : P 97)
    (h098 : P 98)
    (h099 : P 99)
    (h100 : P 100)
    (h101 : P 101)
    (h102 : P 102)
    (h103 : P 103)
    (h104 : P 104)
    (h105 : P 105)
    (h106 : P 106)
    (h107 : P 107)
    (h108 : P 108)
    (h109 : P 109)
    (h110 : P 110)
    (h111 : P 111)
    (h112 : P 112)
    (h113 : P 113)
    (h114 : P 114)
    (h115 : P 115)
    (h116 : P 116)
    (h117 : P 117)
    (h118 : P 118)
    (h119 : P 119)
    (h120 : P 120)
    (h121 : P 121)
    (h122 : P 122)
    (h123 : P 123)
    (h124 : P 124)
    (h125 : P 125)
    (h126 : P 126)
    (h127 : P 127)
    : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h000
  · exact h001
  · exact h002
  · exact h003
  · exact h004
  · exact h005
  · exact h006
  · exact h007
  · exact h008
  · exact h009
  · exact h010
  · exact h011
  · exact h012
  · exact h013
  · exact h014
  · exact h015
  · exact h016
  · exact h017
  · exact h018
  · exact h019
  · exact h020
  · exact h021
  · exact h022
  · exact h023
  · exact h024
  · exact h025
  · exact h026
  · exact h027
  · exact h028
  · exact h029
  · exact h030
  · exact h031
  · exact h032
  · exact h033
  · exact h034
  · exact h035
  · exact h036
  · exact h037
  · exact h038
  · exact h039
  · exact h040
  · exact h041
  · exact h042
  · exact h043
  · exact h044
  · exact h045
  · exact h046
  · exact h047
  · exact h048
  · exact h049
  · exact h050
  · exact h051
  · exact h052
  · exact h053
  · exact h054
  · exact h055
  · exact h056
  · exact h057
  · exact h058
  · exact h059
  · exact h060
  · exact h061
  · exact h062
  · exact h063
  · exact h064
  · exact h065
  · exact h066
  · exact h067
  · exact h068
  · exact h069
  · exact h070
  · exact h071
  · exact h072
  · exact h073
  · exact h074
  · exact h075
  · exact h076
  · exact h077
  · exact h078
  · exact h079
  · exact h080
  · exact h081
  · exact h082
  · exact h083
  · exact h084
  · exact h085
  · exact h086
  · exact h087
  · exact h088
  · exact h089
  · exact h090
  · exact h091
  · exact h092
  · exact h093
  · exact h094
  · exact h095
  · exact h096
  · exact h097
  · exact h098
  · exact h099
  · exact h100
  · exact h101
  · exact h102
  · exact h103
  · exact h104
  · exact h105
  · exact h106
  · exact h107
  · exact h108
  · exact h109
  · exact h110
  · exact h111
  · exact h112
  · exact h113
  · exact h114
  · exact h115
  · exact h116
  · exact h117
  · exact h118
  · exact h119
  · exact h120
  · exact h121
  · exact h122
  · exact h123
  · exact h124
  · exact h125
  · exact h126
  · exact h127

private theorem valid_all : ∀ n : Word, Valid n := by
  apply forall_word
  exact forall_blocks (fun i => ∀ j, Valid (wordAt i j))
    block000 block001 block002 block003 block004 block005 block006 block007 block008 block009 block010 block011 block012 block013 block014 block015 block016 block017 block018 block019 block020 block021 block022 block023 block024 block025 block026 block027 block028 block029 block030 block031 block032 block033 block034 block035 block036 block037 block038 block039 block040 block041 block042 block043 block044 block045 block046 block047 block048 block049 block050 block051 block052 block053 block054 block055 block056 block057 block058 block059 block060 block061 block062 block063 block064 block065 block066 block067 block068 block069 block070 block071 block072 block073 block074 block075 block076 block077 block078 block079 block080 block081 block082 block083 block084 block085 block086 block087 block088 block089 block090 block091 block092 block093 block094 block095 block096 block097 block098 block099 block100 block101 block102 block103 block104 block105 block106 block107 block108 block109 block110 block111 block112 block113 block114 block115 block116 block117 block118 block119 block120 block121 block122 block123 block124 block125 block126 block127

theorem root_cases (n : Word) :
    (treeRow n).root = 0 ∨ (treeRow n).root = 1 ∨
      (treeRow n).root = 4 ∨ (treeRow n).root = 7 := (valid_all n).1

theorem root_zero (n : Word) : (treeRow n).root = 0 ↔ n = 0 := (valid_all n).2.1

theorem tree_roots (n : Word) : (treeRow n).depth = 0 → n = (treeRow n).root :=
  (valid_all n).2.2.1

theorem tree_descent (n : Word) : (treeRow n).depth ≠ 0 →
    (treeRow (treeRow n).parent).depth < (treeRow n).depth ∧
    (treeRow (treeRow n).parent).root = (treeRow n).root ∧
    next (treeRow n).useB (treeRow n).parent = n.val := (valid_all n).2.2.2.1

theorem next_lt (b : Bool) (n : Word) : next b n < 4096 := (valid_all n).2.2.2.2 b |>.1

theorem next_root (b : Bool) (n : Word) :
    (treeRow ⟨next b n, next_lt b n⟩).root = (treeRow n).root := by
  have he := (valid_all n).2.2.2.2 b |>.2
  simpa only [nextWord, Nat.mod_eq_of_lt (next_lt b n)] using he

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits
end
