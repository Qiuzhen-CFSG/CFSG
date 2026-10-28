module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Rows

/-!
# The 693-coset cover of the fixed max2 presentation

The fixed words and transitions replay `source/special_scan.json`.
Tree edges are word extensions; 17 special edges have subgroup tails and
relations derived from the 29 published relators. Every remaining edge is
obtained by cancelling known paths in an original relator loop.
The untrusted producer uses GAP only to discover this finite witness.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000

/-- All four signed transitions from each of the 693 representatives. -/
theorem transitions (i : Fin 693) (a : Letter Bool) :
    Holds level0Subgroup PresentedGroup.of representative
      ⟨i.val, [a], (destination i a).val⟩ := by
  by_cases h346 : i.val < 346
  · by_cases h173 : i.val < 173
    · by_cases h86 : i.val < 86
      · by_cases h43 : i.val < 43
        · by_cases h21 : i.val < 21
          · by_cases h10 : i.val < 10
            · by_cases h5 : i.val < 5
              · by_cases h2 : i.val < 2
                · by_cases h1 : i.val < 1
                  · have he : i = 0 := Fin.ext (by omega)
                    subst i
                    exact row0 a
                  · have he : i = 1 := Fin.ext (by omega)
                    subst i
                    exact row1 a
                · by_cases h3 : i.val < 3
                  · have he : i = 2 := Fin.ext (by omega)
                    subst i
                    exact row2 a
                  · by_cases h4 : i.val < 4
                    · have he : i = 3 := Fin.ext (by omega)
                      subst i
                      exact row3 a
                    · have he : i = 4 := Fin.ext (by omega)
                      subst i
                      exact row4 a
              · by_cases h7 : i.val < 7
                · by_cases h6 : i.val < 6
                  · have he : i = 5 := Fin.ext (by omega)
                    subst i
                    exact row5 a
                  · have he : i = 6 := Fin.ext (by omega)
                    subst i
                    exact row6 a
                · by_cases h8 : i.val < 8
                  · have he : i = 7 := Fin.ext (by omega)
                    subst i
                    exact row7 a
                  · by_cases h9 : i.val < 9
                    · have he : i = 8 := Fin.ext (by omega)
                      subst i
                      exact row8 a
                    · have he : i = 9 := Fin.ext (by omega)
                      subst i
                      exact row9 a
            · by_cases h15 : i.val < 15
              · by_cases h12 : i.val < 12
                · by_cases h11 : i.val < 11
                  · have he : i = 10 := Fin.ext (by omega)
                    subst i
                    exact row10 a
                  · have he : i = 11 := Fin.ext (by omega)
                    subst i
                    exact row11 a
                · by_cases h13 : i.val < 13
                  · have he : i = 12 := Fin.ext (by omega)
                    subst i
                    exact row12 a
                  · by_cases h14 : i.val < 14
                    · have he : i = 13 := Fin.ext (by omega)
                      subst i
                      exact row13 a
                    · have he : i = 14 := Fin.ext (by omega)
                      subst i
                      exact row14 a
              · by_cases h18 : i.val < 18
                · by_cases h16 : i.val < 16
                  · have he : i = 15 := Fin.ext (by omega)
                    subst i
                    exact row15 a
                  · by_cases h17 : i.val < 17
                    · have he : i = 16 := Fin.ext (by omega)
                      subst i
                      exact row16 a
                    · have he : i = 17 := Fin.ext (by omega)
                      subst i
                      exact row17 a
                · by_cases h19 : i.val < 19
                  · have he : i = 18 := Fin.ext (by omega)
                    subst i
                    exact row18 a
                  · by_cases h20 : i.val < 20
                    · have he : i = 19 := Fin.ext (by omega)
                      subst i
                      exact row19 a
                    · have he : i = 20 := Fin.ext (by omega)
                      subst i
                      exact row20 a
          · by_cases h32 : i.val < 32
            · by_cases h26 : i.val < 26
              · by_cases h23 : i.val < 23
                · by_cases h22 : i.val < 22
                  · have he : i = 21 := Fin.ext (by omega)
                    subst i
                    exact row21 a
                  · have he : i = 22 := Fin.ext (by omega)
                    subst i
                    exact row22 a
                · by_cases h24 : i.val < 24
                  · have he : i = 23 := Fin.ext (by omega)
                    subst i
                    exact row23 a
                  · by_cases h25 : i.val < 25
                    · have he : i = 24 := Fin.ext (by omega)
                      subst i
                      exact row24 a
                    · have he : i = 25 := Fin.ext (by omega)
                      subst i
                      exact row25 a
              · by_cases h29 : i.val < 29
                · by_cases h27 : i.val < 27
                  · have he : i = 26 := Fin.ext (by omega)
                    subst i
                    exact row26 a
                  · by_cases h28 : i.val < 28
                    · have he : i = 27 := Fin.ext (by omega)
                      subst i
                      exact row27 a
                    · have he : i = 28 := Fin.ext (by omega)
                      subst i
                      exact row28 a
                · by_cases h30 : i.val < 30
                  · have he : i = 29 := Fin.ext (by omega)
                    subst i
                    exact row29 a
                  · by_cases h31 : i.val < 31
                    · have he : i = 30 := Fin.ext (by omega)
                      subst i
                      exact row30 a
                    · have he : i = 31 := Fin.ext (by omega)
                      subst i
                      exact row31 a
            · by_cases h37 : i.val < 37
              · by_cases h34 : i.val < 34
                · by_cases h33 : i.val < 33
                  · have he : i = 32 := Fin.ext (by omega)
                    subst i
                    exact row32 a
                  · have he : i = 33 := Fin.ext (by omega)
                    subst i
                    exact row33 a
                · by_cases h35 : i.val < 35
                  · have he : i = 34 := Fin.ext (by omega)
                    subst i
                    exact row34 a
                  · by_cases h36 : i.val < 36
                    · have he : i = 35 := Fin.ext (by omega)
                      subst i
                      exact row35 a
                    · have he : i = 36 := Fin.ext (by omega)
                      subst i
                      exact row36 a
              · by_cases h40 : i.val < 40
                · by_cases h38 : i.val < 38
                  · have he : i = 37 := Fin.ext (by omega)
                    subst i
                    exact row37 a
                  · by_cases h39 : i.val < 39
                    · have he : i = 38 := Fin.ext (by omega)
                      subst i
                      exact row38 a
                    · have he : i = 39 := Fin.ext (by omega)
                      subst i
                      exact row39 a
                · by_cases h41 : i.val < 41
                  · have he : i = 40 := Fin.ext (by omega)
                    subst i
                    exact row40 a
                  · by_cases h42 : i.val < 42
                    · have he : i = 41 := Fin.ext (by omega)
                      subst i
                      exact row41 a
                    · have he : i = 42 := Fin.ext (by omega)
                      subst i
                      exact row42 a
        · by_cases h64 : i.val < 64
          · by_cases h53 : i.val < 53
            · by_cases h48 : i.val < 48
              · by_cases h45 : i.val < 45
                · by_cases h44 : i.val < 44
                  · have he : i = 43 := Fin.ext (by omega)
                    subst i
                    exact row43 a
                  · have he : i = 44 := Fin.ext (by omega)
                    subst i
                    exact row44 a
                · by_cases h46 : i.val < 46
                  · have he : i = 45 := Fin.ext (by omega)
                    subst i
                    exact row45 a
                  · by_cases h47 : i.val < 47
                    · have he : i = 46 := Fin.ext (by omega)
                      subst i
                      exact row46 a
                    · have he : i = 47 := Fin.ext (by omega)
                      subst i
                      exact row47 a
              · by_cases h50 : i.val < 50
                · by_cases h49 : i.val < 49
                  · have he : i = 48 := Fin.ext (by omega)
                    subst i
                    exact row48 a
                  · have he : i = 49 := Fin.ext (by omega)
                    subst i
                    exact row49 a
                · by_cases h51 : i.val < 51
                  · have he : i = 50 := Fin.ext (by omega)
                    subst i
                    exact row50 a
                  · by_cases h52 : i.val < 52
                    · have he : i = 51 := Fin.ext (by omega)
                      subst i
                      exact row51 a
                    · have he : i = 52 := Fin.ext (by omega)
                      subst i
                      exact row52 a
            · by_cases h58 : i.val < 58
              · by_cases h55 : i.val < 55
                · by_cases h54 : i.val < 54
                  · have he : i = 53 := Fin.ext (by omega)
                    subst i
                    exact row53 a
                  · have he : i = 54 := Fin.ext (by omega)
                    subst i
                    exact row54 a
                · by_cases h56 : i.val < 56
                  · have he : i = 55 := Fin.ext (by omega)
                    subst i
                    exact row55 a
                  · by_cases h57 : i.val < 57
                    · have he : i = 56 := Fin.ext (by omega)
                      subst i
                      exact row56 a
                    · have he : i = 57 := Fin.ext (by omega)
                      subst i
                      exact row57 a
              · by_cases h61 : i.val < 61
                · by_cases h59 : i.val < 59
                  · have he : i = 58 := Fin.ext (by omega)
                    subst i
                    exact row58 a
                  · by_cases h60 : i.val < 60
                    · have he : i = 59 := Fin.ext (by omega)
                      subst i
                      exact row59 a
                    · have he : i = 60 := Fin.ext (by omega)
                      subst i
                      exact row60 a
                · by_cases h62 : i.val < 62
                  · have he : i = 61 := Fin.ext (by omega)
                    subst i
                    exact row61 a
                  · by_cases h63 : i.val < 63
                    · have he : i = 62 := Fin.ext (by omega)
                      subst i
                      exact row62 a
                    · have he : i = 63 := Fin.ext (by omega)
                      subst i
                      exact row63 a
          · by_cases h75 : i.val < 75
            · by_cases h69 : i.val < 69
              · by_cases h66 : i.val < 66
                · by_cases h65 : i.val < 65
                  · have he : i = 64 := Fin.ext (by omega)
                    subst i
                    exact row64 a
                  · have he : i = 65 := Fin.ext (by omega)
                    subst i
                    exact row65 a
                · by_cases h67 : i.val < 67
                  · have he : i = 66 := Fin.ext (by omega)
                    subst i
                    exact row66 a
                  · by_cases h68 : i.val < 68
                    · have he : i = 67 := Fin.ext (by omega)
                      subst i
                      exact row67 a
                    · have he : i = 68 := Fin.ext (by omega)
                      subst i
                      exact row68 a
              · by_cases h72 : i.val < 72
                · by_cases h70 : i.val < 70
                  · have he : i = 69 := Fin.ext (by omega)
                    subst i
                    exact row69 a
                  · by_cases h71 : i.val < 71
                    · have he : i = 70 := Fin.ext (by omega)
                      subst i
                      exact row70 a
                    · have he : i = 71 := Fin.ext (by omega)
                      subst i
                      exact row71 a
                · by_cases h73 : i.val < 73
                  · have he : i = 72 := Fin.ext (by omega)
                    subst i
                    exact row72 a
                  · by_cases h74 : i.val < 74
                    · have he : i = 73 := Fin.ext (by omega)
                      subst i
                      exact row73 a
                    · have he : i = 74 := Fin.ext (by omega)
                      subst i
                      exact row74 a
            · by_cases h80 : i.val < 80
              · by_cases h77 : i.val < 77
                · by_cases h76 : i.val < 76
                  · have he : i = 75 := Fin.ext (by omega)
                    subst i
                    exact row75 a
                  · have he : i = 76 := Fin.ext (by omega)
                    subst i
                    exact row76 a
                · by_cases h78 : i.val < 78
                  · have he : i = 77 := Fin.ext (by omega)
                    subst i
                    exact row77 a
                  · by_cases h79 : i.val < 79
                    · have he : i = 78 := Fin.ext (by omega)
                      subst i
                      exact row78 a
                    · have he : i = 79 := Fin.ext (by omega)
                      subst i
                      exact row79 a
              · by_cases h83 : i.val < 83
                · by_cases h81 : i.val < 81
                  · have he : i = 80 := Fin.ext (by omega)
                    subst i
                    exact row80 a
                  · by_cases h82 : i.val < 82
                    · have he : i = 81 := Fin.ext (by omega)
                      subst i
                      exact row81 a
                    · have he : i = 82 := Fin.ext (by omega)
                      subst i
                      exact row82 a
                · by_cases h84 : i.val < 84
                  · have he : i = 83 := Fin.ext (by omega)
                    subst i
                    exact row83 a
                  · by_cases h85 : i.val < 85
                    · have he : i = 84 := Fin.ext (by omega)
                      subst i
                      exact row84 a
                    · have he : i = 85 := Fin.ext (by omega)
                      subst i
                      exact row85 a
      · by_cases h129 : i.val < 129
        · by_cases h107 : i.val < 107
          · by_cases h96 : i.val < 96
            · by_cases h91 : i.val < 91
              · by_cases h88 : i.val < 88
                · by_cases h87 : i.val < 87
                  · have he : i = 86 := Fin.ext (by omega)
                    subst i
                    exact row86 a
                  · have he : i = 87 := Fin.ext (by omega)
                    subst i
                    exact row87 a
                · by_cases h89 : i.val < 89
                  · have he : i = 88 := Fin.ext (by omega)
                    subst i
                    exact row88 a
                  · by_cases h90 : i.val < 90
                    · have he : i = 89 := Fin.ext (by omega)
                      subst i
                      exact row89 a
                    · have he : i = 90 := Fin.ext (by omega)
                      subst i
                      exact row90 a
              · by_cases h93 : i.val < 93
                · by_cases h92 : i.val < 92
                  · have he : i = 91 := Fin.ext (by omega)
                    subst i
                    exact row91 a
                  · have he : i = 92 := Fin.ext (by omega)
                    subst i
                    exact row92 a
                · by_cases h94 : i.val < 94
                  · have he : i = 93 := Fin.ext (by omega)
                    subst i
                    exact row93 a
                  · by_cases h95 : i.val < 95
                    · have he : i = 94 := Fin.ext (by omega)
                      subst i
                      exact row94 a
                    · have he : i = 95 := Fin.ext (by omega)
                      subst i
                      exact row95 a
            · by_cases h101 : i.val < 101
              · by_cases h98 : i.val < 98
                · by_cases h97 : i.val < 97
                  · have he : i = 96 := Fin.ext (by omega)
                    subst i
                    exact row96 a
                  · have he : i = 97 := Fin.ext (by omega)
                    subst i
                    exact row97 a
                · by_cases h99 : i.val < 99
                  · have he : i = 98 := Fin.ext (by omega)
                    subst i
                    exact row98 a
                  · by_cases h100 : i.val < 100
                    · have he : i = 99 := Fin.ext (by omega)
                      subst i
                      exact row99 a
                    · have he : i = 100 := Fin.ext (by omega)
                      subst i
                      exact row100 a
              · by_cases h104 : i.val < 104
                · by_cases h102 : i.val < 102
                  · have he : i = 101 := Fin.ext (by omega)
                    subst i
                    exact row101 a
                  · by_cases h103 : i.val < 103
                    · have he : i = 102 := Fin.ext (by omega)
                      subst i
                      exact row102 a
                    · have he : i = 103 := Fin.ext (by omega)
                      subst i
                      exact row103 a
                · by_cases h105 : i.val < 105
                  · have he : i = 104 := Fin.ext (by omega)
                    subst i
                    exact row104 a
                  · by_cases h106 : i.val < 106
                    · have he : i = 105 := Fin.ext (by omega)
                      subst i
                      exact row105 a
                    · have he : i = 106 := Fin.ext (by omega)
                      subst i
                      exact row106 a
          · by_cases h118 : i.val < 118
            · by_cases h112 : i.val < 112
              · by_cases h109 : i.val < 109
                · by_cases h108 : i.val < 108
                  · have he : i = 107 := Fin.ext (by omega)
                    subst i
                    exact row107 a
                  · have he : i = 108 := Fin.ext (by omega)
                    subst i
                    exact row108 a
                · by_cases h110 : i.val < 110
                  · have he : i = 109 := Fin.ext (by omega)
                    subst i
                    exact row109 a
                  · by_cases h111 : i.val < 111
                    · have he : i = 110 := Fin.ext (by omega)
                      subst i
                      exact row110 a
                    · have he : i = 111 := Fin.ext (by omega)
                      subst i
                      exact row111 a
              · by_cases h115 : i.val < 115
                · by_cases h113 : i.val < 113
                  · have he : i = 112 := Fin.ext (by omega)
                    subst i
                    exact row112 a
                  · by_cases h114 : i.val < 114
                    · have he : i = 113 := Fin.ext (by omega)
                      subst i
                      exact row113 a
                    · have he : i = 114 := Fin.ext (by omega)
                      subst i
                      exact row114 a
                · by_cases h116 : i.val < 116
                  · have he : i = 115 := Fin.ext (by omega)
                    subst i
                    exact row115 a
                  · by_cases h117 : i.val < 117
                    · have he : i = 116 := Fin.ext (by omega)
                      subst i
                      exact row116 a
                    · have he : i = 117 := Fin.ext (by omega)
                      subst i
                      exact row117 a
            · by_cases h123 : i.val < 123
              · by_cases h120 : i.val < 120
                · by_cases h119 : i.val < 119
                  · have he : i = 118 := Fin.ext (by omega)
                    subst i
                    exact row118 a
                  · have he : i = 119 := Fin.ext (by omega)
                    subst i
                    exact row119 a
                · by_cases h121 : i.val < 121
                  · have he : i = 120 := Fin.ext (by omega)
                    subst i
                    exact row120 a
                  · by_cases h122 : i.val < 122
                    · have he : i = 121 := Fin.ext (by omega)
                      subst i
                      exact row121 a
                    · have he : i = 122 := Fin.ext (by omega)
                      subst i
                      exact row122 a
              · by_cases h126 : i.val < 126
                · by_cases h124 : i.val < 124
                  · have he : i = 123 := Fin.ext (by omega)
                    subst i
                    exact row123 a
                  · by_cases h125 : i.val < 125
                    · have he : i = 124 := Fin.ext (by omega)
                      subst i
                      exact row124 a
                    · have he : i = 125 := Fin.ext (by omega)
                      subst i
                      exact row125 a
                · by_cases h127 : i.val < 127
                  · have he : i = 126 := Fin.ext (by omega)
                    subst i
                    exact row126 a
                  · by_cases h128 : i.val < 128
                    · have he : i = 127 := Fin.ext (by omega)
                      subst i
                      exact row127 a
                    · have he : i = 128 := Fin.ext (by omega)
                      subst i
                      exact row128 a
        · by_cases h151 : i.val < 151
          · by_cases h140 : i.val < 140
            · by_cases h134 : i.val < 134
              · by_cases h131 : i.val < 131
                · by_cases h130 : i.val < 130
                  · have he : i = 129 := Fin.ext (by omega)
                    subst i
                    exact row129 a
                  · have he : i = 130 := Fin.ext (by omega)
                    subst i
                    exact row130 a
                · by_cases h132 : i.val < 132
                  · have he : i = 131 := Fin.ext (by omega)
                    subst i
                    exact row131 a
                  · by_cases h133 : i.val < 133
                    · have he : i = 132 := Fin.ext (by omega)
                      subst i
                      exact row132 a
                    · have he : i = 133 := Fin.ext (by omega)
                      subst i
                      exact row133 a
              · by_cases h137 : i.val < 137
                · by_cases h135 : i.val < 135
                  · have he : i = 134 := Fin.ext (by omega)
                    subst i
                    exact row134 a
                  · by_cases h136 : i.val < 136
                    · have he : i = 135 := Fin.ext (by omega)
                      subst i
                      exact row135 a
                    · have he : i = 136 := Fin.ext (by omega)
                      subst i
                      exact row136 a
                · by_cases h138 : i.val < 138
                  · have he : i = 137 := Fin.ext (by omega)
                    subst i
                    exact row137 a
                  · by_cases h139 : i.val < 139
                    · have he : i = 138 := Fin.ext (by omega)
                      subst i
                      exact row138 a
                    · have he : i = 139 := Fin.ext (by omega)
                      subst i
                      exact row139 a
            · by_cases h145 : i.val < 145
              · by_cases h142 : i.val < 142
                · by_cases h141 : i.val < 141
                  · have he : i = 140 := Fin.ext (by omega)
                    subst i
                    exact row140 a
                  · have he : i = 141 := Fin.ext (by omega)
                    subst i
                    exact row141 a
                · by_cases h143 : i.val < 143
                  · have he : i = 142 := Fin.ext (by omega)
                    subst i
                    exact row142 a
                  · by_cases h144 : i.val < 144
                    · have he : i = 143 := Fin.ext (by omega)
                      subst i
                      exact row143 a
                    · have he : i = 144 := Fin.ext (by omega)
                      subst i
                      exact row144 a
              · by_cases h148 : i.val < 148
                · by_cases h146 : i.val < 146
                  · have he : i = 145 := Fin.ext (by omega)
                    subst i
                    exact row145 a
                  · by_cases h147 : i.val < 147
                    · have he : i = 146 := Fin.ext (by omega)
                      subst i
                      exact row146 a
                    · have he : i = 147 := Fin.ext (by omega)
                      subst i
                      exact row147 a
                · by_cases h149 : i.val < 149
                  · have he : i = 148 := Fin.ext (by omega)
                    subst i
                    exact row148 a
                  · by_cases h150 : i.val < 150
                    · have he : i = 149 := Fin.ext (by omega)
                      subst i
                      exact row149 a
                    · have he : i = 150 := Fin.ext (by omega)
                      subst i
                      exact row150 a
          · by_cases h162 : i.val < 162
            · by_cases h156 : i.val < 156
              · by_cases h153 : i.val < 153
                · by_cases h152 : i.val < 152
                  · have he : i = 151 := Fin.ext (by omega)
                    subst i
                    exact row151 a
                  · have he : i = 152 := Fin.ext (by omega)
                    subst i
                    exact row152 a
                · by_cases h154 : i.val < 154
                  · have he : i = 153 := Fin.ext (by omega)
                    subst i
                    exact row153 a
                  · by_cases h155 : i.val < 155
                    · have he : i = 154 := Fin.ext (by omega)
                      subst i
                      exact row154 a
                    · have he : i = 155 := Fin.ext (by omega)
                      subst i
                      exact row155 a
              · by_cases h159 : i.val < 159
                · by_cases h157 : i.val < 157
                  · have he : i = 156 := Fin.ext (by omega)
                    subst i
                    exact row156 a
                  · by_cases h158 : i.val < 158
                    · have he : i = 157 := Fin.ext (by omega)
                      subst i
                      exact row157 a
                    · have he : i = 158 := Fin.ext (by omega)
                      subst i
                      exact row158 a
                · by_cases h160 : i.val < 160
                  · have he : i = 159 := Fin.ext (by omega)
                    subst i
                    exact row159 a
                  · by_cases h161 : i.val < 161
                    · have he : i = 160 := Fin.ext (by omega)
                      subst i
                      exact row160 a
                    · have he : i = 161 := Fin.ext (by omega)
                      subst i
                      exact row161 a
            · by_cases h167 : i.val < 167
              · by_cases h164 : i.val < 164
                · by_cases h163 : i.val < 163
                  · have he : i = 162 := Fin.ext (by omega)
                    subst i
                    exact row162 a
                  · have he : i = 163 := Fin.ext (by omega)
                    subst i
                    exact row163 a
                · by_cases h165 : i.val < 165
                  · have he : i = 164 := Fin.ext (by omega)
                    subst i
                    exact row164 a
                  · by_cases h166 : i.val < 166
                    · have he : i = 165 := Fin.ext (by omega)
                      subst i
                      exact row165 a
                    · have he : i = 166 := Fin.ext (by omega)
                      subst i
                      exact row166 a
              · by_cases h170 : i.val < 170
                · by_cases h168 : i.val < 168
                  · have he : i = 167 := Fin.ext (by omega)
                    subst i
                    exact row167 a
                  · by_cases h169 : i.val < 169
                    · have he : i = 168 := Fin.ext (by omega)
                      subst i
                      exact row168 a
                    · have he : i = 169 := Fin.ext (by omega)
                      subst i
                      exact row169 a
                · by_cases h171 : i.val < 171
                  · have he : i = 170 := Fin.ext (by omega)
                    subst i
                    exact row170 a
                  · by_cases h172 : i.val < 172
                    · have he : i = 171 := Fin.ext (by omega)
                      subst i
                      exact row171 a
                    · have he : i = 172 := Fin.ext (by omega)
                      subst i
                      exact row172 a
    · by_cases h259 : i.val < 259
      · by_cases h216 : i.val < 216
        · by_cases h194 : i.val < 194
          · by_cases h183 : i.val < 183
            · by_cases h178 : i.val < 178
              · by_cases h175 : i.val < 175
                · by_cases h174 : i.val < 174
                  · have he : i = 173 := Fin.ext (by omega)
                    subst i
                    exact row173 a
                  · have he : i = 174 := Fin.ext (by omega)
                    subst i
                    exact row174 a
                · by_cases h176 : i.val < 176
                  · have he : i = 175 := Fin.ext (by omega)
                    subst i
                    exact row175 a
                  · by_cases h177 : i.val < 177
                    · have he : i = 176 := Fin.ext (by omega)
                      subst i
                      exact row176 a
                    · have he : i = 177 := Fin.ext (by omega)
                      subst i
                      exact row177 a
              · by_cases h180 : i.val < 180
                · by_cases h179 : i.val < 179
                  · have he : i = 178 := Fin.ext (by omega)
                    subst i
                    exact row178 a
                  · have he : i = 179 := Fin.ext (by omega)
                    subst i
                    exact row179 a
                · by_cases h181 : i.val < 181
                  · have he : i = 180 := Fin.ext (by omega)
                    subst i
                    exact row180 a
                  · by_cases h182 : i.val < 182
                    · have he : i = 181 := Fin.ext (by omega)
                      subst i
                      exact row181 a
                    · have he : i = 182 := Fin.ext (by omega)
                      subst i
                      exact row182 a
            · by_cases h188 : i.val < 188
              · by_cases h185 : i.val < 185
                · by_cases h184 : i.val < 184
                  · have he : i = 183 := Fin.ext (by omega)
                    subst i
                    exact row183 a
                  · have he : i = 184 := Fin.ext (by omega)
                    subst i
                    exact row184 a
                · by_cases h186 : i.val < 186
                  · have he : i = 185 := Fin.ext (by omega)
                    subst i
                    exact row185 a
                  · by_cases h187 : i.val < 187
                    · have he : i = 186 := Fin.ext (by omega)
                      subst i
                      exact row186 a
                    · have he : i = 187 := Fin.ext (by omega)
                      subst i
                      exact row187 a
              · by_cases h191 : i.val < 191
                · by_cases h189 : i.val < 189
                  · have he : i = 188 := Fin.ext (by omega)
                    subst i
                    exact row188 a
                  · by_cases h190 : i.val < 190
                    · have he : i = 189 := Fin.ext (by omega)
                      subst i
                      exact row189 a
                    · have he : i = 190 := Fin.ext (by omega)
                      subst i
                      exact row190 a
                · by_cases h192 : i.val < 192
                  · have he : i = 191 := Fin.ext (by omega)
                    subst i
                    exact row191 a
                  · by_cases h193 : i.val < 193
                    · have he : i = 192 := Fin.ext (by omega)
                      subst i
                      exact row192 a
                    · have he : i = 193 := Fin.ext (by omega)
                      subst i
                      exact row193 a
          · by_cases h205 : i.val < 205
            · by_cases h199 : i.val < 199
              · by_cases h196 : i.val < 196
                · by_cases h195 : i.val < 195
                  · have he : i = 194 := Fin.ext (by omega)
                    subst i
                    exact row194 a
                  · have he : i = 195 := Fin.ext (by omega)
                    subst i
                    exact row195 a
                · by_cases h197 : i.val < 197
                  · have he : i = 196 := Fin.ext (by omega)
                    subst i
                    exact row196 a
                  · by_cases h198 : i.val < 198
                    · have he : i = 197 := Fin.ext (by omega)
                      subst i
                      exact row197 a
                    · have he : i = 198 := Fin.ext (by omega)
                      subst i
                      exact row198 a
              · by_cases h202 : i.val < 202
                · by_cases h200 : i.val < 200
                  · have he : i = 199 := Fin.ext (by omega)
                    subst i
                    exact row199 a
                  · by_cases h201 : i.val < 201
                    · have he : i = 200 := Fin.ext (by omega)
                      subst i
                      exact row200 a
                    · have he : i = 201 := Fin.ext (by omega)
                      subst i
                      exact row201 a
                · by_cases h203 : i.val < 203
                  · have he : i = 202 := Fin.ext (by omega)
                    subst i
                    exact row202 a
                  · by_cases h204 : i.val < 204
                    · have he : i = 203 := Fin.ext (by omega)
                      subst i
                      exact row203 a
                    · have he : i = 204 := Fin.ext (by omega)
                      subst i
                      exact row204 a
            · by_cases h210 : i.val < 210
              · by_cases h207 : i.val < 207
                · by_cases h206 : i.val < 206
                  · have he : i = 205 := Fin.ext (by omega)
                    subst i
                    exact row205 a
                  · have he : i = 206 := Fin.ext (by omega)
                    subst i
                    exact row206 a
                · by_cases h208 : i.val < 208
                  · have he : i = 207 := Fin.ext (by omega)
                    subst i
                    exact row207 a
                  · by_cases h209 : i.val < 209
                    · have he : i = 208 := Fin.ext (by omega)
                      subst i
                      exact row208 a
                    · have he : i = 209 := Fin.ext (by omega)
                      subst i
                      exact row209 a
              · by_cases h213 : i.val < 213
                · by_cases h211 : i.val < 211
                  · have he : i = 210 := Fin.ext (by omega)
                    subst i
                    exact row210 a
                  · by_cases h212 : i.val < 212
                    · have he : i = 211 := Fin.ext (by omega)
                      subst i
                      exact row211 a
                    · have he : i = 212 := Fin.ext (by omega)
                      subst i
                      exact row212 a
                · by_cases h214 : i.val < 214
                  · have he : i = 213 := Fin.ext (by omega)
                    subst i
                    exact row213 a
                  · by_cases h215 : i.val < 215
                    · have he : i = 214 := Fin.ext (by omega)
                      subst i
                      exact row214 a
                    · have he : i = 215 := Fin.ext (by omega)
                      subst i
                      exact row215 a
        · by_cases h237 : i.val < 237
          · by_cases h226 : i.val < 226
            · by_cases h221 : i.val < 221
              · by_cases h218 : i.val < 218
                · by_cases h217 : i.val < 217
                  · have he : i = 216 := Fin.ext (by omega)
                    subst i
                    exact row216 a
                  · have he : i = 217 := Fin.ext (by omega)
                    subst i
                    exact row217 a
                · by_cases h219 : i.val < 219
                  · have he : i = 218 := Fin.ext (by omega)
                    subst i
                    exact row218 a
                  · by_cases h220 : i.val < 220
                    · have he : i = 219 := Fin.ext (by omega)
                      subst i
                      exact row219 a
                    · have he : i = 220 := Fin.ext (by omega)
                      subst i
                      exact row220 a
              · by_cases h223 : i.val < 223
                · by_cases h222 : i.val < 222
                  · have he : i = 221 := Fin.ext (by omega)
                    subst i
                    exact row221 a
                  · have he : i = 222 := Fin.ext (by omega)
                    subst i
                    exact row222 a
                · by_cases h224 : i.val < 224
                  · have he : i = 223 := Fin.ext (by omega)
                    subst i
                    exact row223 a
                  · by_cases h225 : i.val < 225
                    · have he : i = 224 := Fin.ext (by omega)
                      subst i
                      exact row224 a
                    · have he : i = 225 := Fin.ext (by omega)
                      subst i
                      exact row225 a
            · by_cases h231 : i.val < 231
              · by_cases h228 : i.val < 228
                · by_cases h227 : i.val < 227
                  · have he : i = 226 := Fin.ext (by omega)
                    subst i
                    exact row226 a
                  · have he : i = 227 := Fin.ext (by omega)
                    subst i
                    exact row227 a
                · by_cases h229 : i.val < 229
                  · have he : i = 228 := Fin.ext (by omega)
                    subst i
                    exact row228 a
                  · by_cases h230 : i.val < 230
                    · have he : i = 229 := Fin.ext (by omega)
                      subst i
                      exact row229 a
                    · have he : i = 230 := Fin.ext (by omega)
                      subst i
                      exact row230 a
              · by_cases h234 : i.val < 234
                · by_cases h232 : i.val < 232
                  · have he : i = 231 := Fin.ext (by omega)
                    subst i
                    exact row231 a
                  · by_cases h233 : i.val < 233
                    · have he : i = 232 := Fin.ext (by omega)
                      subst i
                      exact row232 a
                    · have he : i = 233 := Fin.ext (by omega)
                      subst i
                      exact row233 a
                · by_cases h235 : i.val < 235
                  · have he : i = 234 := Fin.ext (by omega)
                    subst i
                    exact row234 a
                  · by_cases h236 : i.val < 236
                    · have he : i = 235 := Fin.ext (by omega)
                      subst i
                      exact row235 a
                    · have he : i = 236 := Fin.ext (by omega)
                      subst i
                      exact row236 a
          · by_cases h248 : i.val < 248
            · by_cases h242 : i.val < 242
              · by_cases h239 : i.val < 239
                · by_cases h238 : i.val < 238
                  · have he : i = 237 := Fin.ext (by omega)
                    subst i
                    exact row237 a
                  · have he : i = 238 := Fin.ext (by omega)
                    subst i
                    exact row238 a
                · by_cases h240 : i.val < 240
                  · have he : i = 239 := Fin.ext (by omega)
                    subst i
                    exact row239 a
                  · by_cases h241 : i.val < 241
                    · have he : i = 240 := Fin.ext (by omega)
                      subst i
                      exact row240 a
                    · have he : i = 241 := Fin.ext (by omega)
                      subst i
                      exact row241 a
              · by_cases h245 : i.val < 245
                · by_cases h243 : i.val < 243
                  · have he : i = 242 := Fin.ext (by omega)
                    subst i
                    exact row242 a
                  · by_cases h244 : i.val < 244
                    · have he : i = 243 := Fin.ext (by omega)
                      subst i
                      exact row243 a
                    · have he : i = 244 := Fin.ext (by omega)
                      subst i
                      exact row244 a
                · by_cases h246 : i.val < 246
                  · have he : i = 245 := Fin.ext (by omega)
                    subst i
                    exact row245 a
                  · by_cases h247 : i.val < 247
                    · have he : i = 246 := Fin.ext (by omega)
                      subst i
                      exact row246 a
                    · have he : i = 247 := Fin.ext (by omega)
                      subst i
                      exact row247 a
            · by_cases h253 : i.val < 253
              · by_cases h250 : i.val < 250
                · by_cases h249 : i.val < 249
                  · have he : i = 248 := Fin.ext (by omega)
                    subst i
                    exact row248 a
                  · have he : i = 249 := Fin.ext (by omega)
                    subst i
                    exact row249 a
                · by_cases h251 : i.val < 251
                  · have he : i = 250 := Fin.ext (by omega)
                    subst i
                    exact row250 a
                  · by_cases h252 : i.val < 252
                    · have he : i = 251 := Fin.ext (by omega)
                      subst i
                      exact row251 a
                    · have he : i = 252 := Fin.ext (by omega)
                      subst i
                      exact row252 a
              · by_cases h256 : i.val < 256
                · by_cases h254 : i.val < 254
                  · have he : i = 253 := Fin.ext (by omega)
                    subst i
                    exact row253 a
                  · by_cases h255 : i.val < 255
                    · have he : i = 254 := Fin.ext (by omega)
                      subst i
                      exact row254 a
                    · have he : i = 255 := Fin.ext (by omega)
                      subst i
                      exact row255 a
                · by_cases h257 : i.val < 257
                  · have he : i = 256 := Fin.ext (by omega)
                    subst i
                    exact row256 a
                  · by_cases h258 : i.val < 258
                    · have he : i = 257 := Fin.ext (by omega)
                      subst i
                      exact row257 a
                    · have he : i = 258 := Fin.ext (by omega)
                      subst i
                      exact row258 a
      · by_cases h302 : i.val < 302
        · by_cases h280 : i.val < 280
          · by_cases h269 : i.val < 269
            · by_cases h264 : i.val < 264
              · by_cases h261 : i.val < 261
                · by_cases h260 : i.val < 260
                  · have he : i = 259 := Fin.ext (by omega)
                    subst i
                    exact row259 a
                  · have he : i = 260 := Fin.ext (by omega)
                    subst i
                    exact row260 a
                · by_cases h262 : i.val < 262
                  · have he : i = 261 := Fin.ext (by omega)
                    subst i
                    exact row261 a
                  · by_cases h263 : i.val < 263
                    · have he : i = 262 := Fin.ext (by omega)
                      subst i
                      exact row262 a
                    · have he : i = 263 := Fin.ext (by omega)
                      subst i
                      exact row263 a
              · by_cases h266 : i.val < 266
                · by_cases h265 : i.val < 265
                  · have he : i = 264 := Fin.ext (by omega)
                    subst i
                    exact row264 a
                  · have he : i = 265 := Fin.ext (by omega)
                    subst i
                    exact row265 a
                · by_cases h267 : i.val < 267
                  · have he : i = 266 := Fin.ext (by omega)
                    subst i
                    exact row266 a
                  · by_cases h268 : i.val < 268
                    · have he : i = 267 := Fin.ext (by omega)
                      subst i
                      exact row267 a
                    · have he : i = 268 := Fin.ext (by omega)
                      subst i
                      exact row268 a
            · by_cases h274 : i.val < 274
              · by_cases h271 : i.val < 271
                · by_cases h270 : i.val < 270
                  · have he : i = 269 := Fin.ext (by omega)
                    subst i
                    exact row269 a
                  · have he : i = 270 := Fin.ext (by omega)
                    subst i
                    exact row270 a
                · by_cases h272 : i.val < 272
                  · have he : i = 271 := Fin.ext (by omega)
                    subst i
                    exact row271 a
                  · by_cases h273 : i.val < 273
                    · have he : i = 272 := Fin.ext (by omega)
                      subst i
                      exact row272 a
                    · have he : i = 273 := Fin.ext (by omega)
                      subst i
                      exact row273 a
              · by_cases h277 : i.val < 277
                · by_cases h275 : i.val < 275
                  · have he : i = 274 := Fin.ext (by omega)
                    subst i
                    exact row274 a
                  · by_cases h276 : i.val < 276
                    · have he : i = 275 := Fin.ext (by omega)
                      subst i
                      exact row275 a
                    · have he : i = 276 := Fin.ext (by omega)
                      subst i
                      exact row276 a
                · by_cases h278 : i.val < 278
                  · have he : i = 277 := Fin.ext (by omega)
                    subst i
                    exact row277 a
                  · by_cases h279 : i.val < 279
                    · have he : i = 278 := Fin.ext (by omega)
                      subst i
                      exact row278 a
                    · have he : i = 279 := Fin.ext (by omega)
                      subst i
                      exact row279 a
          · by_cases h291 : i.val < 291
            · by_cases h285 : i.val < 285
              · by_cases h282 : i.val < 282
                · by_cases h281 : i.val < 281
                  · have he : i = 280 := Fin.ext (by omega)
                    subst i
                    exact row280 a
                  · have he : i = 281 := Fin.ext (by omega)
                    subst i
                    exact row281 a
                · by_cases h283 : i.val < 283
                  · have he : i = 282 := Fin.ext (by omega)
                    subst i
                    exact row282 a
                  · by_cases h284 : i.val < 284
                    · have he : i = 283 := Fin.ext (by omega)
                      subst i
                      exact row283 a
                    · have he : i = 284 := Fin.ext (by omega)
                      subst i
                      exact row284 a
              · by_cases h288 : i.val < 288
                · by_cases h286 : i.val < 286
                  · have he : i = 285 := Fin.ext (by omega)
                    subst i
                    exact row285 a
                  · by_cases h287 : i.val < 287
                    · have he : i = 286 := Fin.ext (by omega)
                      subst i
                      exact row286 a
                    · have he : i = 287 := Fin.ext (by omega)
                      subst i
                      exact row287 a
                · by_cases h289 : i.val < 289
                  · have he : i = 288 := Fin.ext (by omega)
                    subst i
                    exact row288 a
                  · by_cases h290 : i.val < 290
                    · have he : i = 289 := Fin.ext (by omega)
                      subst i
                      exact row289 a
                    · have he : i = 290 := Fin.ext (by omega)
                      subst i
                      exact row290 a
            · by_cases h296 : i.val < 296
              · by_cases h293 : i.val < 293
                · by_cases h292 : i.val < 292
                  · have he : i = 291 := Fin.ext (by omega)
                    subst i
                    exact row291 a
                  · have he : i = 292 := Fin.ext (by omega)
                    subst i
                    exact row292 a
                · by_cases h294 : i.val < 294
                  · have he : i = 293 := Fin.ext (by omega)
                    subst i
                    exact row293 a
                  · by_cases h295 : i.val < 295
                    · have he : i = 294 := Fin.ext (by omega)
                      subst i
                      exact row294 a
                    · have he : i = 295 := Fin.ext (by omega)
                      subst i
                      exact row295 a
              · by_cases h299 : i.val < 299
                · by_cases h297 : i.val < 297
                  · have he : i = 296 := Fin.ext (by omega)
                    subst i
                    exact row296 a
                  · by_cases h298 : i.val < 298
                    · have he : i = 297 := Fin.ext (by omega)
                      subst i
                      exact row297 a
                    · have he : i = 298 := Fin.ext (by omega)
                      subst i
                      exact row298 a
                · by_cases h300 : i.val < 300
                  · have he : i = 299 := Fin.ext (by omega)
                    subst i
                    exact row299 a
                  · by_cases h301 : i.val < 301
                    · have he : i = 300 := Fin.ext (by omega)
                      subst i
                      exact row300 a
                    · have he : i = 301 := Fin.ext (by omega)
                      subst i
                      exact row301 a
        · by_cases h324 : i.val < 324
          · by_cases h313 : i.val < 313
            · by_cases h307 : i.val < 307
              · by_cases h304 : i.val < 304
                · by_cases h303 : i.val < 303
                  · have he : i = 302 := Fin.ext (by omega)
                    subst i
                    exact row302 a
                  · have he : i = 303 := Fin.ext (by omega)
                    subst i
                    exact row303 a
                · by_cases h305 : i.val < 305
                  · have he : i = 304 := Fin.ext (by omega)
                    subst i
                    exact row304 a
                  · by_cases h306 : i.val < 306
                    · have he : i = 305 := Fin.ext (by omega)
                      subst i
                      exact row305 a
                    · have he : i = 306 := Fin.ext (by omega)
                      subst i
                      exact row306 a
              · by_cases h310 : i.val < 310
                · by_cases h308 : i.val < 308
                  · have he : i = 307 := Fin.ext (by omega)
                    subst i
                    exact row307 a
                  · by_cases h309 : i.val < 309
                    · have he : i = 308 := Fin.ext (by omega)
                      subst i
                      exact row308 a
                    · have he : i = 309 := Fin.ext (by omega)
                      subst i
                      exact row309 a
                · by_cases h311 : i.val < 311
                  · have he : i = 310 := Fin.ext (by omega)
                    subst i
                    exact row310 a
                  · by_cases h312 : i.val < 312
                    · have he : i = 311 := Fin.ext (by omega)
                      subst i
                      exact row311 a
                    · have he : i = 312 := Fin.ext (by omega)
                      subst i
                      exact row312 a
            · by_cases h318 : i.val < 318
              · by_cases h315 : i.val < 315
                · by_cases h314 : i.val < 314
                  · have he : i = 313 := Fin.ext (by omega)
                    subst i
                    exact row313 a
                  · have he : i = 314 := Fin.ext (by omega)
                    subst i
                    exact row314 a
                · by_cases h316 : i.val < 316
                  · have he : i = 315 := Fin.ext (by omega)
                    subst i
                    exact row315 a
                  · by_cases h317 : i.val < 317
                    · have he : i = 316 := Fin.ext (by omega)
                      subst i
                      exact row316 a
                    · have he : i = 317 := Fin.ext (by omega)
                      subst i
                      exact row317 a
              · by_cases h321 : i.val < 321
                · by_cases h319 : i.val < 319
                  · have he : i = 318 := Fin.ext (by omega)
                    subst i
                    exact row318 a
                  · by_cases h320 : i.val < 320
                    · have he : i = 319 := Fin.ext (by omega)
                      subst i
                      exact row319 a
                    · have he : i = 320 := Fin.ext (by omega)
                      subst i
                      exact row320 a
                · by_cases h322 : i.val < 322
                  · have he : i = 321 := Fin.ext (by omega)
                    subst i
                    exact row321 a
                  · by_cases h323 : i.val < 323
                    · have he : i = 322 := Fin.ext (by omega)
                      subst i
                      exact row322 a
                    · have he : i = 323 := Fin.ext (by omega)
                      subst i
                      exact row323 a
          · by_cases h335 : i.val < 335
            · by_cases h329 : i.val < 329
              · by_cases h326 : i.val < 326
                · by_cases h325 : i.val < 325
                  · have he : i = 324 := Fin.ext (by omega)
                    subst i
                    exact row324 a
                  · have he : i = 325 := Fin.ext (by omega)
                    subst i
                    exact row325 a
                · by_cases h327 : i.val < 327
                  · have he : i = 326 := Fin.ext (by omega)
                    subst i
                    exact row326 a
                  · by_cases h328 : i.val < 328
                    · have he : i = 327 := Fin.ext (by omega)
                      subst i
                      exact row327 a
                    · have he : i = 328 := Fin.ext (by omega)
                      subst i
                      exact row328 a
              · by_cases h332 : i.val < 332
                · by_cases h330 : i.val < 330
                  · have he : i = 329 := Fin.ext (by omega)
                    subst i
                    exact row329 a
                  · by_cases h331 : i.val < 331
                    · have he : i = 330 := Fin.ext (by omega)
                      subst i
                      exact row330 a
                    · have he : i = 331 := Fin.ext (by omega)
                      subst i
                      exact row331 a
                · by_cases h333 : i.val < 333
                  · have he : i = 332 := Fin.ext (by omega)
                    subst i
                    exact row332 a
                  · by_cases h334 : i.val < 334
                    · have he : i = 333 := Fin.ext (by omega)
                      subst i
                      exact row333 a
                    · have he : i = 334 := Fin.ext (by omega)
                      subst i
                      exact row334 a
            · by_cases h340 : i.val < 340
              · by_cases h337 : i.val < 337
                · by_cases h336 : i.val < 336
                  · have he : i = 335 := Fin.ext (by omega)
                    subst i
                    exact row335 a
                  · have he : i = 336 := Fin.ext (by omega)
                    subst i
                    exact row336 a
                · by_cases h338 : i.val < 338
                  · have he : i = 337 := Fin.ext (by omega)
                    subst i
                    exact row337 a
                  · by_cases h339 : i.val < 339
                    · have he : i = 338 := Fin.ext (by omega)
                      subst i
                      exact row338 a
                    · have he : i = 339 := Fin.ext (by omega)
                      subst i
                      exact row339 a
              · by_cases h343 : i.val < 343
                · by_cases h341 : i.val < 341
                  · have he : i = 340 := Fin.ext (by omega)
                    subst i
                    exact row340 a
                  · by_cases h342 : i.val < 342
                    · have he : i = 341 := Fin.ext (by omega)
                      subst i
                      exact row341 a
                    · have he : i = 342 := Fin.ext (by omega)
                      subst i
                      exact row342 a
                · by_cases h344 : i.val < 344
                  · have he : i = 343 := Fin.ext (by omega)
                    subst i
                    exact row343 a
                  · by_cases h345 : i.val < 345
                    · have he : i = 344 := Fin.ext (by omega)
                      subst i
                      exact row344 a
                    · have he : i = 345 := Fin.ext (by omega)
                      subst i
                      exact row345 a
  · by_cases h519 : i.val < 519
    · by_cases h432 : i.val < 432
      · by_cases h389 : i.val < 389
        · by_cases h367 : i.val < 367
          · by_cases h356 : i.val < 356
            · by_cases h351 : i.val < 351
              · by_cases h348 : i.val < 348
                · by_cases h347 : i.val < 347
                  · have he : i = 346 := Fin.ext (by omega)
                    subst i
                    exact row346 a
                  · have he : i = 347 := Fin.ext (by omega)
                    subst i
                    exact row347 a
                · by_cases h349 : i.val < 349
                  · have he : i = 348 := Fin.ext (by omega)
                    subst i
                    exact row348 a
                  · by_cases h350 : i.val < 350
                    · have he : i = 349 := Fin.ext (by omega)
                      subst i
                      exact row349 a
                    · have he : i = 350 := Fin.ext (by omega)
                      subst i
                      exact row350 a
              · by_cases h353 : i.val < 353
                · by_cases h352 : i.val < 352
                  · have he : i = 351 := Fin.ext (by omega)
                    subst i
                    exact row351 a
                  · have he : i = 352 := Fin.ext (by omega)
                    subst i
                    exact row352 a
                · by_cases h354 : i.val < 354
                  · have he : i = 353 := Fin.ext (by omega)
                    subst i
                    exact row353 a
                  · by_cases h355 : i.val < 355
                    · have he : i = 354 := Fin.ext (by omega)
                      subst i
                      exact row354 a
                    · have he : i = 355 := Fin.ext (by omega)
                      subst i
                      exact row355 a
            · by_cases h361 : i.val < 361
              · by_cases h358 : i.val < 358
                · by_cases h357 : i.val < 357
                  · have he : i = 356 := Fin.ext (by omega)
                    subst i
                    exact row356 a
                  · have he : i = 357 := Fin.ext (by omega)
                    subst i
                    exact row357 a
                · by_cases h359 : i.val < 359
                  · have he : i = 358 := Fin.ext (by omega)
                    subst i
                    exact row358 a
                  · by_cases h360 : i.val < 360
                    · have he : i = 359 := Fin.ext (by omega)
                      subst i
                      exact row359 a
                    · have he : i = 360 := Fin.ext (by omega)
                      subst i
                      exact row360 a
              · by_cases h364 : i.val < 364
                · by_cases h362 : i.val < 362
                  · have he : i = 361 := Fin.ext (by omega)
                    subst i
                    exact row361 a
                  · by_cases h363 : i.val < 363
                    · have he : i = 362 := Fin.ext (by omega)
                      subst i
                      exact row362 a
                    · have he : i = 363 := Fin.ext (by omega)
                      subst i
                      exact row363 a
                · by_cases h365 : i.val < 365
                  · have he : i = 364 := Fin.ext (by omega)
                    subst i
                    exact row364 a
                  · by_cases h366 : i.val < 366
                    · have he : i = 365 := Fin.ext (by omega)
                      subst i
                      exact row365 a
                    · have he : i = 366 := Fin.ext (by omega)
                      subst i
                      exact row366 a
          · by_cases h378 : i.val < 378
            · by_cases h372 : i.val < 372
              · by_cases h369 : i.val < 369
                · by_cases h368 : i.val < 368
                  · have he : i = 367 := Fin.ext (by omega)
                    subst i
                    exact row367 a
                  · have he : i = 368 := Fin.ext (by omega)
                    subst i
                    exact row368 a
                · by_cases h370 : i.val < 370
                  · have he : i = 369 := Fin.ext (by omega)
                    subst i
                    exact row369 a
                  · by_cases h371 : i.val < 371
                    · have he : i = 370 := Fin.ext (by omega)
                      subst i
                      exact row370 a
                    · have he : i = 371 := Fin.ext (by omega)
                      subst i
                      exact row371 a
              · by_cases h375 : i.val < 375
                · by_cases h373 : i.val < 373
                  · have he : i = 372 := Fin.ext (by omega)
                    subst i
                    exact row372 a
                  · by_cases h374 : i.val < 374
                    · have he : i = 373 := Fin.ext (by omega)
                      subst i
                      exact row373 a
                    · have he : i = 374 := Fin.ext (by omega)
                      subst i
                      exact row374 a
                · by_cases h376 : i.val < 376
                  · have he : i = 375 := Fin.ext (by omega)
                    subst i
                    exact row375 a
                  · by_cases h377 : i.val < 377
                    · have he : i = 376 := Fin.ext (by omega)
                      subst i
                      exact row376 a
                    · have he : i = 377 := Fin.ext (by omega)
                      subst i
                      exact row377 a
            · by_cases h383 : i.val < 383
              · by_cases h380 : i.val < 380
                · by_cases h379 : i.val < 379
                  · have he : i = 378 := Fin.ext (by omega)
                    subst i
                    exact row378 a
                  · have he : i = 379 := Fin.ext (by omega)
                    subst i
                    exact row379 a
                · by_cases h381 : i.val < 381
                  · have he : i = 380 := Fin.ext (by omega)
                    subst i
                    exact row380 a
                  · by_cases h382 : i.val < 382
                    · have he : i = 381 := Fin.ext (by omega)
                      subst i
                      exact row381 a
                    · have he : i = 382 := Fin.ext (by omega)
                      subst i
                      exact row382 a
              · by_cases h386 : i.val < 386
                · by_cases h384 : i.val < 384
                  · have he : i = 383 := Fin.ext (by omega)
                    subst i
                    exact row383 a
                  · by_cases h385 : i.val < 385
                    · have he : i = 384 := Fin.ext (by omega)
                      subst i
                      exact row384 a
                    · have he : i = 385 := Fin.ext (by omega)
                      subst i
                      exact row385 a
                · by_cases h387 : i.val < 387
                  · have he : i = 386 := Fin.ext (by omega)
                    subst i
                    exact row386 a
                  · by_cases h388 : i.val < 388
                    · have he : i = 387 := Fin.ext (by omega)
                      subst i
                      exact row387 a
                    · have he : i = 388 := Fin.ext (by omega)
                      subst i
                      exact row388 a
        · by_cases h410 : i.val < 410
          · by_cases h399 : i.val < 399
            · by_cases h394 : i.val < 394
              · by_cases h391 : i.val < 391
                · by_cases h390 : i.val < 390
                  · have he : i = 389 := Fin.ext (by omega)
                    subst i
                    exact row389 a
                  · have he : i = 390 := Fin.ext (by omega)
                    subst i
                    exact row390 a
                · by_cases h392 : i.val < 392
                  · have he : i = 391 := Fin.ext (by omega)
                    subst i
                    exact row391 a
                  · by_cases h393 : i.val < 393
                    · have he : i = 392 := Fin.ext (by omega)
                      subst i
                      exact row392 a
                    · have he : i = 393 := Fin.ext (by omega)
                      subst i
                      exact row393 a
              · by_cases h396 : i.val < 396
                · by_cases h395 : i.val < 395
                  · have he : i = 394 := Fin.ext (by omega)
                    subst i
                    exact row394 a
                  · have he : i = 395 := Fin.ext (by omega)
                    subst i
                    exact row395 a
                · by_cases h397 : i.val < 397
                  · have he : i = 396 := Fin.ext (by omega)
                    subst i
                    exact row396 a
                  · by_cases h398 : i.val < 398
                    · have he : i = 397 := Fin.ext (by omega)
                      subst i
                      exact row397 a
                    · have he : i = 398 := Fin.ext (by omega)
                      subst i
                      exact row398 a
            · by_cases h404 : i.val < 404
              · by_cases h401 : i.val < 401
                · by_cases h400 : i.val < 400
                  · have he : i = 399 := Fin.ext (by omega)
                    subst i
                    exact row399 a
                  · have he : i = 400 := Fin.ext (by omega)
                    subst i
                    exact row400 a
                · by_cases h402 : i.val < 402
                  · have he : i = 401 := Fin.ext (by omega)
                    subst i
                    exact row401 a
                  · by_cases h403 : i.val < 403
                    · have he : i = 402 := Fin.ext (by omega)
                      subst i
                      exact row402 a
                    · have he : i = 403 := Fin.ext (by omega)
                      subst i
                      exact row403 a
              · by_cases h407 : i.val < 407
                · by_cases h405 : i.val < 405
                  · have he : i = 404 := Fin.ext (by omega)
                    subst i
                    exact row404 a
                  · by_cases h406 : i.val < 406
                    · have he : i = 405 := Fin.ext (by omega)
                      subst i
                      exact row405 a
                    · have he : i = 406 := Fin.ext (by omega)
                      subst i
                      exact row406 a
                · by_cases h408 : i.val < 408
                  · have he : i = 407 := Fin.ext (by omega)
                    subst i
                    exact row407 a
                  · by_cases h409 : i.val < 409
                    · have he : i = 408 := Fin.ext (by omega)
                      subst i
                      exact row408 a
                    · have he : i = 409 := Fin.ext (by omega)
                      subst i
                      exact row409 a
          · by_cases h421 : i.val < 421
            · by_cases h415 : i.val < 415
              · by_cases h412 : i.val < 412
                · by_cases h411 : i.val < 411
                  · have he : i = 410 := Fin.ext (by omega)
                    subst i
                    exact row410 a
                  · have he : i = 411 := Fin.ext (by omega)
                    subst i
                    exact row411 a
                · by_cases h413 : i.val < 413
                  · have he : i = 412 := Fin.ext (by omega)
                    subst i
                    exact row412 a
                  · by_cases h414 : i.val < 414
                    · have he : i = 413 := Fin.ext (by omega)
                      subst i
                      exact row413 a
                    · have he : i = 414 := Fin.ext (by omega)
                      subst i
                      exact row414 a
              · by_cases h418 : i.val < 418
                · by_cases h416 : i.val < 416
                  · have he : i = 415 := Fin.ext (by omega)
                    subst i
                    exact row415 a
                  · by_cases h417 : i.val < 417
                    · have he : i = 416 := Fin.ext (by omega)
                      subst i
                      exact row416 a
                    · have he : i = 417 := Fin.ext (by omega)
                      subst i
                      exact row417 a
                · by_cases h419 : i.val < 419
                  · have he : i = 418 := Fin.ext (by omega)
                    subst i
                    exact row418 a
                  · by_cases h420 : i.val < 420
                    · have he : i = 419 := Fin.ext (by omega)
                      subst i
                      exact row419 a
                    · have he : i = 420 := Fin.ext (by omega)
                      subst i
                      exact row420 a
            · by_cases h426 : i.val < 426
              · by_cases h423 : i.val < 423
                · by_cases h422 : i.val < 422
                  · have he : i = 421 := Fin.ext (by omega)
                    subst i
                    exact row421 a
                  · have he : i = 422 := Fin.ext (by omega)
                    subst i
                    exact row422 a
                · by_cases h424 : i.val < 424
                  · have he : i = 423 := Fin.ext (by omega)
                    subst i
                    exact row423 a
                  · by_cases h425 : i.val < 425
                    · have he : i = 424 := Fin.ext (by omega)
                      subst i
                      exact row424 a
                    · have he : i = 425 := Fin.ext (by omega)
                      subst i
                      exact row425 a
              · by_cases h429 : i.val < 429
                · by_cases h427 : i.val < 427
                  · have he : i = 426 := Fin.ext (by omega)
                    subst i
                    exact row426 a
                  · by_cases h428 : i.val < 428
                    · have he : i = 427 := Fin.ext (by omega)
                      subst i
                      exact row427 a
                    · have he : i = 428 := Fin.ext (by omega)
                      subst i
                      exact row428 a
                · by_cases h430 : i.val < 430
                  · have he : i = 429 := Fin.ext (by omega)
                    subst i
                    exact row429 a
                  · by_cases h431 : i.val < 431
                    · have he : i = 430 := Fin.ext (by omega)
                      subst i
                      exact row430 a
                    · have he : i = 431 := Fin.ext (by omega)
                      subst i
                      exact row431 a
      · by_cases h475 : i.val < 475
        · by_cases h453 : i.val < 453
          · by_cases h442 : i.val < 442
            · by_cases h437 : i.val < 437
              · by_cases h434 : i.val < 434
                · by_cases h433 : i.val < 433
                  · have he : i = 432 := Fin.ext (by omega)
                    subst i
                    exact row432 a
                  · have he : i = 433 := Fin.ext (by omega)
                    subst i
                    exact row433 a
                · by_cases h435 : i.val < 435
                  · have he : i = 434 := Fin.ext (by omega)
                    subst i
                    exact row434 a
                  · by_cases h436 : i.val < 436
                    · have he : i = 435 := Fin.ext (by omega)
                      subst i
                      exact row435 a
                    · have he : i = 436 := Fin.ext (by omega)
                      subst i
                      exact row436 a
              · by_cases h439 : i.val < 439
                · by_cases h438 : i.val < 438
                  · have he : i = 437 := Fin.ext (by omega)
                    subst i
                    exact row437 a
                  · have he : i = 438 := Fin.ext (by omega)
                    subst i
                    exact row438 a
                · by_cases h440 : i.val < 440
                  · have he : i = 439 := Fin.ext (by omega)
                    subst i
                    exact row439 a
                  · by_cases h441 : i.val < 441
                    · have he : i = 440 := Fin.ext (by omega)
                      subst i
                      exact row440 a
                    · have he : i = 441 := Fin.ext (by omega)
                      subst i
                      exact row441 a
            · by_cases h447 : i.val < 447
              · by_cases h444 : i.val < 444
                · by_cases h443 : i.val < 443
                  · have he : i = 442 := Fin.ext (by omega)
                    subst i
                    exact row442 a
                  · have he : i = 443 := Fin.ext (by omega)
                    subst i
                    exact row443 a
                · by_cases h445 : i.val < 445
                  · have he : i = 444 := Fin.ext (by omega)
                    subst i
                    exact row444 a
                  · by_cases h446 : i.val < 446
                    · have he : i = 445 := Fin.ext (by omega)
                      subst i
                      exact row445 a
                    · have he : i = 446 := Fin.ext (by omega)
                      subst i
                      exact row446 a
              · by_cases h450 : i.val < 450
                · by_cases h448 : i.val < 448
                  · have he : i = 447 := Fin.ext (by omega)
                    subst i
                    exact row447 a
                  · by_cases h449 : i.val < 449
                    · have he : i = 448 := Fin.ext (by omega)
                      subst i
                      exact row448 a
                    · have he : i = 449 := Fin.ext (by omega)
                      subst i
                      exact row449 a
                · by_cases h451 : i.val < 451
                  · have he : i = 450 := Fin.ext (by omega)
                    subst i
                    exact row450 a
                  · by_cases h452 : i.val < 452
                    · have he : i = 451 := Fin.ext (by omega)
                      subst i
                      exact row451 a
                    · have he : i = 452 := Fin.ext (by omega)
                      subst i
                      exact row452 a
          · by_cases h464 : i.val < 464
            · by_cases h458 : i.val < 458
              · by_cases h455 : i.val < 455
                · by_cases h454 : i.val < 454
                  · have he : i = 453 := Fin.ext (by omega)
                    subst i
                    exact row453 a
                  · have he : i = 454 := Fin.ext (by omega)
                    subst i
                    exact row454 a
                · by_cases h456 : i.val < 456
                  · have he : i = 455 := Fin.ext (by omega)
                    subst i
                    exact row455 a
                  · by_cases h457 : i.val < 457
                    · have he : i = 456 := Fin.ext (by omega)
                      subst i
                      exact row456 a
                    · have he : i = 457 := Fin.ext (by omega)
                      subst i
                      exact row457 a
              · by_cases h461 : i.val < 461
                · by_cases h459 : i.val < 459
                  · have he : i = 458 := Fin.ext (by omega)
                    subst i
                    exact row458 a
                  · by_cases h460 : i.val < 460
                    · have he : i = 459 := Fin.ext (by omega)
                      subst i
                      exact row459 a
                    · have he : i = 460 := Fin.ext (by omega)
                      subst i
                      exact row460 a
                · by_cases h462 : i.val < 462
                  · have he : i = 461 := Fin.ext (by omega)
                    subst i
                    exact row461 a
                  · by_cases h463 : i.val < 463
                    · have he : i = 462 := Fin.ext (by omega)
                      subst i
                      exact row462 a
                    · have he : i = 463 := Fin.ext (by omega)
                      subst i
                      exact row463 a
            · by_cases h469 : i.val < 469
              · by_cases h466 : i.val < 466
                · by_cases h465 : i.val < 465
                  · have he : i = 464 := Fin.ext (by omega)
                    subst i
                    exact row464 a
                  · have he : i = 465 := Fin.ext (by omega)
                    subst i
                    exact row465 a
                · by_cases h467 : i.val < 467
                  · have he : i = 466 := Fin.ext (by omega)
                    subst i
                    exact row466 a
                  · by_cases h468 : i.val < 468
                    · have he : i = 467 := Fin.ext (by omega)
                      subst i
                      exact row467 a
                    · have he : i = 468 := Fin.ext (by omega)
                      subst i
                      exact row468 a
              · by_cases h472 : i.val < 472
                · by_cases h470 : i.val < 470
                  · have he : i = 469 := Fin.ext (by omega)
                    subst i
                    exact row469 a
                  · by_cases h471 : i.val < 471
                    · have he : i = 470 := Fin.ext (by omega)
                      subst i
                      exact row470 a
                    · have he : i = 471 := Fin.ext (by omega)
                      subst i
                      exact row471 a
                · by_cases h473 : i.val < 473
                  · have he : i = 472 := Fin.ext (by omega)
                    subst i
                    exact row472 a
                  · by_cases h474 : i.val < 474
                    · have he : i = 473 := Fin.ext (by omega)
                      subst i
                      exact row473 a
                    · have he : i = 474 := Fin.ext (by omega)
                      subst i
                      exact row474 a
        · by_cases h497 : i.val < 497
          · by_cases h486 : i.val < 486
            · by_cases h480 : i.val < 480
              · by_cases h477 : i.val < 477
                · by_cases h476 : i.val < 476
                  · have he : i = 475 := Fin.ext (by omega)
                    subst i
                    exact row475 a
                  · have he : i = 476 := Fin.ext (by omega)
                    subst i
                    exact row476 a
                · by_cases h478 : i.val < 478
                  · have he : i = 477 := Fin.ext (by omega)
                    subst i
                    exact row477 a
                  · by_cases h479 : i.val < 479
                    · have he : i = 478 := Fin.ext (by omega)
                      subst i
                      exact row478 a
                    · have he : i = 479 := Fin.ext (by omega)
                      subst i
                      exact row479 a
              · by_cases h483 : i.val < 483
                · by_cases h481 : i.val < 481
                  · have he : i = 480 := Fin.ext (by omega)
                    subst i
                    exact row480 a
                  · by_cases h482 : i.val < 482
                    · have he : i = 481 := Fin.ext (by omega)
                      subst i
                      exact row481 a
                    · have he : i = 482 := Fin.ext (by omega)
                      subst i
                      exact row482 a
                · by_cases h484 : i.val < 484
                  · have he : i = 483 := Fin.ext (by omega)
                    subst i
                    exact row483 a
                  · by_cases h485 : i.val < 485
                    · have he : i = 484 := Fin.ext (by omega)
                      subst i
                      exact row484 a
                    · have he : i = 485 := Fin.ext (by omega)
                      subst i
                      exact row485 a
            · by_cases h491 : i.val < 491
              · by_cases h488 : i.val < 488
                · by_cases h487 : i.val < 487
                  · have he : i = 486 := Fin.ext (by omega)
                    subst i
                    exact row486 a
                  · have he : i = 487 := Fin.ext (by omega)
                    subst i
                    exact row487 a
                · by_cases h489 : i.val < 489
                  · have he : i = 488 := Fin.ext (by omega)
                    subst i
                    exact row488 a
                  · by_cases h490 : i.val < 490
                    · have he : i = 489 := Fin.ext (by omega)
                      subst i
                      exact row489 a
                    · have he : i = 490 := Fin.ext (by omega)
                      subst i
                      exact row490 a
              · by_cases h494 : i.val < 494
                · by_cases h492 : i.val < 492
                  · have he : i = 491 := Fin.ext (by omega)
                    subst i
                    exact row491 a
                  · by_cases h493 : i.val < 493
                    · have he : i = 492 := Fin.ext (by omega)
                      subst i
                      exact row492 a
                    · have he : i = 493 := Fin.ext (by omega)
                      subst i
                      exact row493 a
                · by_cases h495 : i.val < 495
                  · have he : i = 494 := Fin.ext (by omega)
                    subst i
                    exact row494 a
                  · by_cases h496 : i.val < 496
                    · have he : i = 495 := Fin.ext (by omega)
                      subst i
                      exact row495 a
                    · have he : i = 496 := Fin.ext (by omega)
                      subst i
                      exact row496 a
          · by_cases h508 : i.val < 508
            · by_cases h502 : i.val < 502
              · by_cases h499 : i.val < 499
                · by_cases h498 : i.val < 498
                  · have he : i = 497 := Fin.ext (by omega)
                    subst i
                    exact row497 a
                  · have he : i = 498 := Fin.ext (by omega)
                    subst i
                    exact row498 a
                · by_cases h500 : i.val < 500
                  · have he : i = 499 := Fin.ext (by omega)
                    subst i
                    exact row499 a
                  · by_cases h501 : i.val < 501
                    · have he : i = 500 := Fin.ext (by omega)
                      subst i
                      exact row500 a
                    · have he : i = 501 := Fin.ext (by omega)
                      subst i
                      exact row501 a
              · by_cases h505 : i.val < 505
                · by_cases h503 : i.val < 503
                  · have he : i = 502 := Fin.ext (by omega)
                    subst i
                    exact row502 a
                  · by_cases h504 : i.val < 504
                    · have he : i = 503 := Fin.ext (by omega)
                      subst i
                      exact row503 a
                    · have he : i = 504 := Fin.ext (by omega)
                      subst i
                      exact row504 a
                · by_cases h506 : i.val < 506
                  · have he : i = 505 := Fin.ext (by omega)
                    subst i
                    exact row505 a
                  · by_cases h507 : i.val < 507
                    · have he : i = 506 := Fin.ext (by omega)
                      subst i
                      exact row506 a
                    · have he : i = 507 := Fin.ext (by omega)
                      subst i
                      exact row507 a
            · by_cases h513 : i.val < 513
              · by_cases h510 : i.val < 510
                · by_cases h509 : i.val < 509
                  · have he : i = 508 := Fin.ext (by omega)
                    subst i
                    exact row508 a
                  · have he : i = 509 := Fin.ext (by omega)
                    subst i
                    exact row509 a
                · by_cases h511 : i.val < 511
                  · have he : i = 510 := Fin.ext (by omega)
                    subst i
                    exact row510 a
                  · by_cases h512 : i.val < 512
                    · have he : i = 511 := Fin.ext (by omega)
                      subst i
                      exact row511 a
                    · have he : i = 512 := Fin.ext (by omega)
                      subst i
                      exact row512 a
              · by_cases h516 : i.val < 516
                · by_cases h514 : i.val < 514
                  · have he : i = 513 := Fin.ext (by omega)
                    subst i
                    exact row513 a
                  · by_cases h515 : i.val < 515
                    · have he : i = 514 := Fin.ext (by omega)
                      subst i
                      exact row514 a
                    · have he : i = 515 := Fin.ext (by omega)
                      subst i
                      exact row515 a
                · by_cases h517 : i.val < 517
                  · have he : i = 516 := Fin.ext (by omega)
                    subst i
                    exact row516 a
                  · by_cases h518 : i.val < 518
                    · have he : i = 517 := Fin.ext (by omega)
                      subst i
                      exact row517 a
                    · have he : i = 518 := Fin.ext (by omega)
                      subst i
                      exact row518 a
    · by_cases h606 : i.val < 606
      · by_cases h562 : i.val < 562
        · by_cases h540 : i.val < 540
          · by_cases h529 : i.val < 529
            · by_cases h524 : i.val < 524
              · by_cases h521 : i.val < 521
                · by_cases h520 : i.val < 520
                  · have he : i = 519 := Fin.ext (by omega)
                    subst i
                    exact row519 a
                  · have he : i = 520 := Fin.ext (by omega)
                    subst i
                    exact row520 a
                · by_cases h522 : i.val < 522
                  · have he : i = 521 := Fin.ext (by omega)
                    subst i
                    exact row521 a
                  · by_cases h523 : i.val < 523
                    · have he : i = 522 := Fin.ext (by omega)
                      subst i
                      exact row522 a
                    · have he : i = 523 := Fin.ext (by omega)
                      subst i
                      exact row523 a
              · by_cases h526 : i.val < 526
                · by_cases h525 : i.val < 525
                  · have he : i = 524 := Fin.ext (by omega)
                    subst i
                    exact row524 a
                  · have he : i = 525 := Fin.ext (by omega)
                    subst i
                    exact row525 a
                · by_cases h527 : i.val < 527
                  · have he : i = 526 := Fin.ext (by omega)
                    subst i
                    exact row526 a
                  · by_cases h528 : i.val < 528
                    · have he : i = 527 := Fin.ext (by omega)
                      subst i
                      exact row527 a
                    · have he : i = 528 := Fin.ext (by omega)
                      subst i
                      exact row528 a
            · by_cases h534 : i.val < 534
              · by_cases h531 : i.val < 531
                · by_cases h530 : i.val < 530
                  · have he : i = 529 := Fin.ext (by omega)
                    subst i
                    exact row529 a
                  · have he : i = 530 := Fin.ext (by omega)
                    subst i
                    exact row530 a
                · by_cases h532 : i.val < 532
                  · have he : i = 531 := Fin.ext (by omega)
                    subst i
                    exact row531 a
                  · by_cases h533 : i.val < 533
                    · have he : i = 532 := Fin.ext (by omega)
                      subst i
                      exact row532 a
                    · have he : i = 533 := Fin.ext (by omega)
                      subst i
                      exact row533 a
              · by_cases h537 : i.val < 537
                · by_cases h535 : i.val < 535
                  · have he : i = 534 := Fin.ext (by omega)
                    subst i
                    exact row534 a
                  · by_cases h536 : i.val < 536
                    · have he : i = 535 := Fin.ext (by omega)
                      subst i
                      exact row535 a
                    · have he : i = 536 := Fin.ext (by omega)
                      subst i
                      exact row536 a
                · by_cases h538 : i.val < 538
                  · have he : i = 537 := Fin.ext (by omega)
                    subst i
                    exact row537 a
                  · by_cases h539 : i.val < 539
                    · have he : i = 538 := Fin.ext (by omega)
                      subst i
                      exact row538 a
                    · have he : i = 539 := Fin.ext (by omega)
                      subst i
                      exact row539 a
          · by_cases h551 : i.val < 551
            · by_cases h545 : i.val < 545
              · by_cases h542 : i.val < 542
                · by_cases h541 : i.val < 541
                  · have he : i = 540 := Fin.ext (by omega)
                    subst i
                    exact row540 a
                  · have he : i = 541 := Fin.ext (by omega)
                    subst i
                    exact row541 a
                · by_cases h543 : i.val < 543
                  · have he : i = 542 := Fin.ext (by omega)
                    subst i
                    exact row542 a
                  · by_cases h544 : i.val < 544
                    · have he : i = 543 := Fin.ext (by omega)
                      subst i
                      exact row543 a
                    · have he : i = 544 := Fin.ext (by omega)
                      subst i
                      exact row544 a
              · by_cases h548 : i.val < 548
                · by_cases h546 : i.val < 546
                  · have he : i = 545 := Fin.ext (by omega)
                    subst i
                    exact row545 a
                  · by_cases h547 : i.val < 547
                    · have he : i = 546 := Fin.ext (by omega)
                      subst i
                      exact row546 a
                    · have he : i = 547 := Fin.ext (by omega)
                      subst i
                      exact row547 a
                · by_cases h549 : i.val < 549
                  · have he : i = 548 := Fin.ext (by omega)
                    subst i
                    exact row548 a
                  · by_cases h550 : i.val < 550
                    · have he : i = 549 := Fin.ext (by omega)
                      subst i
                      exact row549 a
                    · have he : i = 550 := Fin.ext (by omega)
                      subst i
                      exact row550 a
            · by_cases h556 : i.val < 556
              · by_cases h553 : i.val < 553
                · by_cases h552 : i.val < 552
                  · have he : i = 551 := Fin.ext (by omega)
                    subst i
                    exact row551 a
                  · have he : i = 552 := Fin.ext (by omega)
                    subst i
                    exact row552 a
                · by_cases h554 : i.val < 554
                  · have he : i = 553 := Fin.ext (by omega)
                    subst i
                    exact row553 a
                  · by_cases h555 : i.val < 555
                    · have he : i = 554 := Fin.ext (by omega)
                      subst i
                      exact row554 a
                    · have he : i = 555 := Fin.ext (by omega)
                      subst i
                      exact row555 a
              · by_cases h559 : i.val < 559
                · by_cases h557 : i.val < 557
                  · have he : i = 556 := Fin.ext (by omega)
                    subst i
                    exact row556 a
                  · by_cases h558 : i.val < 558
                    · have he : i = 557 := Fin.ext (by omega)
                      subst i
                      exact row557 a
                    · have he : i = 558 := Fin.ext (by omega)
                      subst i
                      exact row558 a
                · by_cases h560 : i.val < 560
                  · have he : i = 559 := Fin.ext (by omega)
                    subst i
                    exact row559 a
                  · by_cases h561 : i.val < 561
                    · have he : i = 560 := Fin.ext (by omega)
                      subst i
                      exact row560 a
                    · have he : i = 561 := Fin.ext (by omega)
                      subst i
                      exact row561 a
        · by_cases h584 : i.val < 584
          · by_cases h573 : i.val < 573
            · by_cases h567 : i.val < 567
              · by_cases h564 : i.val < 564
                · by_cases h563 : i.val < 563
                  · have he : i = 562 := Fin.ext (by omega)
                    subst i
                    exact row562 a
                  · have he : i = 563 := Fin.ext (by omega)
                    subst i
                    exact row563 a
                · by_cases h565 : i.val < 565
                  · have he : i = 564 := Fin.ext (by omega)
                    subst i
                    exact row564 a
                  · by_cases h566 : i.val < 566
                    · have he : i = 565 := Fin.ext (by omega)
                      subst i
                      exact row565 a
                    · have he : i = 566 := Fin.ext (by omega)
                      subst i
                      exact row566 a
              · by_cases h570 : i.val < 570
                · by_cases h568 : i.val < 568
                  · have he : i = 567 := Fin.ext (by omega)
                    subst i
                    exact row567 a
                  · by_cases h569 : i.val < 569
                    · have he : i = 568 := Fin.ext (by omega)
                      subst i
                      exact row568 a
                    · have he : i = 569 := Fin.ext (by omega)
                      subst i
                      exact row569 a
                · by_cases h571 : i.val < 571
                  · have he : i = 570 := Fin.ext (by omega)
                    subst i
                    exact row570 a
                  · by_cases h572 : i.val < 572
                    · have he : i = 571 := Fin.ext (by omega)
                      subst i
                      exact row571 a
                    · have he : i = 572 := Fin.ext (by omega)
                      subst i
                      exact row572 a
            · by_cases h578 : i.val < 578
              · by_cases h575 : i.val < 575
                · by_cases h574 : i.val < 574
                  · have he : i = 573 := Fin.ext (by omega)
                    subst i
                    exact row573 a
                  · have he : i = 574 := Fin.ext (by omega)
                    subst i
                    exact row574 a
                · by_cases h576 : i.val < 576
                  · have he : i = 575 := Fin.ext (by omega)
                    subst i
                    exact row575 a
                  · by_cases h577 : i.val < 577
                    · have he : i = 576 := Fin.ext (by omega)
                      subst i
                      exact row576 a
                    · have he : i = 577 := Fin.ext (by omega)
                      subst i
                      exact row577 a
              · by_cases h581 : i.val < 581
                · by_cases h579 : i.val < 579
                  · have he : i = 578 := Fin.ext (by omega)
                    subst i
                    exact row578 a
                  · by_cases h580 : i.val < 580
                    · have he : i = 579 := Fin.ext (by omega)
                      subst i
                      exact row579 a
                    · have he : i = 580 := Fin.ext (by omega)
                      subst i
                      exact row580 a
                · by_cases h582 : i.val < 582
                  · have he : i = 581 := Fin.ext (by omega)
                    subst i
                    exact row581 a
                  · by_cases h583 : i.val < 583
                    · have he : i = 582 := Fin.ext (by omega)
                      subst i
                      exact row582 a
                    · have he : i = 583 := Fin.ext (by omega)
                      subst i
                      exact row583 a
          · by_cases h595 : i.val < 595
            · by_cases h589 : i.val < 589
              · by_cases h586 : i.val < 586
                · by_cases h585 : i.val < 585
                  · have he : i = 584 := Fin.ext (by omega)
                    subst i
                    exact row584 a
                  · have he : i = 585 := Fin.ext (by omega)
                    subst i
                    exact row585 a
                · by_cases h587 : i.val < 587
                  · have he : i = 586 := Fin.ext (by omega)
                    subst i
                    exact row586 a
                  · by_cases h588 : i.val < 588
                    · have he : i = 587 := Fin.ext (by omega)
                      subst i
                      exact row587 a
                    · have he : i = 588 := Fin.ext (by omega)
                      subst i
                      exact row588 a
              · by_cases h592 : i.val < 592
                · by_cases h590 : i.val < 590
                  · have he : i = 589 := Fin.ext (by omega)
                    subst i
                    exact row589 a
                  · by_cases h591 : i.val < 591
                    · have he : i = 590 := Fin.ext (by omega)
                      subst i
                      exact row590 a
                    · have he : i = 591 := Fin.ext (by omega)
                      subst i
                      exact row591 a
                · by_cases h593 : i.val < 593
                  · have he : i = 592 := Fin.ext (by omega)
                    subst i
                    exact row592 a
                  · by_cases h594 : i.val < 594
                    · have he : i = 593 := Fin.ext (by omega)
                      subst i
                      exact row593 a
                    · have he : i = 594 := Fin.ext (by omega)
                      subst i
                      exact row594 a
            · by_cases h600 : i.val < 600
              · by_cases h597 : i.val < 597
                · by_cases h596 : i.val < 596
                  · have he : i = 595 := Fin.ext (by omega)
                    subst i
                    exact row595 a
                  · have he : i = 596 := Fin.ext (by omega)
                    subst i
                    exact row596 a
                · by_cases h598 : i.val < 598
                  · have he : i = 597 := Fin.ext (by omega)
                    subst i
                    exact row597 a
                  · by_cases h599 : i.val < 599
                    · have he : i = 598 := Fin.ext (by omega)
                      subst i
                      exact row598 a
                    · have he : i = 599 := Fin.ext (by omega)
                      subst i
                      exact row599 a
              · by_cases h603 : i.val < 603
                · by_cases h601 : i.val < 601
                  · have he : i = 600 := Fin.ext (by omega)
                    subst i
                    exact row600 a
                  · by_cases h602 : i.val < 602
                    · have he : i = 601 := Fin.ext (by omega)
                      subst i
                      exact row601 a
                    · have he : i = 602 := Fin.ext (by omega)
                      subst i
                      exact row602 a
                · by_cases h604 : i.val < 604
                  · have he : i = 603 := Fin.ext (by omega)
                    subst i
                    exact row603 a
                  · by_cases h605 : i.val < 605
                    · have he : i = 604 := Fin.ext (by omega)
                      subst i
                      exact row604 a
                    · have he : i = 605 := Fin.ext (by omega)
                      subst i
                      exact row605 a
      · by_cases h649 : i.val < 649
        · by_cases h627 : i.val < 627
          · by_cases h616 : i.val < 616
            · by_cases h611 : i.val < 611
              · by_cases h608 : i.val < 608
                · by_cases h607 : i.val < 607
                  · have he : i = 606 := Fin.ext (by omega)
                    subst i
                    exact row606 a
                  · have he : i = 607 := Fin.ext (by omega)
                    subst i
                    exact row607 a
                · by_cases h609 : i.val < 609
                  · have he : i = 608 := Fin.ext (by omega)
                    subst i
                    exact row608 a
                  · by_cases h610 : i.val < 610
                    · have he : i = 609 := Fin.ext (by omega)
                      subst i
                      exact row609 a
                    · have he : i = 610 := Fin.ext (by omega)
                      subst i
                      exact row610 a
              · by_cases h613 : i.val < 613
                · by_cases h612 : i.val < 612
                  · have he : i = 611 := Fin.ext (by omega)
                    subst i
                    exact row611 a
                  · have he : i = 612 := Fin.ext (by omega)
                    subst i
                    exact row612 a
                · by_cases h614 : i.val < 614
                  · have he : i = 613 := Fin.ext (by omega)
                    subst i
                    exact row613 a
                  · by_cases h615 : i.val < 615
                    · have he : i = 614 := Fin.ext (by omega)
                      subst i
                      exact row614 a
                    · have he : i = 615 := Fin.ext (by omega)
                      subst i
                      exact row615 a
            · by_cases h621 : i.val < 621
              · by_cases h618 : i.val < 618
                · by_cases h617 : i.val < 617
                  · have he : i = 616 := Fin.ext (by omega)
                    subst i
                    exact row616 a
                  · have he : i = 617 := Fin.ext (by omega)
                    subst i
                    exact row617 a
                · by_cases h619 : i.val < 619
                  · have he : i = 618 := Fin.ext (by omega)
                    subst i
                    exact row618 a
                  · by_cases h620 : i.val < 620
                    · have he : i = 619 := Fin.ext (by omega)
                      subst i
                      exact row619 a
                    · have he : i = 620 := Fin.ext (by omega)
                      subst i
                      exact row620 a
              · by_cases h624 : i.val < 624
                · by_cases h622 : i.val < 622
                  · have he : i = 621 := Fin.ext (by omega)
                    subst i
                    exact row621 a
                  · by_cases h623 : i.val < 623
                    · have he : i = 622 := Fin.ext (by omega)
                      subst i
                      exact row622 a
                    · have he : i = 623 := Fin.ext (by omega)
                      subst i
                      exact row623 a
                · by_cases h625 : i.val < 625
                  · have he : i = 624 := Fin.ext (by omega)
                    subst i
                    exact row624 a
                  · by_cases h626 : i.val < 626
                    · have he : i = 625 := Fin.ext (by omega)
                      subst i
                      exact row625 a
                    · have he : i = 626 := Fin.ext (by omega)
                      subst i
                      exact row626 a
          · by_cases h638 : i.val < 638
            · by_cases h632 : i.val < 632
              · by_cases h629 : i.val < 629
                · by_cases h628 : i.val < 628
                  · have he : i = 627 := Fin.ext (by omega)
                    subst i
                    exact row627 a
                  · have he : i = 628 := Fin.ext (by omega)
                    subst i
                    exact row628 a
                · by_cases h630 : i.val < 630
                  · have he : i = 629 := Fin.ext (by omega)
                    subst i
                    exact row629 a
                  · by_cases h631 : i.val < 631
                    · have he : i = 630 := Fin.ext (by omega)
                      subst i
                      exact row630 a
                    · have he : i = 631 := Fin.ext (by omega)
                      subst i
                      exact row631 a
              · by_cases h635 : i.val < 635
                · by_cases h633 : i.val < 633
                  · have he : i = 632 := Fin.ext (by omega)
                    subst i
                    exact row632 a
                  · by_cases h634 : i.val < 634
                    · have he : i = 633 := Fin.ext (by omega)
                      subst i
                      exact row633 a
                    · have he : i = 634 := Fin.ext (by omega)
                      subst i
                      exact row634 a
                · by_cases h636 : i.val < 636
                  · have he : i = 635 := Fin.ext (by omega)
                    subst i
                    exact row635 a
                  · by_cases h637 : i.val < 637
                    · have he : i = 636 := Fin.ext (by omega)
                      subst i
                      exact row636 a
                    · have he : i = 637 := Fin.ext (by omega)
                      subst i
                      exact row637 a
            · by_cases h643 : i.val < 643
              · by_cases h640 : i.val < 640
                · by_cases h639 : i.val < 639
                  · have he : i = 638 := Fin.ext (by omega)
                    subst i
                    exact row638 a
                  · have he : i = 639 := Fin.ext (by omega)
                    subst i
                    exact row639 a
                · by_cases h641 : i.val < 641
                  · have he : i = 640 := Fin.ext (by omega)
                    subst i
                    exact row640 a
                  · by_cases h642 : i.val < 642
                    · have he : i = 641 := Fin.ext (by omega)
                      subst i
                      exact row641 a
                    · have he : i = 642 := Fin.ext (by omega)
                      subst i
                      exact row642 a
              · by_cases h646 : i.val < 646
                · by_cases h644 : i.val < 644
                  · have he : i = 643 := Fin.ext (by omega)
                    subst i
                    exact row643 a
                  · by_cases h645 : i.val < 645
                    · have he : i = 644 := Fin.ext (by omega)
                      subst i
                      exact row644 a
                    · have he : i = 645 := Fin.ext (by omega)
                      subst i
                      exact row645 a
                · by_cases h647 : i.val < 647
                  · have he : i = 646 := Fin.ext (by omega)
                    subst i
                    exact row646 a
                  · by_cases h648 : i.val < 648
                    · have he : i = 647 := Fin.ext (by omega)
                      subst i
                      exact row647 a
                    · have he : i = 648 := Fin.ext (by omega)
                      subst i
                      exact row648 a
        · by_cases h671 : i.val < 671
          · by_cases h660 : i.val < 660
            · by_cases h654 : i.val < 654
              · by_cases h651 : i.val < 651
                · by_cases h650 : i.val < 650
                  · have he : i = 649 := Fin.ext (by omega)
                    subst i
                    exact row649 a
                  · have he : i = 650 := Fin.ext (by omega)
                    subst i
                    exact row650 a
                · by_cases h652 : i.val < 652
                  · have he : i = 651 := Fin.ext (by omega)
                    subst i
                    exact row651 a
                  · by_cases h653 : i.val < 653
                    · have he : i = 652 := Fin.ext (by omega)
                      subst i
                      exact row652 a
                    · have he : i = 653 := Fin.ext (by omega)
                      subst i
                      exact row653 a
              · by_cases h657 : i.val < 657
                · by_cases h655 : i.val < 655
                  · have he : i = 654 := Fin.ext (by omega)
                    subst i
                    exact row654 a
                  · by_cases h656 : i.val < 656
                    · have he : i = 655 := Fin.ext (by omega)
                      subst i
                      exact row655 a
                    · have he : i = 656 := Fin.ext (by omega)
                      subst i
                      exact row656 a
                · by_cases h658 : i.val < 658
                  · have he : i = 657 := Fin.ext (by omega)
                    subst i
                    exact row657 a
                  · by_cases h659 : i.val < 659
                    · have he : i = 658 := Fin.ext (by omega)
                      subst i
                      exact row658 a
                    · have he : i = 659 := Fin.ext (by omega)
                      subst i
                      exact row659 a
            · by_cases h665 : i.val < 665
              · by_cases h662 : i.val < 662
                · by_cases h661 : i.val < 661
                  · have he : i = 660 := Fin.ext (by omega)
                    subst i
                    exact row660 a
                  · have he : i = 661 := Fin.ext (by omega)
                    subst i
                    exact row661 a
                · by_cases h663 : i.val < 663
                  · have he : i = 662 := Fin.ext (by omega)
                    subst i
                    exact row662 a
                  · by_cases h664 : i.val < 664
                    · have he : i = 663 := Fin.ext (by omega)
                      subst i
                      exact row663 a
                    · have he : i = 664 := Fin.ext (by omega)
                      subst i
                      exact row664 a
              · by_cases h668 : i.val < 668
                · by_cases h666 : i.val < 666
                  · have he : i = 665 := Fin.ext (by omega)
                    subst i
                    exact row665 a
                  · by_cases h667 : i.val < 667
                    · have he : i = 666 := Fin.ext (by omega)
                      subst i
                      exact row666 a
                    · have he : i = 667 := Fin.ext (by omega)
                      subst i
                      exact row667 a
                · by_cases h669 : i.val < 669
                  · have he : i = 668 := Fin.ext (by omega)
                    subst i
                    exact row668 a
                  · by_cases h670 : i.val < 670
                    · have he : i = 669 := Fin.ext (by omega)
                      subst i
                      exact row669 a
                    · have he : i = 670 := Fin.ext (by omega)
                      subst i
                      exact row670 a
          · by_cases h682 : i.val < 682
            · by_cases h676 : i.val < 676
              · by_cases h673 : i.val < 673
                · by_cases h672 : i.val < 672
                  · have he : i = 671 := Fin.ext (by omega)
                    subst i
                    exact row671 a
                  · have he : i = 672 := Fin.ext (by omega)
                    subst i
                    exact row672 a
                · by_cases h674 : i.val < 674
                  · have he : i = 673 := Fin.ext (by omega)
                    subst i
                    exact row673 a
                  · by_cases h675 : i.val < 675
                    · have he : i = 674 := Fin.ext (by omega)
                      subst i
                      exact row674 a
                    · have he : i = 675 := Fin.ext (by omega)
                      subst i
                      exact row675 a
              · by_cases h679 : i.val < 679
                · by_cases h677 : i.val < 677
                  · have he : i = 676 := Fin.ext (by omega)
                    subst i
                    exact row676 a
                  · by_cases h678 : i.val < 678
                    · have he : i = 677 := Fin.ext (by omega)
                      subst i
                      exact row677 a
                    · have he : i = 678 := Fin.ext (by omega)
                      subst i
                      exact row678 a
                · by_cases h680 : i.val < 680
                  · have he : i = 679 := Fin.ext (by omega)
                    subst i
                    exact row679 a
                  · by_cases h681 : i.val < 681
                    · have he : i = 680 := Fin.ext (by omega)
                      subst i
                      exact row680 a
                    · have he : i = 681 := Fin.ext (by omega)
                      subst i
                      exact row681 a
            · by_cases h687 : i.val < 687
              · by_cases h684 : i.val < 684
                · by_cases h683 : i.val < 683
                  · have he : i = 682 := Fin.ext (by omega)
                    subst i
                    exact row682 a
                  · have he : i = 683 := Fin.ext (by omega)
                    subst i
                    exact row683 a
                · by_cases h685 : i.val < 685
                  · have he : i = 684 := Fin.ext (by omega)
                    subst i
                    exact row684 a
                  · by_cases h686 : i.val < 686
                    · have he : i = 685 := Fin.ext (by omega)
                      subst i
                      exact row685 a
                    · have he : i = 686 := Fin.ext (by omega)
                      subst i
                      exact row686 a
              · by_cases h690 : i.val < 690
                · by_cases h688 : i.val < 688
                  · have he : i = 687 := Fin.ext (by omega)
                    subst i
                    exact row687 a
                  · by_cases h689 : i.val < 689
                    · have he : i = 688 := Fin.ext (by omega)
                      subst i
                      exact row688 a
                    · have he : i = 689 := Fin.ext (by omega)
                      subst i
                      exact row689 a
                · by_cases h691 : i.val < 691
                  · have he : i = 690 := Fin.ext (by omega)
                    subst i
                    exact row690 a
                  · by_cases h692 : i.val < 692
                    · have he : i = 691 := Fin.ext (by omega)
                      subst i
                      exact row691 a
                    · have he : i = 692 := Fin.ext (by omega)
                      subst i
                      exact row692 a

/-- A cover of the actual original presentation by its explicit seven-generator subgroup. -/
noncomputable def cover :
    Subgroup.GeneratorCosetCover level0Subgroup PresentedGroup.of (Fin 693) :=
  generatorCosetCover Fin.val 0 (by exact eval_nil _) destination transitions

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
