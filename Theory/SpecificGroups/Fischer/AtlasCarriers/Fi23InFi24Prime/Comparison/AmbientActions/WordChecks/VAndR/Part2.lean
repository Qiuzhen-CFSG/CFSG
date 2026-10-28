module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 8192

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block128 : checkPow pointTest 8192 6 = true := by
  decide +kernel

private theorem block129 : checkPow pointTest 8256 6 = true := by
  decide +kernel

private theorem block130 : checkPow pointTest 8320 6 = true := by
  decide +kernel

private theorem block131 : checkPow pointTest 8384 6 = true := by
  decide +kernel

private theorem block132 : checkPow pointTest 8448 6 = true := by
  decide +kernel

private theorem block133 : checkPow pointTest 8512 6 = true := by
  decide +kernel

private theorem block134 : checkPow pointTest 8576 6 = true := by
  decide +kernel

private theorem block135 : checkPow pointTest 8640 6 = true := by
  decide +kernel

private theorem block136 : checkPow pointTest 8704 6 = true := by
  decide +kernel

private theorem block137 : checkPow pointTest 8768 6 = true := by
  decide +kernel

private theorem block138 : checkPow pointTest 8832 6 = true := by
  decide +kernel

private theorem block139 : checkPow pointTest 8896 6 = true := by
  decide +kernel

private theorem block140 : checkPow pointTest 8960 6 = true := by
  decide +kernel

private theorem block141 : checkPow pointTest 9024 6 = true := by
  decide +kernel

private theorem block142 : checkPow pointTest 9088 6 = true := by
  decide +kernel

private theorem block143 : checkPow pointTest 9152 6 = true := by
  decide +kernel

private theorem block144 : checkPow pointTest 9216 6 = true := by
  decide +kernel

private theorem block145 : checkPow pointTest 9280 6 = true := by
  decide +kernel

private theorem block146 : checkPow pointTest 9344 6 = true := by
  decide +kernel

private theorem block147 : checkPow pointTest 9408 6 = true := by
  decide +kernel

private theorem block148 : checkPow pointTest 9472 6 = true := by
  decide +kernel

private theorem block149 : checkPow pointTest 9536 6 = true := by
  decide +kernel

private theorem block150 : checkPow pointTest 9600 6 = true := by
  decide +kernel

private theorem block151 : checkPow pointTest 9664 6 = true := by
  decide +kernel

private theorem block152 : checkPow pointTest 9728 6 = true := by
  decide +kernel

private theorem block153 : checkPow pointTest 9792 6 = true := by
  decide +kernel

private theorem block154 : checkPow pointTest 9856 6 = true := by
  decide +kernel

private theorem block155 : checkPow pointTest 9920 6 = true := by
  decide +kernel

private theorem block156 : checkPow pointTest 9984 6 = true := by
  decide +kernel

private theorem block157 : checkPow pointTest 10048 6 = true := by
  decide +kernel

private theorem block158 : checkPow pointTest 10112 6 = true := by
  decide +kernel

private theorem block159 : checkPow pointTest 10176 6 = true := by
  decide +kernel

private theorem block160 : checkPow pointTest 10240 6 = true := by
  decide +kernel

private theorem block161 : checkPow pointTest 10304 6 = true := by
  decide +kernel

private theorem block162 : checkPow pointTest 10368 6 = true := by
  decide +kernel

private theorem block163 : checkPow pointTest 10432 6 = true := by
  decide +kernel

private theorem block164 : checkPow pointTest 10496 6 = true := by
  decide +kernel

private theorem block165 : checkPow pointTest 10560 6 = true := by
  decide +kernel

private theorem block166 : checkPow pointTest 10624 6 = true := by
  decide +kernel

private theorem block167 : checkPow pointTest 10688 6 = true := by
  decide +kernel

private theorem block168 : checkPow pointTest 10752 6 = true := by
  decide +kernel

private theorem block169 : checkPow pointTest 10816 6 = true := by
  decide +kernel

private theorem block170 : checkPow pointTest 10880 6 = true := by
  decide +kernel

private theorem block171 : checkPow pointTest 10944 6 = true := by
  decide +kernel

private theorem block172 : checkPow pointTest 11008 6 = true := by
  decide +kernel

private theorem block173 : checkPow pointTest 11072 6 = true := by
  decide +kernel

private theorem block174 : checkPow pointTest 11136 6 = true := by
  decide +kernel

private theorem block175 : checkPow pointTest 11200 6 = true := by
  decide +kernel

private theorem block176 : checkPow pointTest 11264 6 = true := by
  decide +kernel

private theorem block177 : checkPow pointTest 11328 6 = true := by
  decide +kernel

private theorem block178 : checkPow pointTest 11392 6 = true := by
  decide +kernel

private theorem block179 : checkPow pointTest 11456 6 = true := by
  decide +kernel

private theorem block180 : checkPow pointTest 11520 6 = true := by
  decide +kernel

private theorem block181 : checkPow pointTest 11584 6 = true := by
  decide +kernel

private theorem block182 : checkPow pointTest 11648 6 = true := by
  decide +kernel

private theorem block183 : checkPow pointTest 11712 6 = true := by
  decide +kernel

private theorem block184 : checkPow pointTest 11776 6 = true := by
  decide +kernel

private theorem block185 : checkPow pointTest 11840 6 = true := by
  decide +kernel

private theorem block186 : checkPow pointTest 11904 6 = true := by
  decide +kernel

private theorem block187 : checkPow pointTest 11968 6 = true := by
  decide +kernel

private theorem block188 : checkPow pointTest 12032 6 = true := by
  decide +kernel

private theorem block189 : checkPow pointTest 12096 6 = true := by
  decide +kernel

private theorem block190 : checkPow pointTest 12160 6 = true := by
  decide +kernel

private theorem block191 : checkPow pointTest 12224 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked2 : checkPow pointTest 8192 12 = true :=
  (checkPow_join pointTest 11 8192
    (checkPow_join pointTest 10 8192
    (checkPow_join pointTest 9 8192
    (checkPow_join pointTest 8 8192
    (checkPow_join pointTest 7 8192
    (checkPow_join pointTest 6 8192
    block128
    block129)
    (checkPow_join pointTest 6 8320
    block130
    block131))
    (checkPow_join pointTest 7 8448
    (checkPow_join pointTest 6 8448
    block132
    block133)
    (checkPow_join pointTest 6 8576
    block134
    block135)))
    (checkPow_join pointTest 8 8704
    (checkPow_join pointTest 7 8704
    (checkPow_join pointTest 6 8704
    block136
    block137)
    (checkPow_join pointTest 6 8832
    block138
    block139))
    (checkPow_join pointTest 7 8960
    (checkPow_join pointTest 6 8960
    block140
    block141)
    (checkPow_join pointTest 6 9088
    block142
    block143))))
    (checkPow_join pointTest 9 9216
    (checkPow_join pointTest 8 9216
    (checkPow_join pointTest 7 9216
    (checkPow_join pointTest 6 9216
    block144
    block145)
    (checkPow_join pointTest 6 9344
    block146
    block147))
    (checkPow_join pointTest 7 9472
    (checkPow_join pointTest 6 9472
    block148
    block149)
    (checkPow_join pointTest 6 9600
    block150
    block151)))
    (checkPow_join pointTest 8 9728
    (checkPow_join pointTest 7 9728
    (checkPow_join pointTest 6 9728
    block152
    block153)
    (checkPow_join pointTest 6 9856
    block154
    block155))
    (checkPow_join pointTest 7 9984
    (checkPow_join pointTest 6 9984
    block156
    block157)
    (checkPow_join pointTest 6 10112
    block158
    block159)))))
    (checkPow_join pointTest 10 10240
    (checkPow_join pointTest 9 10240
    (checkPow_join pointTest 8 10240
    (checkPow_join pointTest 7 10240
    (checkPow_join pointTest 6 10240
    block160
    block161)
    (checkPow_join pointTest 6 10368
    block162
    block163))
    (checkPow_join pointTest 7 10496
    (checkPow_join pointTest 6 10496
    block164
    block165)
    (checkPow_join pointTest 6 10624
    block166
    block167)))
    (checkPow_join pointTest 8 10752
    (checkPow_join pointTest 7 10752
    (checkPow_join pointTest 6 10752
    block168
    block169)
    (checkPow_join pointTest 6 10880
    block170
    block171))
    (checkPow_join pointTest 7 11008
    (checkPow_join pointTest 6 11008
    block172
    block173)
    (checkPow_join pointTest 6 11136
    block174
    block175))))
    (checkPow_join pointTest 9 11264
    (checkPow_join pointTest 8 11264
    (checkPow_join pointTest 7 11264
    (checkPow_join pointTest 6 11264
    block176
    block177)
    (checkPow_join pointTest 6 11392
    block178
    block179))
    (checkPow_join pointTest 7 11520
    (checkPow_join pointTest 6 11520
    block180
    block181)
    (checkPow_join pointTest 6 11648
    block182
    block183)))
    (checkPow_join pointTest 8 11776
    (checkPow_join pointTest 7 11776
    (checkPow_join pointTest 6 11776
    block184
    block185)
    (checkPow_join pointTest 6 11904
    block186
    block187))
    (checkPow_join pointTest 7 12032
    (checkPow_join pointTest 6 12032
    block188
    block189)
    (checkPow_join pointTest 6 12160
    block190
    block191))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
