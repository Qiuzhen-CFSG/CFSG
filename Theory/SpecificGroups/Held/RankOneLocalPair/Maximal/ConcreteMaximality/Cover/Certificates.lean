module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Checks36
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Checks37

/-!
# The complete checked collection of max5 cover words

The 38 bounded blocks contain 4,831 rows. This module selects the original
zero-based row and proves that every selected row passed its kernel check.
The independent `Alignment` module identifies these rows with the unchanged
production data. Source: ../source/cover.json and the ATLAS words cited there.
-/

namespace Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate

@[expose] public def certificateRow (j : Fin 4831) : Row :=
  (match j.val / 128 with
    | 0 => Checks00.rows
    | 1 => Checks01.rows
    | 2 => Checks02.rows
    | 3 => Checks03.rows
    | 4 => Checks04.rows
    | 5 => Checks05.rows
    | 6 => Checks06.rows
    | 7 => Checks07.rows
    | 8 => Checks08.rows
    | 9 => Checks09.rows
    | 10 => Checks10.rows
    | 11 => Checks11.rows
    | 12 => Checks12.rows
    | 13 => Checks13.rows
    | 14 => Checks14.rows
    | 15 => Checks15.rows
    | 16 => Checks16.rows
    | 17 => Checks17.rows
    | 18 => Checks18.rows
    | 19 => Checks19.rows
    | 20 => Checks20.rows
    | 21 => Checks21.rows
    | 22 => Checks22.rows
    | 23 => Checks23.rows
    | 24 => Checks24.rows
    | 25 => Checks25.rows
    | 26 => Checks26.rows
    | 27 => Checks27.rows
    | 28 => Checks28.rows
    | 29 => Checks29.rows
    | 30 => Checks30.rows
    | 31 => Checks31.rows
    | 32 => Checks32.rows
    | 33 => Checks33.rows
    | 34 => Checks34.rows
    | 35 => Checks35.rows
    | 36 => Checks36.rows
    | _ => Checks37.rows)[j.val % 128]!

public theorem certificate_checked (j : Fin 4831) :
    rowCheck (certificateRow j) = true := by
  by_cases h0 : j.val < 128
  · have hd : j.val / 128 = 0 := by omega
    simpa only [certificateRow, hd] using
      Checks00.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h1 : j.val < 256
  · have hd : j.val / 128 = 1 := by omega
    simpa only [certificateRow, hd] using
      Checks01.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h2 : j.val < 384
  · have hd : j.val / 128 = 2 := by omega
    simpa only [certificateRow, hd] using
      Checks02.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h3 : j.val < 512
  · have hd : j.val / 128 = 3 := by omega
    simpa only [certificateRow, hd] using
      Checks03.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h4 : j.val < 640
  · have hd : j.val / 128 = 4 := by omega
    simpa only [certificateRow, hd] using
      Checks04.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h5 : j.val < 768
  · have hd : j.val / 128 = 5 := by omega
    simpa only [certificateRow, hd] using
      Checks05.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h6 : j.val < 896
  · have hd : j.val / 128 = 6 := by omega
    simpa only [certificateRow, hd] using
      Checks06.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h7 : j.val < 1024
  · have hd : j.val / 128 = 7 := by omega
    simpa only [certificateRow, hd] using
      Checks07.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h8 : j.val < 1152
  · have hd : j.val / 128 = 8 := by omega
    simpa only [certificateRow, hd] using
      Checks08.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h9 : j.val < 1280
  · have hd : j.val / 128 = 9 := by omega
    simpa only [certificateRow, hd] using
      Checks09.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h10 : j.val < 1408
  · have hd : j.val / 128 = 10 := by omega
    simpa only [certificateRow, hd] using
      Checks10.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h11 : j.val < 1536
  · have hd : j.val / 128 = 11 := by omega
    simpa only [certificateRow, hd] using
      Checks11.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h12 : j.val < 1664
  · have hd : j.val / 128 = 12 := by omega
    simpa only [certificateRow, hd] using
      Checks12.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h13 : j.val < 1792
  · have hd : j.val / 128 = 13 := by omega
    simpa only [certificateRow, hd] using
      Checks13.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h14 : j.val < 1920
  · have hd : j.val / 128 = 14 := by omega
    simpa only [certificateRow, hd] using
      Checks14.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h15 : j.val < 2048
  · have hd : j.val / 128 = 15 := by omega
    simpa only [certificateRow, hd] using
      Checks15.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h16 : j.val < 2176
  · have hd : j.val / 128 = 16 := by omega
    simpa only [certificateRow, hd] using
      Checks16.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h17 : j.val < 2304
  · have hd : j.val / 128 = 17 := by omega
    simpa only [certificateRow, hd] using
      Checks17.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h18 : j.val < 2432
  · have hd : j.val / 128 = 18 := by omega
    simpa only [certificateRow, hd] using
      Checks18.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h19 : j.val < 2560
  · have hd : j.val / 128 = 19 := by omega
    simpa only [certificateRow, hd] using
      Checks19.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h20 : j.val < 2688
  · have hd : j.val / 128 = 20 := by omega
    simpa only [certificateRow, hd] using
      Checks20.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h21 : j.val < 2816
  · have hd : j.val / 128 = 21 := by omega
    simpa only [certificateRow, hd] using
      Checks21.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h22 : j.val < 2944
  · have hd : j.val / 128 = 22 := by omega
    simpa only [certificateRow, hd] using
      Checks22.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h23 : j.val < 3072
  · have hd : j.val / 128 = 23 := by omega
    simpa only [certificateRow, hd] using
      Checks23.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h24 : j.val < 3200
  · have hd : j.val / 128 = 24 := by omega
    simpa only [certificateRow, hd] using
      Checks24.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h25 : j.val < 3328
  · have hd : j.val / 128 = 25 := by omega
    simpa only [certificateRow, hd] using
      Checks25.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h26 : j.val < 3456
  · have hd : j.val / 128 = 26 := by omega
    simpa only [certificateRow, hd] using
      Checks26.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h27 : j.val < 3584
  · have hd : j.val / 128 = 27 := by omega
    simpa only [certificateRow, hd] using
      Checks27.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h28 : j.val < 3712
  · have hd : j.val / 128 = 28 := by omega
    simpa only [certificateRow, hd] using
      Checks28.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h29 : j.val < 3840
  · have hd : j.val / 128 = 29 := by omega
    simpa only [certificateRow, hd] using
      Checks29.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h30 : j.val < 3968
  · have hd : j.val / 128 = 30 := by omega
    simpa only [certificateRow, hd] using
      Checks30.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h31 : j.val < 4096
  · have hd : j.val / 128 = 31 := by omega
    simpa only [certificateRow, hd] using
      Checks31.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h32 : j.val < 4224
  · have hd : j.val / 128 = 32 := by omega
    simpa only [certificateRow, hd] using
      Checks32.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h33 : j.val < 4352
  · have hd : j.val / 128 = 33 := by omega
    simpa only [certificateRow, hd] using
      Checks33.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h34 : j.val < 4480
  · have hd : j.val / 128 = 34 := by omega
    simpa only [certificateRow, hd] using
      Checks34.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h35 : j.val < 4608
  · have hd : j.val / 128 = 35 := by omega
    simpa only [certificateRow, hd] using
      Checks35.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  by_cases h36 : j.val < 4736
  · have hd : j.val / 128 = 36 := by omega
    simpa only [certificateRow, hd] using
      Checks36.checked ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  have hd : j.val / 128 = 37 := by omega
  simpa only [certificateRow, hd] using
    Checks37.checked ⟨j.val % 128, by omega⟩

end Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
