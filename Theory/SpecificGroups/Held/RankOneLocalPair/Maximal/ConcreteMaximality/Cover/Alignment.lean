module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Certificates
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Alignment36
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Alignment37

/-!
# The checked rows are exactly the original max5 cover words

The finite blocks certify all word triples against the existing Data module.
This assembly preserves every representative index and the last partial block.
Source: ../source/cover.json and SylowOvergroups/source/representatives.json.
-/

namespace Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate

public theorem actualRow_eq_certificateRow (j : Fin 4831) : actualRow j = certificateRow j := by
  by_cases h0 : j.val < 128
  · have hd : j.val / 128 = 0 := by omega
    have he : (⟨0+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 0+j.val%128 = j.val
      omega
    have h := Alignment00.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h1 : j.val < 256
  · have hd : j.val / 128 = 1 := by omega
    have he : (⟨128+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 128+j.val%128 = j.val
      omega
    have h := Alignment01.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h2 : j.val < 384
  · have hd : j.val / 128 = 2 := by omega
    have he : (⟨256+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 256+j.val%128 = j.val
      omega
    have h := Alignment02.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h3 : j.val < 512
  · have hd : j.val / 128 = 3 := by omega
    have he : (⟨384+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 384+j.val%128 = j.val
      omega
    have h := Alignment03.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h4 : j.val < 640
  · have hd : j.val / 128 = 4 := by omega
    have he : (⟨512+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 512+j.val%128 = j.val
      omega
    have h := Alignment04.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h5 : j.val < 768
  · have hd : j.val / 128 = 5 := by omega
    have he : (⟨640+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 640+j.val%128 = j.val
      omega
    have h := Alignment05.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h6 : j.val < 896
  · have hd : j.val / 128 = 6 := by omega
    have he : (⟨768+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 768+j.val%128 = j.val
      omega
    have h := Alignment06.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h7 : j.val < 1024
  · have hd : j.val / 128 = 7 := by omega
    have he : (⟨896+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 896+j.val%128 = j.val
      omega
    have h := Alignment07.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h8 : j.val < 1152
  · have hd : j.val / 128 = 8 := by omega
    have he : (⟨1024+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1024+j.val%128 = j.val
      omega
    have h := Alignment08.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h9 : j.val < 1280
  · have hd : j.val / 128 = 9 := by omega
    have he : (⟨1152+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1152+j.val%128 = j.val
      omega
    have h := Alignment09.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h10 : j.val < 1408
  · have hd : j.val / 128 = 10 := by omega
    have he : (⟨1280+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1280+j.val%128 = j.val
      omega
    have h := Alignment10.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h11 : j.val < 1536
  · have hd : j.val / 128 = 11 := by omega
    have he : (⟨1408+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1408+j.val%128 = j.val
      omega
    have h := Alignment11.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h12 : j.val < 1664
  · have hd : j.val / 128 = 12 := by omega
    have he : (⟨1536+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1536+j.val%128 = j.val
      omega
    have h := Alignment12.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h13 : j.val < 1792
  · have hd : j.val / 128 = 13 := by omega
    have he : (⟨1664+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1664+j.val%128 = j.val
      omega
    have h := Alignment13.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h14 : j.val < 1920
  · have hd : j.val / 128 = 14 := by omega
    have he : (⟨1792+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1792+j.val%128 = j.val
      omega
    have h := Alignment14.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h15 : j.val < 2048
  · have hd : j.val / 128 = 15 := by omega
    have he : (⟨1920+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 1920+j.val%128 = j.val
      omega
    have h := Alignment15.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h16 : j.val < 2176
  · have hd : j.val / 128 = 16 := by omega
    have he : (⟨2048+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2048+j.val%128 = j.val
      omega
    have h := Alignment16.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h17 : j.val < 2304
  · have hd : j.val / 128 = 17 := by omega
    have he : (⟨2176+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2176+j.val%128 = j.val
      omega
    have h := Alignment17.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h18 : j.val < 2432
  · have hd : j.val / 128 = 18 := by omega
    have he : (⟨2304+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2304+j.val%128 = j.val
      omega
    have h := Alignment18.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h19 : j.val < 2560
  · have hd : j.val / 128 = 19 := by omega
    have he : (⟨2432+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2432+j.val%128 = j.val
      omega
    have h := Alignment19.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h20 : j.val < 2688
  · have hd : j.val / 128 = 20 := by omega
    have he : (⟨2560+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2560+j.val%128 = j.val
      omega
    have h := Alignment20.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h21 : j.val < 2816
  · have hd : j.val / 128 = 21 := by omega
    have he : (⟨2688+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2688+j.val%128 = j.val
      omega
    have h := Alignment21.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h22 : j.val < 2944
  · have hd : j.val / 128 = 22 := by omega
    have he : (⟨2816+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2816+j.val%128 = j.val
      omega
    have h := Alignment22.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h23 : j.val < 3072
  · have hd : j.val / 128 = 23 := by omega
    have he : (⟨2944+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 2944+j.val%128 = j.val
      omega
    have h := Alignment23.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h24 : j.val < 3200
  · have hd : j.val / 128 = 24 := by omega
    have he : (⟨3072+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3072+j.val%128 = j.val
      omega
    have h := Alignment24.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h25 : j.val < 3328
  · have hd : j.val / 128 = 25 := by omega
    have he : (⟨3200+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3200+j.val%128 = j.val
      omega
    have h := Alignment25.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h26 : j.val < 3456
  · have hd : j.val / 128 = 26 := by omega
    have he : (⟨3328+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3328+j.val%128 = j.val
      omega
    have h := Alignment26.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h27 : j.val < 3584
  · have hd : j.val / 128 = 27 := by omega
    have he : (⟨3456+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3456+j.val%128 = j.val
      omega
    have h := Alignment27.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h28 : j.val < 3712
  · have hd : j.val / 128 = 28 := by omega
    have he : (⟨3584+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3584+j.val%128 = j.val
      omega
    have h := Alignment28.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h29 : j.val < 3840
  · have hd : j.val / 128 = 29 := by omega
    have he : (⟨3712+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3712+j.val%128 = j.val
      omega
    have h := Alignment29.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h30 : j.val < 3968
  · have hd : j.val / 128 = 30 := by omega
    have he : (⟨3840+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3840+j.val%128 = j.val
      omega
    have h := Alignment30.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h31 : j.val < 4096
  · have hd : j.val / 128 = 31 := by omega
    have he : (⟨3968+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 3968+j.val%128 = j.val
      omega
    have h := Alignment31.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h32 : j.val < 4224
  · have hd : j.val / 128 = 32 := by omega
    have he : (⟨4096+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 4096+j.val%128 = j.val
      omega
    have h := Alignment32.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h33 : j.val < 4352
  · have hd : j.val / 128 = 33 := by omega
    have he : (⟨4224+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 4224+j.val%128 = j.val
      omega
    have h := Alignment33.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h34 : j.val < 4480
  · have hd : j.val / 128 = 34 := by omega
    have he : (⟨4352+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 4352+j.val%128 = j.val
      omega
    have h := Alignment34.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h35 : j.val < 4608
  · have hd : j.val / 128 = 35 := by omega
    have he : (⟨4480+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 4480+j.val%128 = j.val
      omega
    have h := Alignment35.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  by_cases h36 : j.val < 4736
  · have hd : j.val / 128 = 36 := by omega
    have he : (⟨4608+j.val%128, by omega⟩ : Fin 4831) = j := by
      apply Fin.ext
      change 4608+j.val%128 = j.val
      omega
    have h := Alignment36.aligned ⟨j.val%128, Nat.mod_lt _ (by decide)⟩
    rw [he] at h
    simpa only [certificateRow, hd] using h
  have hd : j.val / 128 = 37 := by omega
  have he : (⟨4736+j.val%128, by omega⟩ : Fin 4831) = j := by
    apply Fin.ext
    change 4736+j.val%128 = j.val
    omega
  have h := Alignment37.aligned ⟨j.val%128, by omega⟩
  rw [he] at h
  simpa only [certificateRow, hd] using h

end Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
