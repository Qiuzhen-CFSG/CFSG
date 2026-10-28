module

public import Theory.SpecificGroups.Tits.R1WordCertificate.Check00
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check01
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check02
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check03
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check04
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check05
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check06
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check07
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check08
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check09
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check10
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check11
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check12
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check13
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check14
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check15
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check16
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check17
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check18
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check19
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check20
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check21
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check22
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check23
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check24
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check25
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check26
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check27
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check28
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check29
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check30
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check31
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check32
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check33
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check34
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check35
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check36
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check37
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check38
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check39
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check40
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check41
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check42
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check43
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check44
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check45
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check46
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check47
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check48
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check49
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check50
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check51
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check52
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check53
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check54
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check55
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check56
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check57
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check58
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check59
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check60
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check61
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check62
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check63
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check64
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check65
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check66
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check67
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check68
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check69
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check70
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check71
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check72
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check73
public import Theory.SpecificGroups.Tits.R1WordCertificate.Check74

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

/-- All 304877 deductions follow from the actual model of the certificate. -/
theorem all_hold {G : Type*} [Group G] {H : Subgroup G}
    {g : ParrottR1Generator → G} {ρ : Nat → G}
    (valid : Valid context H g ρ) :
    ∀ n, n < 304877 → Holds H g ρ (facts n) := by
  have hall_0 := checkChunk_sound valid facts instructions 0 4096
    (fun n h => (Nat.not_lt_zero n h).elim) checked_0
  have hall_4096 := checkChunk_sound valid facts instructions 4096 4096
    hall_0 checked_4096
  have hall_8192 := checkChunk_sound valid facts instructions 8192 4096
    hall_4096 checked_8192
  have hall_12288 := checkChunk_sound valid facts instructions 12288 4096
    hall_8192 checked_12288
  have hall_16384 := checkChunk_sound valid facts instructions 16384 4096
    hall_12288 checked_16384
  have hall_20480 := checkChunk_sound valid facts instructions 20480 4096
    hall_16384 checked_20480
  have hall_24576 := checkChunk_sound valid facts instructions 24576 4096
    hall_20480 checked_24576
  have hall_28672 := checkChunk_sound valid facts instructions 28672 4096
    hall_24576 checked_28672
  have hall_32768 := checkChunk_sound valid facts instructions 32768 4096
    hall_28672 checked_32768
  have hall_36864 := checkChunk_sound valid facts instructions 36864 4096
    hall_32768 checked_36864
  have hall_40960 := checkChunk_sound valid facts instructions 40960 4096
    hall_36864 checked_40960
  have hall_45056 := checkChunk_sound valid facts instructions 45056 4096
    hall_40960 checked_45056
  have hall_49152 := checkChunk_sound valid facts instructions 49152 4096
    hall_45056 checked_49152
  have hall_53248 := checkChunk_sound valid facts instructions 53248 4096
    hall_49152 checked_53248
  have hall_57344 := checkChunk_sound valid facts instructions 57344 4096
    hall_53248 checked_57344
  have hall_61440 := checkChunk_sound valid facts instructions 61440 4096
    hall_57344 checked_61440
  have hall_65536 := checkChunk_sound valid facts instructions 65536 4096
    hall_61440 checked_65536
  have hall_69632 := checkChunk_sound valid facts instructions 69632 4096
    hall_65536 checked_69632
  have hall_73728 := checkChunk_sound valid facts instructions 73728 4096
    hall_69632 checked_73728
  have hall_77824 := checkChunk_sound valid facts instructions 77824 4096
    hall_73728 checked_77824
  have hall_81920 := checkChunk_sound valid facts instructions 81920 4096
    hall_77824 checked_81920
  have hall_86016 := checkChunk_sound valid facts instructions 86016 4096
    hall_81920 checked_86016
  have hall_90112 := checkChunk_sound valid facts instructions 90112 4096
    hall_86016 checked_90112
  have hall_94208 := checkChunk_sound valid facts instructions 94208 4096
    hall_90112 checked_94208
  have hall_98304 := checkChunk_sound valid facts instructions 98304 4096
    hall_94208 checked_98304
  have hall_102400 := checkChunk_sound valid facts instructions 102400 4096
    hall_98304 checked_102400
  have hall_106496 := checkChunk_sound valid facts instructions 106496 4096
    hall_102400 checked_106496
  have hall_110592 := checkChunk_sound valid facts instructions 110592 4096
    hall_106496 checked_110592
  have hall_114688 := checkChunk_sound valid facts instructions 114688 4096
    hall_110592 checked_114688
  have hall_118784 := checkChunk_sound valid facts instructions 118784 4096
    hall_114688 checked_118784
  have hall_122880 := checkChunk_sound valid facts instructions 122880 4096
    hall_118784 checked_122880
  have hall_126976 := checkChunk_sound valid facts instructions 126976 4096
    hall_122880 checked_126976
  have hall_131072 := checkChunk_sound valid facts instructions 131072 4096
    hall_126976 checked_131072
  have hall_135168 := checkChunk_sound valid facts instructions 135168 4096
    hall_131072 checked_135168
  have hall_139264 := checkChunk_sound valid facts instructions 139264 4096
    hall_135168 checked_139264
  have hall_143360 := checkChunk_sound valid facts instructions 143360 4096
    hall_139264 checked_143360
  have hall_147456 := checkChunk_sound valid facts instructions 147456 4096
    hall_143360 checked_147456
  have hall_151552 := checkChunk_sound valid facts instructions 151552 4096
    hall_147456 checked_151552
  have hall_155648 := checkChunk_sound valid facts instructions 155648 4096
    hall_151552 checked_155648
  have hall_159744 := checkChunk_sound valid facts instructions 159744 4096
    hall_155648 checked_159744
  have hall_163840 := checkChunk_sound valid facts instructions 163840 4096
    hall_159744 checked_163840
  have hall_167936 := checkChunk_sound valid facts instructions 167936 4096
    hall_163840 checked_167936
  have hall_172032 := checkChunk_sound valid facts instructions 172032 4096
    hall_167936 checked_172032
  have hall_176128 := checkChunk_sound valid facts instructions 176128 4096
    hall_172032 checked_176128
  have hall_180224 := checkChunk_sound valid facts instructions 180224 4096
    hall_176128 checked_180224
  have hall_184320 := checkChunk_sound valid facts instructions 184320 4096
    hall_180224 checked_184320
  have hall_188416 := checkChunk_sound valid facts instructions 188416 4096
    hall_184320 checked_188416
  have hall_192512 := checkChunk_sound valid facts instructions 192512 4096
    hall_188416 checked_192512
  have hall_196608 := checkChunk_sound valid facts instructions 196608 4096
    hall_192512 checked_196608
  have hall_200704 := checkChunk_sound valid facts instructions 200704 4096
    hall_196608 checked_200704
  have hall_204800 := checkChunk_sound valid facts instructions 204800 4096
    hall_200704 checked_204800
  have hall_208896 := checkChunk_sound valid facts instructions 208896 4096
    hall_204800 checked_208896
  have hall_212992 := checkChunk_sound valid facts instructions 212992 4096
    hall_208896 checked_212992
  have hall_217088 := checkChunk_sound valid facts instructions 217088 4096
    hall_212992 checked_217088
  have hall_221184 := checkChunk_sound valid facts instructions 221184 4096
    hall_217088 checked_221184
  have hall_225280 := checkChunk_sound valid facts instructions 225280 4096
    hall_221184 checked_225280
  have hall_229376 := checkChunk_sound valid facts instructions 229376 4096
    hall_225280 checked_229376
  have hall_233472 := checkChunk_sound valid facts instructions 233472 4096
    hall_229376 checked_233472
  have hall_237568 := checkChunk_sound valid facts instructions 237568 4096
    hall_233472 checked_237568
  have hall_241664 := checkChunk_sound valid facts instructions 241664 4096
    hall_237568 checked_241664
  have hall_245760 := checkChunk_sound valid facts instructions 245760 4096
    hall_241664 checked_245760
  have hall_249856 := checkChunk_sound valid facts instructions 249856 4096
    hall_245760 checked_249856
  have hall_253952 := checkChunk_sound valid facts instructions 253952 4096
    hall_249856 checked_253952
  have hall_258048 := checkChunk_sound valid facts instructions 258048 4096
    hall_253952 checked_258048
  have hall_262144 := checkChunk_sound valid facts instructions 262144 4096
    hall_258048 checked_262144
  have hall_266240 := checkChunk_sound valid facts instructions 266240 4096
    hall_262144 checked_266240
  have hall_270336 := checkChunk_sound valid facts instructions 270336 4096
    hall_266240 checked_270336
  have hall_274432 := checkChunk_sound valid facts instructions 274432 4096
    hall_270336 checked_274432
  have hall_278528 := checkChunk_sound valid facts instructions 278528 4096
    hall_274432 checked_278528
  have hall_282624 := checkChunk_sound valid facts instructions 282624 4096
    hall_278528 checked_282624
  have hall_286720 := checkChunk_sound valid facts instructions 286720 4096
    hall_282624 checked_286720
  have hall_290816 := checkChunk_sound valid facts instructions 290816 4096
    hall_286720 checked_290816
  have hall_294912 := checkChunk_sound valid facts instructions 294912 4096
    hall_290816 checked_294912
  have hall_299008 := checkChunk_sound valid facts instructions 299008 4096
    hall_294912 checked_299008
  have hall_303104 := checkChunk_sound valid facts instructions 303104 1773
    hall_299008 checked_303104
  exact hall_303104

end Tits.R1WordCertificate
