module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check00
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check01
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check02
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check03
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check04
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check05
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check06
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Check07

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

/-- Soundness of all 249178 deductions in any actual group model. -/
theorem all_hold {G : Type*} [Group G] {H : Subgroup G}
    {g : Fin 3 → G} {ρ : Nat → G} (valid : Valid context H g ρ) :
    ∀ n, n < 249178 → Holds H g ρ (facts n) := by
  have hall_0 := checkBoolChunk_sound valid facts instructions 0 4096
    (fun n h => (Nat.not_lt_zero n h).elim) checked_0
  have hall_4096 := checkBoolChunk_sound valid facts instructions 4096 4096
    hall_0 checked_4096
  have hall_8192 := checkBoolChunk_sound valid facts instructions 8192 4096
    hall_4096 checked_8192
  have hall_12288 := checkBoolChunk_sound valid facts instructions 12288 4096
    hall_8192 checked_12288
  have hall_16384 := checkBoolChunk_sound valid facts instructions 16384 4096
    hall_12288 checked_16384
  have hall_20480 := checkBoolChunk_sound valid facts instructions 20480 4096
    hall_16384 checked_20480
  have hall_24576 := checkBoolChunk_sound valid facts instructions 24576 4096
    hall_20480 checked_24576
  have hall_28672 := checkBoolChunk_sound valid facts instructions 28672 4096
    hall_24576 checked_28672
  have hall_32768 := checkBoolChunk_sound valid facts instructions 32768 4096
    hall_28672 checked_32768
  have hall_36864 := checkBoolChunk_sound valid facts instructions 36864 4096
    hall_32768 checked_36864
  have hall_40960 := checkBoolChunk_sound valid facts instructions 40960 4096
    hall_36864 checked_40960
  have hall_45056 := checkBoolChunk_sound valid facts instructions 45056 4096
    hall_40960 checked_45056
  have hall_49152 := checkBoolChunk_sound valid facts instructions 49152 4096
    hall_45056 checked_49152
  have hall_53248 := checkBoolChunk_sound valid facts instructions 53248 4096
    hall_49152 checked_53248
  have hall_57344 := checkBoolChunk_sound valid facts instructions 57344 4096
    hall_53248 checked_57344
  have hall_61440 := checkBoolChunk_sound valid facts instructions 61440 4096
    hall_57344 checked_61440
  have hall_65536 := checkBoolChunk_sound valid facts instructions 65536 4096
    hall_61440 checked_65536
  have hall_69632 := checkBoolChunk_sound valid facts instructions 69632 4096
    hall_65536 checked_69632
  have hall_73728 := checkBoolChunk_sound valid facts instructions 73728 4096
    hall_69632 checked_73728
  have hall_77824 := checkBoolChunk_sound valid facts instructions 77824 4096
    hall_73728 checked_77824
  have hall_81920 := checkBoolChunk_sound valid facts instructions 81920 4096
    hall_77824 checked_81920
  have hall_86016 := checkBoolChunk_sound valid facts instructions 86016 4096
    hall_81920 checked_86016
  have hall_90112 := checkBoolChunk_sound valid facts instructions 90112 4096
    hall_86016 checked_90112
  have hall_94208 := checkBoolChunk_sound valid facts instructions 94208 4096
    hall_90112 checked_94208
  have hall_98304 := checkBoolChunk_sound valid facts instructions 98304 4096
    hall_94208 checked_98304
  have hall_102400 := checkBoolChunk_sound valid facts instructions 102400 4096
    hall_98304 checked_102400
  have hall_106496 := checkBoolChunk_sound valid facts instructions 106496 4096
    hall_102400 checked_106496
  have hall_110592 := checkBoolChunk_sound valid facts instructions 110592 4096
    hall_106496 checked_110592
  have hall_114688 := checkBoolChunk_sound valid facts instructions 114688 4096
    hall_110592 checked_114688
  have hall_118784 := checkBoolChunk_sound valid facts instructions 118784 4096
    hall_114688 checked_118784
  have hall_122880 := checkBoolChunk_sound valid facts instructions 122880 4096
    hall_118784 checked_122880
  have hall_126976 := checkBoolChunk_sound valid facts instructions 126976 4096
    hall_122880 checked_126976
  have hall_131072 := checkBoolChunk_sound valid facts instructions 131072 4096
    hall_126976 checked_131072
  have hall_135168 := checkBoolChunk_sound valid facts instructions 135168 4096
    hall_131072 checked_135168
  have hall_139264 := checkBoolChunk_sound valid facts instructions 139264 4096
    hall_135168 checked_139264
  have hall_143360 := checkBoolChunk_sound valid facts instructions 143360 4096
    hall_139264 checked_143360
  have hall_147456 := checkBoolChunk_sound valid facts instructions 147456 4096
    hall_143360 checked_147456
  have hall_151552 := checkBoolChunk_sound valid facts instructions 151552 4096
    hall_147456 checked_151552
  have hall_155648 := checkBoolChunk_sound valid facts instructions 155648 4096
    hall_151552 checked_155648
  have hall_159744 := checkBoolChunk_sound valid facts instructions 159744 4096
    hall_155648 checked_159744
  have hall_163840 := checkBoolChunk_sound valid facts instructions 163840 4096
    hall_159744 checked_163840
  have hall_167936 := checkBoolChunk_sound valid facts instructions 167936 4096
    hall_163840 checked_167936
  have hall_172032 := checkBoolChunk_sound valid facts instructions 172032 4096
    hall_167936 checked_172032
  have hall_176128 := checkBoolChunk_sound valid facts instructions 176128 4096
    hall_172032 checked_176128
  have hall_180224 := checkBoolChunk_sound valid facts instructions 180224 4096
    hall_176128 checked_180224
  have hall_184320 := checkBoolChunk_sound valid facts instructions 184320 4096
    hall_180224 checked_184320
  have hall_188416 := checkBoolChunk_sound valid facts instructions 188416 4096
    hall_184320 checked_188416
  have hall_192512 := checkBoolChunk_sound valid facts instructions 192512 4096
    hall_188416 checked_192512
  have hall_196608 := checkBoolChunk_sound valid facts instructions 196608 4096
    hall_192512 checked_196608
  have hall_200704 := checkBoolChunk_sound valid facts instructions 200704 4096
    hall_196608 checked_200704
  have hall_204800 := checkBoolChunk_sound valid facts instructions 204800 4096
    hall_200704 checked_204800
  have hall_208896 := checkBoolChunk_sound valid facts instructions 208896 4096
    hall_204800 checked_208896
  have hall_212992 := checkBoolChunk_sound valid facts instructions 212992 4096
    hall_208896 checked_212992
  have hall_217088 := checkBoolChunk_sound valid facts instructions 217088 4096
    hall_212992 checked_217088
  have hall_221184 := checkBoolChunk_sound valid facts instructions 221184 4096
    hall_217088 checked_221184
  have hall_225280 := checkBoolChunk_sound valid facts instructions 225280 4096
    hall_221184 checked_225280
  have hall_229376 := checkBoolChunk_sound valid facts instructions 229376 4096
    hall_225280 checked_229376
  have hall_233472 := checkBoolChunk_sound valid facts instructions 233472 4096
    hall_229376 checked_233472
  have hall_237568 := checkBoolChunk_sound valid facts instructions 237568 4096
    hall_233472 checked_237568
  have hall_241664 := checkBoolChunk_sound valid facts instructions 241664 4096
    hall_237568 checked_241664
  have hall_245760 := checkBoolChunk_sound valid facts instructions 245760 3418
    hall_241664 checked_245760
  exact hall_245760

end Lyons.Gebhardt.ParabolicIndexCertificate
