module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Tables

/-!
# Checked action equation for shared register 72

This is a complete finite equality on the original 31671 letters. Splitting
its balanced check into 256-letter declarations bounds kernel memory. The
algebraic connection to the actual subgroup word is made in `Core.Actions`.

Source: retained ATLAS F23G1-p31671B0 in the inverse-cycle convention;
GLS3 Table 5.3u. Reproduce with `Core/source/generate.py`.
-/

set_option Elab.async false

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Core.Check72
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private def pointTest (n : Nat) : Bool :=
  let x := Fin.ofNat 31671 n
  (KernelUpperData.lookup blocks72 x).val == (KernelUpperData.lookup blocks49 (KernelUpperData.lookup blocks49 (KernelUpperData.lookup blocks67 (KernelUpperData.lookup blocks54 (KernelUpperData.lookup blocks49 (KernelUpperData.lookup blocks49 (x))))))).val

private theorem block0 : checkPow pointTest 0 8 = true := by decide +kernel

private theorem block1 : checkPow pointTest 256 8 = true := by decide +kernel

private theorem block2 : checkPow pointTest 512 8 = true := by decide +kernel

private theorem block3 : checkPow pointTest 768 8 = true := by decide +kernel

private theorem block4 : checkPow pointTest 1024 8 = true := by decide +kernel

private theorem block5 : checkPow pointTest 1280 8 = true := by decide +kernel

private theorem block6 : checkPow pointTest 1536 8 = true := by decide +kernel

private theorem block7 : checkPow pointTest 1792 8 = true := by decide +kernel

private theorem block8 : checkPow pointTest 2048 8 = true := by decide +kernel

private theorem block9 : checkPow pointTest 2304 8 = true := by decide +kernel

private theorem block10 : checkPow pointTest 2560 8 = true := by decide +kernel

private theorem block11 : checkPow pointTest 2816 8 = true := by decide +kernel

private theorem block12 : checkPow pointTest 3072 8 = true := by decide +kernel

private theorem block13 : checkPow pointTest 3328 8 = true := by decide +kernel

private theorem block14 : checkPow pointTest 3584 8 = true := by decide +kernel

private theorem block15 : checkPow pointTest 3840 8 = true := by decide +kernel

private theorem block16 : checkPow pointTest 4096 8 = true := by decide +kernel

private theorem block17 : checkPow pointTest 4352 8 = true := by decide +kernel

private theorem block18 : checkPow pointTest 4608 8 = true := by decide +kernel

private theorem block19 : checkPow pointTest 4864 8 = true := by decide +kernel

private theorem block20 : checkPow pointTest 5120 8 = true := by decide +kernel

private theorem block21 : checkPow pointTest 5376 8 = true := by decide +kernel

private theorem block22 : checkPow pointTest 5632 8 = true := by decide +kernel

private theorem block23 : checkPow pointTest 5888 8 = true := by decide +kernel

private theorem block24 : checkPow pointTest 6144 8 = true := by decide +kernel

private theorem block25 : checkPow pointTest 6400 8 = true := by decide +kernel

private theorem block26 : checkPow pointTest 6656 8 = true := by decide +kernel

private theorem block27 : checkPow pointTest 6912 8 = true := by decide +kernel

private theorem block28 : checkPow pointTest 7168 8 = true := by decide +kernel

private theorem block29 : checkPow pointTest 7424 8 = true := by decide +kernel

private theorem block30 : checkPow pointTest 7680 8 = true := by decide +kernel

private theorem block31 : checkPow pointTest 7936 8 = true := by decide +kernel

private theorem block32 : checkPow pointTest 8192 8 = true := by decide +kernel

private theorem block33 : checkPow pointTest 8448 8 = true := by decide +kernel

private theorem block34 : checkPow pointTest 8704 8 = true := by decide +kernel

private theorem block35 : checkPow pointTest 8960 8 = true := by decide +kernel

private theorem block36 : checkPow pointTest 9216 8 = true := by decide +kernel

private theorem block37 : checkPow pointTest 9472 8 = true := by decide +kernel

private theorem block38 : checkPow pointTest 9728 8 = true := by decide +kernel

private theorem block39 : checkPow pointTest 9984 8 = true := by decide +kernel

private theorem block40 : checkPow pointTest 10240 8 = true := by decide +kernel

private theorem block41 : checkPow pointTest 10496 8 = true := by decide +kernel

private theorem block42 : checkPow pointTest 10752 8 = true := by decide +kernel

private theorem block43 : checkPow pointTest 11008 8 = true := by decide +kernel

private theorem block44 : checkPow pointTest 11264 8 = true := by decide +kernel

private theorem block45 : checkPow pointTest 11520 8 = true := by decide +kernel

private theorem block46 : checkPow pointTest 11776 8 = true := by decide +kernel

private theorem block47 : checkPow pointTest 12032 8 = true := by decide +kernel

private theorem block48 : checkPow pointTest 12288 8 = true := by decide +kernel

private theorem block49 : checkPow pointTest 12544 8 = true := by decide +kernel

private theorem block50 : checkPow pointTest 12800 8 = true := by decide +kernel

private theorem block51 : checkPow pointTest 13056 8 = true := by decide +kernel

private theorem block52 : checkPow pointTest 13312 8 = true := by decide +kernel

private theorem block53 : checkPow pointTest 13568 8 = true := by decide +kernel

private theorem block54 : checkPow pointTest 13824 8 = true := by decide +kernel

private theorem block55 : checkPow pointTest 14080 8 = true := by decide +kernel

private theorem block56 : checkPow pointTest 14336 8 = true := by decide +kernel

private theorem block57 : checkPow pointTest 14592 8 = true := by decide +kernel

private theorem block58 : checkPow pointTest 14848 8 = true := by decide +kernel

private theorem block59 : checkPow pointTest 15104 8 = true := by decide +kernel

private theorem block60 : checkPow pointTest 15360 8 = true := by decide +kernel

private theorem block61 : checkPow pointTest 15616 8 = true := by decide +kernel

private theorem block62 : checkPow pointTest 15872 8 = true := by decide +kernel

private theorem block63 : checkPow pointTest 16128 8 = true := by decide +kernel

private theorem block64 : checkPow pointTest 16384 8 = true := by decide +kernel

private theorem block65 : checkPow pointTest 16640 8 = true := by decide +kernel

private theorem block66 : checkPow pointTest 16896 8 = true := by decide +kernel

private theorem block67 : checkPow pointTest 17152 8 = true := by decide +kernel

private theorem block68 : checkPow pointTest 17408 8 = true := by decide +kernel

private theorem block69 : checkPow pointTest 17664 8 = true := by decide +kernel

private theorem block70 : checkPow pointTest 17920 8 = true := by decide +kernel

private theorem block71 : checkPow pointTest 18176 8 = true := by decide +kernel

private theorem block72 : checkPow pointTest 18432 8 = true := by decide +kernel

private theorem block73 : checkPow pointTest 18688 8 = true := by decide +kernel

private theorem block74 : checkPow pointTest 18944 8 = true := by decide +kernel

private theorem block75 : checkPow pointTest 19200 8 = true := by decide +kernel

private theorem block76 : checkPow pointTest 19456 8 = true := by decide +kernel

private theorem block77 : checkPow pointTest 19712 8 = true := by decide +kernel

private theorem block78 : checkPow pointTest 19968 8 = true := by decide +kernel

private theorem block79 : checkPow pointTest 20224 8 = true := by decide +kernel

private theorem block80 : checkPow pointTest 20480 8 = true := by decide +kernel

private theorem block81 : checkPow pointTest 20736 8 = true := by decide +kernel

private theorem block82 : checkPow pointTest 20992 8 = true := by decide +kernel

private theorem block83 : checkPow pointTest 21248 8 = true := by decide +kernel

private theorem block84 : checkPow pointTest 21504 8 = true := by decide +kernel

private theorem block85 : checkPow pointTest 21760 8 = true := by decide +kernel

private theorem block86 : checkPow pointTest 22016 8 = true := by decide +kernel

private theorem block87 : checkPow pointTest 22272 8 = true := by decide +kernel

private theorem block88 : checkPow pointTest 22528 8 = true := by decide +kernel

private theorem block89 : checkPow pointTest 22784 8 = true := by decide +kernel

private theorem block90 : checkPow pointTest 23040 8 = true := by decide +kernel

private theorem block91 : checkPow pointTest 23296 8 = true := by decide +kernel

private theorem block92 : checkPow pointTest 23552 8 = true := by decide +kernel

private theorem block93 : checkPow pointTest 23808 8 = true := by decide +kernel

private theorem block94 : checkPow pointTest 24064 8 = true := by decide +kernel

private theorem block95 : checkPow pointTest 24320 8 = true := by decide +kernel

private theorem block96 : checkPow pointTest 24576 8 = true := by decide +kernel

private theorem block97 : checkPow pointTest 24832 8 = true := by decide +kernel

private theorem block98 : checkPow pointTest 25088 8 = true := by decide +kernel

private theorem block99 : checkPow pointTest 25344 8 = true := by decide +kernel

private theorem block100 : checkPow pointTest 25600 8 = true := by decide +kernel

private theorem block101 : checkPow pointTest 25856 8 = true := by decide +kernel

private theorem block102 : checkPow pointTest 26112 8 = true := by decide +kernel

private theorem block103 : checkPow pointTest 26368 8 = true := by decide +kernel

private theorem block104 : checkPow pointTest 26624 8 = true := by decide +kernel

private theorem block105 : checkPow pointTest 26880 8 = true := by decide +kernel

private theorem block106 : checkPow pointTest 27136 8 = true := by decide +kernel

private theorem block107 : checkPow pointTest 27392 8 = true := by decide +kernel

private theorem block108 : checkPow pointTest 27648 8 = true := by decide +kernel

private theorem block109 : checkPow pointTest 27904 8 = true := by decide +kernel

private theorem block110 : checkPow pointTest 28160 8 = true := by decide +kernel

private theorem block111 : checkPow pointTest 28416 8 = true := by decide +kernel

private theorem block112 : checkPow pointTest 28672 8 = true := by decide +kernel

private theorem block113 : checkPow pointTest 28928 8 = true := by decide +kernel

private theorem block114 : checkPow pointTest 29184 8 = true := by decide +kernel

private theorem block115 : checkPow pointTest 29440 8 = true := by decide +kernel

private theorem block116 : checkPow pointTest 29696 8 = true := by decide +kernel

private theorem block117 : checkPow pointTest 29952 8 = true := by decide +kernel

private theorem block118 : checkPow pointTest 30208 8 = true := by decide +kernel

private theorem block119 : checkPow pointTest 30464 8 = true := by decide +kernel

private theorem block120 : checkPow pointTest 30720 8 = true := by decide +kernel

private theorem block121 : checkPow pointTest 30976 8 = true := by decide +kernel

private theorem block122 : checkPow pointTest 31232 8 = true := by decide +kernel

private theorem block123 : checkPow pointTest 31488 8 = true := by decide +kernel

private theorem block124 : checkPow pointTest 31744 8 = true := by decide +kernel

private theorem block125 : checkPow pointTest 32000 8 = true := by decide +kernel

private theorem block126 : checkPow pointTest 32256 8 = true := by decide +kernel

private theorem block127 : checkPow pointTest 32512 8 = true := by decide +kernel

private theorem checked : checkPow pointTest 0 15 = true :=
  (checkPow_join pointTest 14 0 (checkPow_join pointTest 13 0 (checkPow_join pointTest 12 0 (checkPow_join pointTest 11 0 (checkPow_join pointTest 10 0 (checkPow_join pointTest 9 0 (checkPow_join pointTest 8 0 block0 block1) (checkPow_join pointTest 8 512 block2 block3)) (checkPow_join pointTest 9 1024 (checkPow_join pointTest 8 1024 block4 block5) (checkPow_join pointTest 8 1536 block6 block7))) (checkPow_join pointTest 10 2048 (checkPow_join pointTest 9 2048 (checkPow_join pointTest 8 2048 block8 block9) (checkPow_join pointTest 8 2560 block10 block11)) (checkPow_join pointTest 9 3072 (checkPow_join pointTest 8 3072 block12 block13) (checkPow_join pointTest 8 3584 block14 block15)))) (checkPow_join pointTest 11 4096 (checkPow_join pointTest 10 4096 (checkPow_join pointTest 9 4096 (checkPow_join pointTest 8 4096 block16 block17) (checkPow_join pointTest 8 4608 block18 block19)) (checkPow_join pointTest 9 5120 (checkPow_join pointTest 8 5120 block20 block21) (checkPow_join pointTest 8 5632 block22 block23))) (checkPow_join pointTest 10 6144 (checkPow_join pointTest 9 6144 (checkPow_join pointTest 8 6144 block24 block25) (checkPow_join pointTest 8 6656 block26 block27)) (checkPow_join pointTest 9 7168 (checkPow_join pointTest 8 7168 block28 block29) (checkPow_join pointTest 8 7680 block30 block31))))) (checkPow_join pointTest 12 8192 (checkPow_join pointTest 11 8192 (checkPow_join pointTest 10 8192 (checkPow_join pointTest 9 8192 (checkPow_join pointTest 8 8192 block32 block33) (checkPow_join pointTest 8 8704 block34 block35)) (checkPow_join pointTest 9 9216 (checkPow_join pointTest 8 9216 block36 block37) (checkPow_join pointTest 8 9728 block38 block39))) (checkPow_join pointTest 10 10240 (checkPow_join pointTest 9 10240 (checkPow_join pointTest 8 10240 block40 block41) (checkPow_join pointTest 8 10752 block42 block43)) (checkPow_join pointTest 9 11264 (checkPow_join pointTest 8 11264 block44 block45) (checkPow_join pointTest 8 11776 block46 block47)))) (checkPow_join pointTest 11 12288 (checkPow_join pointTest 10 12288 (checkPow_join pointTest 9 12288 (checkPow_join pointTest 8 12288 block48 block49) (checkPow_join pointTest 8 12800 block50 block51)) (checkPow_join pointTest 9 13312 (checkPow_join pointTest 8 13312 block52 block53) (checkPow_join pointTest 8 13824 block54 block55))) (checkPow_join pointTest 10 14336 (checkPow_join pointTest 9 14336 (checkPow_join pointTest 8 14336 block56 block57) (checkPow_join pointTest 8 14848 block58 block59)) (checkPow_join pointTest 9 15360 (checkPow_join pointTest 8 15360 block60 block61) (checkPow_join pointTest 8 15872 block62 block63)))))) (checkPow_join pointTest 13 16384 (checkPow_join pointTest 12 16384 (checkPow_join pointTest 11 16384 (checkPow_join pointTest 10 16384 (checkPow_join pointTest 9 16384 (checkPow_join pointTest 8 16384 block64 block65) (checkPow_join pointTest 8 16896 block66 block67)) (checkPow_join pointTest 9 17408 (checkPow_join pointTest 8 17408 block68 block69) (checkPow_join pointTest 8 17920 block70 block71))) (checkPow_join pointTest 10 18432 (checkPow_join pointTest 9 18432 (checkPow_join pointTest 8 18432 block72 block73) (checkPow_join pointTest 8 18944 block74 block75)) (checkPow_join pointTest 9 19456 (checkPow_join pointTest 8 19456 block76 block77) (checkPow_join pointTest 8 19968 block78 block79)))) (checkPow_join pointTest 11 20480 (checkPow_join pointTest 10 20480 (checkPow_join pointTest 9 20480 (checkPow_join pointTest 8 20480 block80 block81) (checkPow_join pointTest 8 20992 block82 block83)) (checkPow_join pointTest 9 21504 (checkPow_join pointTest 8 21504 block84 block85) (checkPow_join pointTest 8 22016 block86 block87))) (checkPow_join pointTest 10 22528 (checkPow_join pointTest 9 22528 (checkPow_join pointTest 8 22528 block88 block89) (checkPow_join pointTest 8 23040 block90 block91)) (checkPow_join pointTest 9 23552 (checkPow_join pointTest 8 23552 block92 block93) (checkPow_join pointTest 8 24064 block94 block95))))) (checkPow_join pointTest 12 24576 (checkPow_join pointTest 11 24576 (checkPow_join pointTest 10 24576 (checkPow_join pointTest 9 24576 (checkPow_join pointTest 8 24576 block96 block97) (checkPow_join pointTest 8 25088 block98 block99)) (checkPow_join pointTest 9 25600 (checkPow_join pointTest 8 25600 block100 block101) (checkPow_join pointTest 8 26112 block102 block103))) (checkPow_join pointTest 10 26624 (checkPow_join pointTest 9 26624 (checkPow_join pointTest 8 26624 block104 block105) (checkPow_join pointTest 8 27136 block106 block107)) (checkPow_join pointTest 9 27648 (checkPow_join pointTest 8 27648 block108 block109) (checkPow_join pointTest 8 28160 block110 block111)))) (checkPow_join pointTest 11 28672 (checkPow_join pointTest 10 28672 (checkPow_join pointTest 9 28672 (checkPow_join pointTest 8 28672 block112 block113) (checkPow_join pointTest 8 29184 block114 block115)) (checkPow_join pointTest 9 29696 (checkPow_join pointTest 8 29696 block116 block117) (checkPow_join pointTest 8 30208 block118 block119))) (checkPow_join pointTest 10 30720 (checkPow_join pointTest 9 30720 (checkPow_join pointTest 8 30720 block120 block121) (checkPow_join pointTest 8 31232 block122 block123)) (checkPow_join pointTest 9 31744 (checkPow_join pointTest 8 31744 block124 block125) (checkPow_join pointTest 8 32256 block126 block127)))))))

theorem equation (x : Fin 31671) :
    KernelUpperData.lookup blocks72 x = KernelUpperData.lookup blocks49 (KernelUpperData.lookup blocks49 (KernelUpperData.lookup blocks67 (KernelUpperData.lookup blocks54 (KernelUpperData.lookup blocks49 (KernelUpperData.lookup blocks49 (x)))))) := by
  have h := checkPow_sound pointTest 15 0 checked x.val (Nat.zero_le _)
    (Nat.lt_trans x.isLt (by decide))
  have hx : Fin.ofNat 31671 x.val = x := by simp
  apply Fin.ext
  simpa only [pointTest, hx, beq_iff_eq] using h

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Core.Check72
