module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.RightInverse.Data

/-!
# Complete numerical right-inverse certificate

Every row of the original B table is multiplied by the original candidate
inverse table. Each declaration checks 32 consecutive rows by kernel reduction.
The block layout and its soundness are proved separately and reused here.
No external computation, native decision procedure, or inverse-power identity
is a premise. See `source/README.md` for source and benchmark information.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.RightInverse

theorem checked00 : checkRows inverseBlocks 0 bBlock00 = true := by
  decide +kernel

theorem checked01 : checkRows inverseBlocks 32 bBlock01 = true := by
  decide +kernel

theorem checked02 : checkRows inverseBlocks 64 bBlock02 = true := by
  decide +kernel

theorem checked03 : checkRows inverseBlocks 96 bBlock03 = true := by
  decide +kernel

theorem checked04 : checkRows inverseBlocks 128 bBlock04 = true := by
  decide +kernel

theorem checked05 : checkRows inverseBlocks 160 bBlock05 = true := by
  decide +kernel

theorem checked06 : checkRows inverseBlocks 192 bBlock06 = true := by
  decide +kernel

theorem checked07 : checkRows inverseBlocks 224 bBlock07 = true := by
  decide +kernel

theorem checked08 : checkRows inverseBlocks 256 bBlock08 = true := by
  decide +kernel

theorem checked09 : checkRows inverseBlocks 288 bBlock09 = true := by
  decide +kernel

theorem checked10 : checkRows inverseBlocks 320 bBlock10 = true := by
  decide +kernel

theorem checked11 : checkRows inverseBlocks 352 bBlock11 = true := by
  decide +kernel

theorem checked12 : checkRows inverseBlocks 384 bBlock12 = true := by
  decide +kernel

theorem checked13 : checkRows inverseBlocks 416 bBlock13 = true := by
  decide +kernel

theorem checked14 : checkRows inverseBlocks 448 bBlock14 = true := by
  decide +kernel

theorem checked15 : checkRows inverseBlocks 480 bBlock15 = true := by
  decide +kernel

theorem checked16 : checkRows inverseBlocks 512 bBlock16 = true := by
  decide +kernel

theorem checked17 : checkRows inverseBlocks 544 bBlock17 = true := by
  decide +kernel

theorem checked18 : checkRows inverseBlocks 576 bBlock18 = true := by
  decide +kernel

theorem checked19 : checkRows inverseBlocks 608 bBlock19 = true := by
  decide +kernel

theorem checked20 : checkRows inverseBlocks 640 bBlock20 = true := by
  decide +kernel

theorem checked21 : checkRows inverseBlocks 672 bBlock21 = true := by
  decide +kernel

theorem checked22 : checkRows inverseBlocks 704 bBlock22 = true := by
  decide +kernel

theorem checked23 : checkRows inverseBlocks 736 bBlock23 = true := by
  decide +kernel

theorem checked24 : checkRows inverseBlocks 768 bBlock24 = true := by
  decide +kernel

theorem checked25 : checkRows inverseBlocks 800 bBlock25 = true := by
  decide +kernel

theorem checked26 : checkRows inverseBlocks 832 bBlock26 = true := by
  decide +kernel

theorem checked27 : checkRows inverseBlocks 864 bBlock27 = true := by
  decide +kernel

theorem checked28 : checkRows inverseBlocks 896 bBlock28 = true := by
  decide +kernel

theorem checked29 : checkRows inverseBlocks 928 bBlock29 = true := by
  decide +kernel

theorem checked30 : checkRows inverseBlocks 960 bBlock30 = true := by
  decide +kernel

theorem checked31 : checkRows inverseBlocks 992 bBlock31 = true := by
  decide +kernel

theorem checked32 : checkRows inverseBlocks 1024 bBlock32 = true := by
  decide +kernel

theorem checked33 : checkRows inverseBlocks 1056 bBlock33 = true := by
  decide +kernel

theorem checked34 : checkRows inverseBlocks 1088 bBlock34 = true := by
  decide +kernel

theorem checked35 : checkRows inverseBlocks 1120 bBlock35 = true := by
  decide +kernel

theorem checked36 : checkRows inverseBlocks 1152 bBlock36 = true := by
  decide +kernel

theorem checked37 : checkRows inverseBlocks 1184 bBlock37 = true := by
  decide +kernel

theorem checked38 : checkRows inverseBlocks 1216 bBlock38 = true := by
  decide +kernel

theorem checked39 : checkRows inverseBlocks 1248 bBlock39 = true := by
  decide +kernel

theorem checked40 : checkRows inverseBlocks 1280 bBlock40 = true := by
  decide +kernel

theorem checked41 : checkRows inverseBlocks 1312 bBlock41 = true := by
  decide +kernel

theorem checked42 : checkRows inverseBlocks 1344 bBlock42 = true := by
  decide +kernel

theorem checked43 : checkRows inverseBlocks 1376 bBlock43 = true := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.RightInverse
