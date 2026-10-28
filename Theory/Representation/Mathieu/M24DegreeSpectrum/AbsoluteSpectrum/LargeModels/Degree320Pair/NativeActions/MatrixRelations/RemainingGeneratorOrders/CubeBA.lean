module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.Blocks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.OrderData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Masks

/-!
# Packed product CubeBA for the degree-320 ATLAS generators

Each eight-row block uses the existing sparse gap checker and the checked
320a generator masks. Explicit block transports assemble the literal product
Ba * (Ba * Ba). Every finite check is reduced by the kernel.
Source: the unchanged ATLAS matrices and John Bray, M24G1-P1.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate

-- Keep the bounded reductions sequential within this certificate.
set_option Elab.async false

set_option maxRecDepth 2000 in
private theorem block00 :
    Checked ((Data.BaRows).drop 0 |>.take 8) (squareBaRows) ((identityRows).drop 0 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 0 |>.take 8) (squareBaRows) ((identityRows).drop 0 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 0 |>.take 8) (squareBaRows) ((identityRows).drop 0 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba00 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block01 :
    Checked ((Data.BaRows).drop 8 |>.take 8) (squareBaRows) ((identityRows).drop 8 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 8 |>.take 8) (squareBaRows) ((identityRows).drop 8 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 8 |>.take 8) (squareBaRows) ((identityRows).drop 8 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba01 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block02 :
    Checked ((Data.BaRows).drop 16 |>.take 8) (squareBaRows) ((identityRows).drop 16 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 16 |>.take 8) (squareBaRows) ((identityRows).drop 16 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 16 |>.take 8) (squareBaRows) ((identityRows).drop 16 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba02 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block03 :
    Checked ((Data.BaRows).drop 24 |>.take 8) (squareBaRows) ((identityRows).drop 24 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 24 |>.take 8) (squareBaRows) ((identityRows).drop 24 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 24 |>.take 8) (squareBaRows) ((identityRows).drop 24 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba03 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block04 :
    Checked ((Data.BaRows).drop 32 |>.take 8) (squareBaRows) ((identityRows).drop 32 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 32 |>.take 8) (squareBaRows) ((identityRows).drop 32 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 32 |>.take 8) (squareBaRows) ((identityRows).drop 32 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba04 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block05 :
    Checked ((Data.BaRows).drop 40 |>.take 8) (squareBaRows) ((identityRows).drop 40 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 40 |>.take 8) (squareBaRows) ((identityRows).drop 40 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 40 |>.take 8) (squareBaRows) ((identityRows).drop 40 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba05 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block06 :
    Checked ((Data.BaRows).drop 48 |>.take 8) (squareBaRows) ((identityRows).drop 48 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 48 |>.take 8) (squareBaRows) ((identityRows).drop 48 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 48 |>.take 8) (squareBaRows) ((identityRows).drop 48 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba06 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block07 :
    Checked ((Data.BaRows).drop 56 |>.take 8) (squareBaRows) ((identityRows).drop 56 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 56 |>.take 8) (squareBaRows) ((identityRows).drop 56 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 56 |>.take 8) (squareBaRows) ((identityRows).drop 56 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba07 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block08 :
    Checked ((Data.BaRows).drop 64 |>.take 8) (squareBaRows) ((identityRows).drop 64 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 64 |>.take 8) (squareBaRows) ((identityRows).drop 64 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 64 |>.take 8) (squareBaRows) ((identityRows).drop 64 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba08 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block09 :
    Checked ((Data.BaRows).drop 72 |>.take 8) (squareBaRows) ((identityRows).drop 72 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 72 |>.take 8) (squareBaRows) ((identityRows).drop 72 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 72 |>.take 8) (squareBaRows) ((identityRows).drop 72 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba09 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block10 :
    Checked ((Data.BaRows).drop 80 |>.take 8) (squareBaRows) ((identityRows).drop 80 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 80 |>.take 8) (squareBaRows) ((identityRows).drop 80 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 80 |>.take 8) (squareBaRows) ((identityRows).drop 80 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba10 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block11 :
    Checked ((Data.BaRows).drop 88 |>.take 8) (squareBaRows) ((identityRows).drop 88 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 88 |>.take 8) (squareBaRows) ((identityRows).drop 88 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 88 |>.take 8) (squareBaRows) ((identityRows).drop 88 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba11 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block12 :
    Checked ((Data.BaRows).drop 96 |>.take 8) (squareBaRows) ((identityRows).drop 96 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 96 |>.take 8) (squareBaRows) ((identityRows).drop 96 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 96 |>.take 8) (squareBaRows) ((identityRows).drop 96 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba12 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block13 :
    Checked ((Data.BaRows).drop 104 |>.take 8) (squareBaRows) ((identityRows).drop 104 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 104 |>.take 8) (squareBaRows) ((identityRows).drop 104 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 104 |>.take 8) (squareBaRows) ((identityRows).drop 104 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba13 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block14 :
    Checked ((Data.BaRows).drop 112 |>.take 8) (squareBaRows) ((identityRows).drop 112 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 112 |>.take 8) (squareBaRows) ((identityRows).drop 112 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 112 |>.take 8) (squareBaRows) ((identityRows).drop 112 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba14 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block15 :
    Checked ((Data.BaRows).drop 120 |>.take 8) (squareBaRows) ((identityRows).drop 120 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 120 |>.take 8) (squareBaRows) ((identityRows).drop 120 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 120 |>.take 8) (squareBaRows) ((identityRows).drop 120 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba15 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block16 :
    Checked ((Data.BaRows).drop 128 |>.take 8) (squareBaRows) ((identityRows).drop 128 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 128 |>.take 8) (squareBaRows) ((identityRows).drop 128 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 128 |>.take 8) (squareBaRows) ((identityRows).drop 128 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba16 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block17 :
    Checked ((Data.BaRows).drop 136 |>.take 8) (squareBaRows) ((identityRows).drop 136 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 136 |>.take 8) (squareBaRows) ((identityRows).drop 136 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 136 |>.take 8) (squareBaRows) ((identityRows).drop 136 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba17 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block18 :
    Checked ((Data.BaRows).drop 144 |>.take 8) (squareBaRows) ((identityRows).drop 144 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 144 |>.take 8) (squareBaRows) ((identityRows).drop 144 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 144 |>.take 8) (squareBaRows) ((identityRows).drop 144 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba18 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block19 :
    Checked ((Data.BaRows).drop 152 |>.take 8) (squareBaRows) ((identityRows).drop 152 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 152 |>.take 8) (squareBaRows) ((identityRows).drop 152 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 152 |>.take 8) (squareBaRows) ((identityRows).drop 152 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba19 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block20 :
    Checked ((Data.BaRows).drop 160 |>.take 8) (squareBaRows) ((identityRows).drop 160 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 160 |>.take 8) (squareBaRows) ((identityRows).drop 160 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 160 |>.take 8) (squareBaRows) ((identityRows).drop 160 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba20 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block21 :
    Checked ((Data.BaRows).drop 168 |>.take 8) (squareBaRows) ((identityRows).drop 168 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 168 |>.take 8) (squareBaRows) ((identityRows).drop 168 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 168 |>.take 8) (squareBaRows) ((identityRows).drop 168 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba21 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block22 :
    Checked ((Data.BaRows).drop 176 |>.take 8) (squareBaRows) ((identityRows).drop 176 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 176 |>.take 8) (squareBaRows) ((identityRows).drop 176 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 176 |>.take 8) (squareBaRows) ((identityRows).drop 176 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba22 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block23 :
    Checked ((Data.BaRows).drop 184 |>.take 8) (squareBaRows) ((identityRows).drop 184 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 184 |>.take 8) (squareBaRows) ((identityRows).drop 184 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 184 |>.take 8) (squareBaRows) ((identityRows).drop 184 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba23 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block24 :
    Checked ((Data.BaRows).drop 192 |>.take 8) (squareBaRows) ((identityRows).drop 192 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 192 |>.take 8) (squareBaRows) ((identityRows).drop 192 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 192 |>.take 8) (squareBaRows) ((identityRows).drop 192 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba24 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block25 :
    Checked ((Data.BaRows).drop 200 |>.take 8) (squareBaRows) ((identityRows).drop 200 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 200 |>.take 8) (squareBaRows) ((identityRows).drop 200 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 200 |>.take 8) (squareBaRows) ((identityRows).drop 200 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba25 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block26 :
    Checked ((Data.BaRows).drop 208 |>.take 8) (squareBaRows) ((identityRows).drop 208 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 208 |>.take 8) (squareBaRows) ((identityRows).drop 208 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 208 |>.take 8) (squareBaRows) ((identityRows).drop 208 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba26 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block27 :
    Checked ((Data.BaRows).drop 216 |>.take 8) (squareBaRows) ((identityRows).drop 216 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 216 |>.take 8) (squareBaRows) ((identityRows).drop 216 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 216 |>.take 8) (squareBaRows) ((identityRows).drop 216 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba27 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block28 :
    Checked ((Data.BaRows).drop 224 |>.take 8) (squareBaRows) ((identityRows).drop 224 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 224 |>.take 8) (squareBaRows) ((identityRows).drop 224 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 224 |>.take 8) (squareBaRows) ((identityRows).drop 224 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba28 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block29 :
    Checked ((Data.BaRows).drop 232 |>.take 8) (squareBaRows) ((identityRows).drop 232 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 232 |>.take 8) (squareBaRows) ((identityRows).drop 232 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 232 |>.take 8) (squareBaRows) ((identityRows).drop 232 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba29 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block30 :
    Checked ((Data.BaRows).drop 240 |>.take 8) (squareBaRows) ((identityRows).drop 240 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 240 |>.take 8) (squareBaRows) ((identityRows).drop 240 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 240 |>.take 8) (squareBaRows) ((identityRows).drop 240 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba30 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block31 :
    Checked ((Data.BaRows).drop 248 |>.take 8) (squareBaRows) ((identityRows).drop 248 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 248 |>.take 8) (squareBaRows) ((identityRows).drop 248 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 248 |>.take 8) (squareBaRows) ((identityRows).drop 248 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba31 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block32 :
    Checked ((Data.BaRows).drop 256 |>.take 8) (squareBaRows) ((identityRows).drop 256 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 256 |>.take 8) (squareBaRows) ((identityRows).drop 256 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 256 |>.take 8) (squareBaRows) ((identityRows).drop 256 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba32 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block33 :
    Checked ((Data.BaRows).drop 264 |>.take 8) (squareBaRows) ((identityRows).drop 264 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 264 |>.take 8) (squareBaRows) ((identityRows).drop 264 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 264 |>.take 8) (squareBaRows) ((identityRows).drop 264 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba33 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block34 :
    Checked ((Data.BaRows).drop 272 |>.take 8) (squareBaRows) ((identityRows).drop 272 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 272 |>.take 8) (squareBaRows) ((identityRows).drop 272 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 272 |>.take 8) (squareBaRows) ((identityRows).drop 272 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba34 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block35 :
    Checked ((Data.BaRows).drop 280 |>.take 8) (squareBaRows) ((identityRows).drop 280 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 280 |>.take 8) (squareBaRows) ((identityRows).drop 280 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 280 |>.take 8) (squareBaRows) ((identityRows).drop 280 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba35 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block36 :
    Checked ((Data.BaRows).drop 288 |>.take 8) (squareBaRows) ((identityRows).drop 288 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 288 |>.take 8) (squareBaRows) ((identityRows).drop 288 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 288 |>.take 8) (squareBaRows) ((identityRows).drop 288 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba36 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block37 :
    Checked ((Data.BaRows).drop 296 |>.take 8) (squareBaRows) ((identityRows).drop 296 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 296 |>.take 8) (squareBaRows) ((identityRows).drop 296 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 296 |>.take 8) (squareBaRows) ((identityRows).drop 296 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba37 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block38 :
    Checked ((Data.BaRows).drop 304 |>.take 8) (squareBaRows) ((identityRows).drop 304 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 304 |>.take 8) (squareBaRows) ((identityRows).drop 304 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 304 |>.take 8) (squareBaRows) ((identityRows).drop 304 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba38 (by decide +kernel))⟩

set_option maxRecDepth 2000 in
private theorem block39 :
    Checked ((Data.BaRows).drop 312 |>.take 8) (squareBaRows) ((identityRows).drop 312 |>.take 8) :=
  ⟨MatrixCertificates.checkRows_of_skip ((Data.BaRows).drop 312 |>.take 8) (squareBaRows) ((identityRows).drop 312 |>.take 8)
    (MatrixCertificates.TraceRows.checkGaps_sound ((Data.BaRows).drop 312 |>.take 8) (squareBaRows) ((identityRows).drop 312 |>.take 8)
      MatrixCertificates.TraceRows.Masks.Ba39 (by decide +kernel))⟩

private theorem ending : Checked ((Data.BaRows).drop (8*40)) (squareBaRows)
    ((identityRows).drop (8*40)) := ⟨by decide +kernel⟩

theorem CubeBA_checked : checkRows (Data.BaRows) (squareBaRows) (identityRows) = true :=
  (start (Data.BaRows) (squareBaRows) (identityRows) (
    step 0 (Data.BaRows) (squareBaRows) (identityRows) block00 (
    step 1 (Data.BaRows) (squareBaRows) (identityRows) block01 (
    step 2 (Data.BaRows) (squareBaRows) (identityRows) block02 (
    step 3 (Data.BaRows) (squareBaRows) (identityRows) block03 (
    step 4 (Data.BaRows) (squareBaRows) (identityRows) block04 (
    step 5 (Data.BaRows) (squareBaRows) (identityRows) block05 (
    step 6 (Data.BaRows) (squareBaRows) (identityRows) block06 (
    step 7 (Data.BaRows) (squareBaRows) (identityRows) block07 (
    step 8 (Data.BaRows) (squareBaRows) (identityRows) block08 (
    step 9 (Data.BaRows) (squareBaRows) (identityRows) block09 (
    step 10 (Data.BaRows) (squareBaRows) (identityRows) block10 (
    step 11 (Data.BaRows) (squareBaRows) (identityRows) block11 (
    step 12 (Data.BaRows) (squareBaRows) (identityRows) block12 (
    step 13 (Data.BaRows) (squareBaRows) (identityRows) block13 (
    step 14 (Data.BaRows) (squareBaRows) (identityRows) block14 (
    step 15 (Data.BaRows) (squareBaRows) (identityRows) block15 (
    step 16 (Data.BaRows) (squareBaRows) (identityRows) block16 (
    step 17 (Data.BaRows) (squareBaRows) (identityRows) block17 (
    step 18 (Data.BaRows) (squareBaRows) (identityRows) block18 (
    step 19 (Data.BaRows) (squareBaRows) (identityRows) block19 (
    step 20 (Data.BaRows) (squareBaRows) (identityRows) block20 (
    step 21 (Data.BaRows) (squareBaRows) (identityRows) block21 (
    step 22 (Data.BaRows) (squareBaRows) (identityRows) block22 (
    step 23 (Data.BaRows) (squareBaRows) (identityRows) block23 (
    step 24 (Data.BaRows) (squareBaRows) (identityRows) block24 (
    step 25 (Data.BaRows) (squareBaRows) (identityRows) block25 (
    step 26 (Data.BaRows) (squareBaRows) (identityRows) block26 (
    step 27 (Data.BaRows) (squareBaRows) (identityRows) block27 (
    step 28 (Data.BaRows) (squareBaRows) (identityRows) block28 (
    step 29 (Data.BaRows) (squareBaRows) (identityRows) block29 (
    step 30 (Data.BaRows) (squareBaRows) (identityRows) block30 (
    step 31 (Data.BaRows) (squareBaRows) (identityRows) block31 (
    step 32 (Data.BaRows) (squareBaRows) (identityRows) block32 (
    step 33 (Data.BaRows) (squareBaRows) (identityRows) block33 (
    step 34 (Data.BaRows) (squareBaRows) (identityRows) block34 (
    step 35 (Data.BaRows) (squareBaRows) (identityRows) block35 (
    step 36 (Data.BaRows) (squareBaRows) (identityRows) block36 (
    step 37 (Data.BaRows) (squareBaRows) (identityRows) block37 (
    step 38 (Data.BaRows) (squareBaRows) (identityRows) block38 (
    step 39 (Data.BaRows) (squareBaRows) (identityRows) block39 (
      ending)))))))))))))))))))))))))))))))))))))))))).eq_true

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
