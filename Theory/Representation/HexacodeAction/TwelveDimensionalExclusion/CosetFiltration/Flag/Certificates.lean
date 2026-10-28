module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Flag.Arithmetic

/-!
# Bounded kernel certificates for the published matrix witnesses

Each basis column is encoded by two bit vectors, for its coefficients of 1
and omega. The checks establish that these are the published columns, that
multiplication by the saved inverse gives the standard basis, and that both
saved adapted actions agree with the original monomial generators. The
remaining zero-entry checks establish every specified invariant cut.

The multiplication certificates check five columns at a time. Their kernel
checks run sequentially within this module to bound temporary reduction
memory; this does not change Lean's default thread count.

Source: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464. The fixed witnesses
and ATLAS attribution are recorded in `../source/README.md`. Every assertion
here is checked by Lean's kernel, without an external computation oracle.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag

def packedColumns : Fin 45 → Packed :=
  ![(17616420793569, 23882948813876),
    (29555751101586, 5569322635044),
    (31707695505080, 25980706106672),
    (26176357662721, 12563060359172),
    (17516684967938, 3491998334980),
    (27667208863752, 11318361849888),
    (19043089121296, 28731785084960),
    (4090554810432, 3563935367424),
    (34817946747008, 29986621358336),
    (19366197461504, 26686252582912),
    (8839585858560, 17604668295168),
    (5862960795648, 34813400268800),
    (13376579174401, 25198568949760),
    (20841792276488, 4432564731904),
    (7797396865088, 30988289851392),
    (15233326252034, 25542912919552),
    (7677144991752, 13217318453248),
    (4350780901392, 34905787613184),
    (19091138019329, 1152401819648),
    (889670598658, 22825175894016),
    (21613114312708, 19797458812928),
    (4039416741889, 2534030704640),
    (2353642078210, 20478404067328),
    (22568442527748, 13247826624512),
    (9404367765512, 22099754221568),
    (4566087106592, 6715181367296),
    (8435852640320, 31784905474048),
    (18210661335552, 18167711662080),
    (9328668971008, 10642928959488),
    (28746753015808, 30138322386944),
    (27661736869889, 7971459301376),
    (7438883356676, 17285095882752),
    (29927332118536, 12354473426944),
    (2473901162497, 2199023255552),
    (2473901162498, 2199023255552),
    (274877906948, 2473901162496),
    (2199023255560, 17867063951360),
    (2199023255568, 17867063951360),
    (20066087206944, 2199023255552),
    (274877907008, 17592186044416),
    (274877907072, 17592186044416),
    (17867063951616, 274877906944),
    (1, 0),
    (8, 0),
    (64, 0)]


private def chunkIndex (b : Fin 9) (y : Fin 5) : Fin 45 :=
  ⟨5 * b.val + y.val, by omega⟩

private theorem forall_chunks (P : Fin 45 → Prop)
    (h : ∀ b y, P (chunkIndex b y)) : ∀ y, P y := by
  intro y
  let b : Fin 9 := ⟨y.val / 5, by omega⟩
  let z : Fin 5 := ⟨y.val % 5, by omega⟩
  have hz : chunkIndex b z = y := by apply Fin.ext; dsimp [chunkIndex, b, z]; omega
  simpa only [hz] using h b z

set_option Elab.async false in
private theorem columns_0 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 0 y)) i.val = basisRows (chunkIndex 0 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_1 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 1 y)) i.val = basisRows (chunkIndex 1 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_2 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 2 y)) i.val = basisRows (chunkIndex 2 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_3 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 3 y)) i.val = basisRows (chunkIndex 3 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_4 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 4 y)) i.val = basisRows (chunkIndex 4 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_5 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 5 y)) i.val = basisRows (chunkIndex 5 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_6 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 6 y)) i.val = basisRows (chunkIndex 6 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_7 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 7 y)) i.val = basisRows (chunkIndex 7 y) i := by
  decide +kernel

set_option Elab.async false in
private theorem columns_8 : ∀ (i : Fin 45) (y : Fin 5),
    code (packedColumns (chunkIndex 8 y)) i.val = basisRows (chunkIndex 8 y) i := by
  decide +kernel

theorem packed_columns_spec : ∀ i j : Fin 45,
    code (packedColumns j) i.val = basisRows j i := by
  intro i
  apply forall_chunks
  intro b
  fin_cases b
  · exact columns_0 i
  · exact columns_1 i
  · exact columns_2 i
  · exact columns_3 i
  · exact columns_4 i
  · exact columns_5 i
  · exact columns_6 i
  · exact columns_7 i
  · exact columns_8 i

set_option Elab.async false in
private theorem inverse_0 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 0 y)) =
      (2 ^ (chunkIndex 0 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_1 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 1 y)) =
      (2 ^ (chunkIndex 1 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_2 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 2 y)) =
      (2 ^ (chunkIndex 2 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_3 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 3 y)) =
      (2 ^ (chunkIndex 3 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_4 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 4 y)) =
      (2 ^ (chunkIndex 4 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_5 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 5 y)) =
      (2 ^ (chunkIndex 5 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_6 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 6 y)) =
      (2 ^ (chunkIndex 6 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_7 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 7 y)) =
      (2 ^ (chunkIndex 7 y).val, 0) := by
  decide +kernel

set_option Elab.async false in
private theorem inverse_8 : ∀ y : Fin 5,
    combine packedColumns (fun z => inverseRows z (chunkIndex 8 y)) =
      (2 ^ (chunkIndex 8 y).val, 0) := by
  decide +kernel

theorem packed_inverse : ∀ y : Fin 45,
    combine packedColumns (fun z => inverseRows z y) = (2 ^ y.val, 0) := by
  apply forall_chunks
  intro b
  fin_cases b
  · exact inverse_0
  · exact inverse_1
  · exact inverse_2
  · exact inverse_3
  · exact inverse_4
  · exact inverse_5
  · exact inverse_6
  · exact inverse_7
  · exact inverse_8

set_option Elab.async false in
private theorem action_0_0 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 0 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 0 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_1 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 1 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 1 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_2 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 2 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 2 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_3 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 3 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 3 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_4 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 4 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 4 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_5 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 5 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 5 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_6 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 6 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 6 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_7 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 7 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 7 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_0_8 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 0 z (chunkIndex 8 y)) =
      pack (fun x => codeMul (coefficientCode 0 x)
        (basisRows (chunkIndex 8 y) (rowSource 0 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_0 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 0 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 0 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_1 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 1 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 1 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_2 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 2 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 2 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_3 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 3 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 3 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_4 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 4 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 4 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_5 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 5 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 5 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_6 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 6 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 6 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_7 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 7 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 7 y) (rowSource 1 x))) := by
  decide +kernel

set_option Elab.async false in
private theorem action_1_8 : ∀ y : Fin 5,
    combine packedColumns (fun z => adaptedRows 1 z (chunkIndex 8 y)) =
      pack (fun x => codeMul (coefficientCode 1 x)
        (basisRows (chunkIndex 8 y) (rowSource 1 x))) := by
  decide +kernel

theorem packed_action : ∀ (j : Fin 2) (y : Fin 45),
    combine packedColumns (fun z => adaptedRows j z y) =
      pack (fun x => codeMul (coefficientCode j x) (basisRows y (rowSource j x))) := by
  intro j
  apply forall_chunks
  intro b
  fin_cases j <;> fin_cases b
  · exact action_0_0
  · exact action_0_1
  · exact action_0_2
  · exact action_0_3
  · exact action_0_4
  · exact action_0_5
  · exact action_0_6
  · exact action_0_7
  · exact action_0_8
  · exact action_1_0
  · exact action_1_1
  · exact action_1_2
  · exact action_1_3
  · exact action_1_4
  · exact action_1_5
  · exact action_1_6
  · exact action_1_7
  · exact action_1_8

set_option Elab.async false in
private theorem lower_0 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 0 ≤ x.val → y.val < cut 0 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_1 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 1 ≤ x.val → y.val < cut 1 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_2 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 2 ≤ x.val → y.val < cut 2 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_3 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 3 ≤ x.val → y.val < cut 3 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_4 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 4 ≤ x.val → y.val < cut 4 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_5 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 5 ≤ x.val → y.val < cut 5 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_6 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 6 ≤ x.val → y.val < cut 6 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_7 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 7 ≤ x.val → y.val < cut 7 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_8 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 8 ≤ x.val → y.val < cut 8 → adaptedRows j x y = 0 := by
  decide +kernel

set_option Elab.async false in
private theorem lower_9 : ∀ (j : Fin 2) (x y : Fin 45),
    cut 9 ≤ x.val → y.val < cut 9 → adaptedRows j x y = 0 := by
  decide +kernel

theorem lower_blocks_zero : ∀ (m : Fin 10) (j : Fin 2) (x y : Fin 45),
    cut m.val ≤ x.val → y.val < cut m.val → adaptedRows j x y = 0 := by
  intro m
  fin_cases m
  · exact lower_0
  · exact lower_1
  · exact lower_2
  · exact lower_3
  · exact lower_4
  · exact lower_5
  · exact lower_6
  · exact lower_7
  · exact lower_8
  · exact lower_9

end Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag
