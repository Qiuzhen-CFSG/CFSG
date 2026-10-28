module

public import Theory.SpecificGroups.Lyons.Atlas111Arithmetic

/-!
# Row certificates for the ATLAS Lyons generators

Each Boolean equality checks one row of a product with its proposed inverse.
`Atlas111Arithmetic.row_sound` proves that these checks imply the actual
matrix identities. The source data is documented in `Atlas111Source/README.md`.
The parts partition the rows to bound checking memory and allow separate builds.
-/

namespace Lyons.Atlas111Certificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row0 :
    checkRow atlasARows atlasAInvColumns 0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row0 :
    checkRow atlasBRows atlasBInvColumns 0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row1 :
    checkRow atlasARows atlasAInvColumns 1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row1 :
    checkRow atlasBRows atlasBInvColumns 1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row2 :
    checkRow atlasARows atlasAInvColumns 2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row2 :
    checkRow atlasBRows atlasBInvColumns 2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row3 :
    checkRow atlasARows atlasAInvColumns 3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row3 :
    checkRow atlasBRows atlasBInvColumns 3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row4 :
    checkRow atlasARows atlasAInvColumns 4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row4 :
    checkRow atlasBRows atlasBInvColumns 4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row5 :
    checkRow atlasARows atlasAInvColumns 5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row5 :
    checkRow atlasBRows atlasBInvColumns 5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row6 :
    checkRow atlasARows atlasAInvColumns 6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row6 :
    checkRow atlasBRows atlasBInvColumns 6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row7 :
    checkRow atlasARows atlasAInvColumns 7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row7 :
    checkRow atlasBRows atlasBInvColumns 7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row8 :
    checkRow atlasARows atlasAInvColumns 8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row8 :
    checkRow atlasBRows atlasBInvColumns 8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row9 :
    checkRow atlasARows atlasAInvColumns 9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row9 :
    checkRow atlasBRows atlasBInvColumns 9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row10 :
    checkRow atlasARows atlasAInvColumns 10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row10 :
    checkRow atlasBRows atlasBInvColumns 10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row11 :
    checkRow atlasARows atlasAInvColumns 11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row11 :
    checkRow atlasBRows atlasBInvColumns 11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row12 :
    checkRow atlasARows atlasAInvColumns 12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row12 :
    checkRow atlasBRows atlasBInvColumns 12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row13 :
    checkRow atlasARows atlasAInvColumns 13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row13 :
    checkRow atlasBRows atlasBInvColumns 13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row14 :
    checkRow atlasARows atlasAInvColumns 14 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row14 :
    checkRow atlasBRows atlasBInvColumns 14 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row15 :
    checkRow atlasARows atlasAInvColumns 15 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row15 :
    checkRow atlasBRows atlasBInvColumns 15 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row16 :
    checkRow atlasARows atlasAInvColumns 16 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row16 :
    checkRow atlasBRows atlasBInvColumns 16 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row17 :
    checkRow atlasARows atlasAInvColumns 17 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row17 :
    checkRow atlasBRows atlasBInvColumns 17 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row18 :
    checkRow atlasARows atlasAInvColumns 18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row18 :
    checkRow atlasBRows atlasBInvColumns 18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row19 :
    checkRow atlasARows atlasAInvColumns 19 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row19 :
    checkRow atlasBRows atlasBInvColumns 19 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row20 :
    checkRow atlasARows atlasAInvColumns 20 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row20 :
    checkRow atlasBRows atlasBInvColumns 20 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row21 :
    checkRow atlasARows atlasAInvColumns 21 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row21 :
    checkRow atlasBRows atlasBInvColumns 21 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row22 :
    checkRow atlasARows atlasAInvColumns 22 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row22 :
    checkRow atlasBRows atlasBInvColumns 22 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row23 :
    checkRow atlasARows atlasAInvColumns 23 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row23 :
    checkRow atlasBRows atlasBInvColumns 23 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row24 :
    checkRow atlasARows atlasAInvColumns 24 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row24 :
    checkRow atlasBRows atlasBInvColumns 24 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row25 :
    checkRow atlasARows atlasAInvColumns 25 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row25 :
    checkRow atlasBRows atlasBInvColumns 25 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row26 :
    checkRow atlasARows atlasAInvColumns 26 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row26 :
    checkRow atlasBRows atlasBInvColumns 26 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row27 :
    checkRow atlasARows atlasAInvColumns 27 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row27 :
    checkRow atlasBRows atlasBInvColumns 27 = true := by
  decide +kernel

end Lyons.Atlas111Certificate
