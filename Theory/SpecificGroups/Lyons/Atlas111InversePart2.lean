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
public theorem inverseA_row56 :
    checkRow atlasARows atlasAInvColumns 56 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row56 :
    checkRow atlasBRows atlasBInvColumns 56 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row57 :
    checkRow atlasARows atlasAInvColumns 57 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row57 :
    checkRow atlasBRows atlasBInvColumns 57 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row58 :
    checkRow atlasARows atlasAInvColumns 58 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row58 :
    checkRow atlasBRows atlasBInvColumns 58 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row59 :
    checkRow atlasARows atlasAInvColumns 59 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row59 :
    checkRow atlasBRows atlasBInvColumns 59 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row60 :
    checkRow atlasARows atlasAInvColumns 60 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row60 :
    checkRow atlasBRows atlasBInvColumns 60 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row61 :
    checkRow atlasARows atlasAInvColumns 61 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row61 :
    checkRow atlasBRows atlasBInvColumns 61 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row62 :
    checkRow atlasARows atlasAInvColumns 62 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row62 :
    checkRow atlasBRows atlasBInvColumns 62 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row63 :
    checkRow atlasARows atlasAInvColumns 63 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row63 :
    checkRow atlasBRows atlasBInvColumns 63 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row64 :
    checkRow atlasARows atlasAInvColumns 64 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row64 :
    checkRow atlasBRows atlasBInvColumns 64 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row65 :
    checkRow atlasARows atlasAInvColumns 65 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row65 :
    checkRow atlasBRows atlasBInvColumns 65 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row66 :
    checkRow atlasARows atlasAInvColumns 66 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row66 :
    checkRow atlasBRows atlasBInvColumns 66 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row67 :
    checkRow atlasARows atlasAInvColumns 67 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row67 :
    checkRow atlasBRows atlasBInvColumns 67 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row68 :
    checkRow atlasARows atlasAInvColumns 68 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row68 :
    checkRow atlasBRows atlasBInvColumns 68 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row69 :
    checkRow atlasARows atlasAInvColumns 69 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row69 :
    checkRow atlasBRows atlasBInvColumns 69 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row70 :
    checkRow atlasARows atlasAInvColumns 70 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row70 :
    checkRow atlasBRows atlasBInvColumns 70 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row71 :
    checkRow atlasARows atlasAInvColumns 71 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row71 :
    checkRow atlasBRows atlasBInvColumns 71 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row72 :
    checkRow atlasARows atlasAInvColumns 72 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row72 :
    checkRow atlasBRows atlasBInvColumns 72 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row73 :
    checkRow atlasARows atlasAInvColumns 73 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row73 :
    checkRow atlasBRows atlasBInvColumns 73 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row74 :
    checkRow atlasARows atlasAInvColumns 74 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row74 :
    checkRow atlasBRows atlasBInvColumns 74 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row75 :
    checkRow atlasARows atlasAInvColumns 75 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row75 :
    checkRow atlasBRows atlasBInvColumns 75 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row76 :
    checkRow atlasARows atlasAInvColumns 76 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row76 :
    checkRow atlasBRows atlasBInvColumns 76 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row77 :
    checkRow atlasARows atlasAInvColumns 77 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row77 :
    checkRow atlasBRows atlasBInvColumns 77 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row78 :
    checkRow atlasARows atlasAInvColumns 78 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row78 :
    checkRow atlasBRows atlasBInvColumns 78 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row79 :
    checkRow atlasARows atlasAInvColumns 79 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row79 :
    checkRow atlasBRows atlasBInvColumns 79 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row80 :
    checkRow atlasARows atlasAInvColumns 80 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row80 :
    checkRow atlasBRows atlasBInvColumns 80 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row81 :
    checkRow atlasARows atlasAInvColumns 81 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row81 :
    checkRow atlasBRows atlasBInvColumns 81 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row82 :
    checkRow atlasARows atlasAInvColumns 82 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row82 :
    checkRow atlasBRows atlasBInvColumns 82 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row83 :
    checkRow atlasARows atlasAInvColumns 83 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row83 :
    checkRow atlasBRows atlasBInvColumns 83 = true := by
  decide +kernel

end Lyons.Atlas111Certificate
