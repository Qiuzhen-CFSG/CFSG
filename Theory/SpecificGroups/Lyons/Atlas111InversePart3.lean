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
public theorem inverseA_row84 :
    checkRow atlasARows atlasAInvColumns 84 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row84 :
    checkRow atlasBRows atlasBInvColumns 84 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row85 :
    checkRow atlasARows atlasAInvColumns 85 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row85 :
    checkRow atlasBRows atlasBInvColumns 85 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row86 :
    checkRow atlasARows atlasAInvColumns 86 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row86 :
    checkRow atlasBRows atlasBInvColumns 86 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row87 :
    checkRow atlasARows atlasAInvColumns 87 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row87 :
    checkRow atlasBRows atlasBInvColumns 87 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row88 :
    checkRow atlasARows atlasAInvColumns 88 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row88 :
    checkRow atlasBRows atlasBInvColumns 88 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row89 :
    checkRow atlasARows atlasAInvColumns 89 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row89 :
    checkRow atlasBRows atlasBInvColumns 89 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row90 :
    checkRow atlasARows atlasAInvColumns 90 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row90 :
    checkRow atlasBRows atlasBInvColumns 90 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row91 :
    checkRow atlasARows atlasAInvColumns 91 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row91 :
    checkRow atlasBRows atlasBInvColumns 91 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row92 :
    checkRow atlasARows atlasAInvColumns 92 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row92 :
    checkRow atlasBRows atlasBInvColumns 92 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row93 :
    checkRow atlasARows atlasAInvColumns 93 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row93 :
    checkRow atlasBRows atlasBInvColumns 93 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row94 :
    checkRow atlasARows atlasAInvColumns 94 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row94 :
    checkRow atlasBRows atlasBInvColumns 94 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row95 :
    checkRow atlasARows atlasAInvColumns 95 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row95 :
    checkRow atlasBRows atlasBInvColumns 95 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row96 :
    checkRow atlasARows atlasAInvColumns 96 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row96 :
    checkRow atlasBRows atlasBInvColumns 96 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row97 :
    checkRow atlasARows atlasAInvColumns 97 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row97 :
    checkRow atlasBRows atlasBInvColumns 97 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row98 :
    checkRow atlasARows atlasAInvColumns 98 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row98 :
    checkRow atlasBRows atlasBInvColumns 98 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row99 :
    checkRow atlasARows atlasAInvColumns 99 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row99 :
    checkRow atlasBRows atlasBInvColumns 99 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row100 :
    checkRow atlasARows atlasAInvColumns 100 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row100 :
    checkRow atlasBRows atlasBInvColumns 100 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row101 :
    checkRow atlasARows atlasAInvColumns 101 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row101 :
    checkRow atlasBRows atlasBInvColumns 101 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row102 :
    checkRow atlasARows atlasAInvColumns 102 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row102 :
    checkRow atlasBRows atlasBInvColumns 102 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row103 :
    checkRow atlasARows atlasAInvColumns 103 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row103 :
    checkRow atlasBRows atlasBInvColumns 103 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row104 :
    checkRow atlasARows atlasAInvColumns 104 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row104 :
    checkRow atlasBRows atlasBInvColumns 104 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row105 :
    checkRow atlasARows atlasAInvColumns 105 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row105 :
    checkRow atlasBRows atlasBInvColumns 105 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row106 :
    checkRow atlasARows atlasAInvColumns 106 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row106 :
    checkRow atlasBRows atlasBInvColumns 106 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row107 :
    checkRow atlasARows atlasAInvColumns 107 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row107 :
    checkRow atlasBRows atlasBInvColumns 107 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row108 :
    checkRow atlasARows atlasAInvColumns 108 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row108 :
    checkRow atlasBRows atlasBInvColumns 108 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row109 :
    checkRow atlasARows atlasAInvColumns 109 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row109 :
    checkRow atlasBRows atlasBInvColumns 109 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row110 :
    checkRow atlasARows atlasAInvColumns 110 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row110 :
    checkRow atlasBRows atlasBInvColumns 110 = true := by
  decide +kernel

end Lyons.Atlas111Certificate
