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
public theorem inverseA_row28 :
    checkRow atlasARows atlasAInvColumns 28 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row28 :
    checkRow atlasBRows atlasBInvColumns 28 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row29 :
    checkRow atlasARows atlasAInvColumns 29 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row29 :
    checkRow atlasBRows atlasBInvColumns 29 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row30 :
    checkRow atlasARows atlasAInvColumns 30 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row30 :
    checkRow atlasBRows atlasBInvColumns 30 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row31 :
    checkRow atlasARows atlasAInvColumns 31 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row31 :
    checkRow atlasBRows atlasBInvColumns 31 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row32 :
    checkRow atlasARows atlasAInvColumns 32 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row32 :
    checkRow atlasBRows atlasBInvColumns 32 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row33 :
    checkRow atlasARows atlasAInvColumns 33 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row33 :
    checkRow atlasBRows atlasBInvColumns 33 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row34 :
    checkRow atlasARows atlasAInvColumns 34 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row34 :
    checkRow atlasBRows atlasBInvColumns 34 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row35 :
    checkRow atlasARows atlasAInvColumns 35 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row35 :
    checkRow atlasBRows atlasBInvColumns 35 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row36 :
    checkRow atlasARows atlasAInvColumns 36 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row36 :
    checkRow atlasBRows atlasBInvColumns 36 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row37 :
    checkRow atlasARows atlasAInvColumns 37 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row37 :
    checkRow atlasBRows atlasBInvColumns 37 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row38 :
    checkRow atlasARows atlasAInvColumns 38 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row38 :
    checkRow atlasBRows atlasBInvColumns 38 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row39 :
    checkRow atlasARows atlasAInvColumns 39 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row39 :
    checkRow atlasBRows atlasBInvColumns 39 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row40 :
    checkRow atlasARows atlasAInvColumns 40 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row40 :
    checkRow atlasBRows atlasBInvColumns 40 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row41 :
    checkRow atlasARows atlasAInvColumns 41 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row41 :
    checkRow atlasBRows atlasBInvColumns 41 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row42 :
    checkRow atlasARows atlasAInvColumns 42 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row42 :
    checkRow atlasBRows atlasBInvColumns 42 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row43 :
    checkRow atlasARows atlasAInvColumns 43 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row43 :
    checkRow atlasBRows atlasBInvColumns 43 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row44 :
    checkRow atlasARows atlasAInvColumns 44 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row44 :
    checkRow atlasBRows atlasBInvColumns 44 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row45 :
    checkRow atlasARows atlasAInvColumns 45 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row45 :
    checkRow atlasBRows atlasBInvColumns 45 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row46 :
    checkRow atlasARows atlasAInvColumns 46 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row46 :
    checkRow atlasBRows atlasBInvColumns 46 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row47 :
    checkRow atlasARows atlasAInvColumns 47 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row47 :
    checkRow atlasBRows atlasBInvColumns 47 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row48 :
    checkRow atlasARows atlasAInvColumns 48 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row48 :
    checkRow atlasBRows atlasBInvColumns 48 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row49 :
    checkRow atlasARows atlasAInvColumns 49 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row49 :
    checkRow atlasBRows atlasBInvColumns 49 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row50 :
    checkRow atlasARows atlasAInvColumns 50 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row50 :
    checkRow atlasBRows atlasBInvColumns 50 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row51 :
    checkRow atlasARows atlasAInvColumns 51 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row51 :
    checkRow atlasBRows atlasBInvColumns 51 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row52 :
    checkRow atlasARows atlasAInvColumns 52 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row52 :
    checkRow atlasBRows atlasBInvColumns 52 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row53 :
    checkRow atlasARows atlasAInvColumns 53 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row53 :
    checkRow atlasBRows atlasBInvColumns 53 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row54 :
    checkRow atlasARows atlasAInvColumns 54 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row54 :
    checkRow atlasBRows atlasBInvColumns 54 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseA_row55 :
    checkRow atlasARows atlasAInvColumns 55 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem inverseB_row55 :
    checkRow atlasBRows atlasBInvColumns 55 = true := by
  decide +kernel

end Lyons.Atlas111Certificate
