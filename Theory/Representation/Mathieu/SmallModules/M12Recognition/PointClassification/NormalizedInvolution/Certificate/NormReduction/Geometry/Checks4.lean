module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Tables

/-!
# Checked norm actions, block 5

The kernel checks the packed predecessor and two-sided seed actions.
Each block covers 1024 indices, with explicit guards on the final block.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry

theorem checked4 :
    allBelow 8 (fun b => allBelow 128 (fun j => entryCheck (4096 + b*128+j))) = true := by
  decide +kernel

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry
