module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.Basic
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.Torus
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.LocalQuotients

/-!
# Matrix parabolic geometry of PSL₃(4) extended by Frobenius

This module exports the concrete standard point and plane stabilizers, their
identification with the root-plane normalizers, and surjective five-point
actions whose exact kernels are the relative root planes. The resulting
equivalences identify the actual local quotients with S₅ and retain the
geometric actions on quotient representatives.

The whole flag overlap has order 384. The odd diagonal torus also supplies
an explicit element of order three outside the Sylow subgroup of order 128.
Thus the overlap strictly contains that Sylow subgroup, as required when
forming the compatible local amalgam.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/
