module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.MatrixWords

/-!
# Concrete data for the Baby Monster order lower bound

The fixed binary ATLAS matrices and the eleven words of Breuer–Magaard–Wilson
(2019), Table 1, are exported here for independent relation and image-size
certification. See https://arxiv.org/abs/1902.07758, §§3.2–3.4.

`OrderLowerBound.card_ge_of_matrix_certificates` transfers those certificates
to the fixed presented carrier. The unconditional matrix certificates, and
hence the lower-bound theorem itself, are not yet established in this module.
-/
