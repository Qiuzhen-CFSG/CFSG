module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level3Step03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel3Data

/-!
# Final refinement consequence with 3 fixed points

Generated witnesses for the ATLAS degree-4060 model, GLS3 Table 5.3r, p.279.
See `Rigidity/source/generate.py`; all asserted equations are kernel-checked.
-/

namespace Rudvalis.OuterNormalizer.RigidityCertificate

set_option maxRecDepth 30000
set_option Elab.async false

private theorem level3_decode : ∀ x : Fin 4060,
    r3s3 x = r3s3 3 →
      OrderCertificate.L3Point (OrderCertificate.L3PointInv x) = x := by
  apply Data.allFin
  decide +kernel

public theorem image3_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (hf : ∀ x : Fin 4060, x.val < 3 → p x = x) :
    p 3 ∈ Set.range OrderCertificate.L3Point :=
  ⟨OrderCertificate.L3PointInv (p 3),
    level3_decode (p 3) (r3s3_preserved p hp hf 3)⟩

end Rudvalis.OuterNormalizer.RigidityCertificate
