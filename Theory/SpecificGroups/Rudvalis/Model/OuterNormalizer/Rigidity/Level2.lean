module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level2Step01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Data

/-!
# Final refinement consequence with 2 fixed points

Generated witnesses for the ATLAS degree-4060 model, GLS3 Table 5.3r, p.279.
See `Rigidity/source/generate.py`; all asserted equations are kernel-checked.
-/

namespace Rudvalis.OuterNormalizer.RigidityCertificate

set_option maxRecDepth 30000
set_option Elab.async false

private theorem level2_decode : ∀ x : Fin 4060,
    r2s1 x = r2s1 2 →
      OrderCertificate.L2Point (OrderCertificate.L2PointInv x) = x := by
  apply Data.allFin
  decide +kernel

public theorem image2_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (hf : ∀ x : Fin 4060, x.val < 2 → p x = x) :
    p 2 ∈ Set.range OrderCertificate.L2Point :=
  ⟨OrderCertificate.L2PointInv (p 2),
    level2_decode (p 2) (r2s1_preserved p hp hf 2)⟩

end Rudvalis.OuterNormalizer.RigidityCertificate
