module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level4Step08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel4Data

/-!
# Final refinement consequence with 4 fixed points

Generated witnesses for the ATLAS degree-4060 model, GLS3 Table 5.3r, p.279.
See `Rigidity/source/generate.py`; all asserted equations are kernel-checked.
-/

namespace Rudvalis.OuterNormalizer.RigidityCertificate

set_option maxRecDepth 30000
set_option Elab.async false

private theorem level4_decode : ∀ x : Fin 4060,
    r4s8 x = r4s8 4 →
      OrderCertificate.L4Point (OrderCertificate.L4PointInv x) = x := by
  apply Data.allFin
  decide +kernel

public theorem image4_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (hf : ∀ x : Fin 4060, x.val < 4 → p x = x) :
    p 4 ∈ Set.range OrderCertificate.L4Point :=
  ⟨OrderCertificate.L4PointInv (p 4),
    level4_decode (p 4) (r4s8_preserved p hp hf 4)⟩

end Rudvalis.OuterNormalizer.RigidityCertificate
