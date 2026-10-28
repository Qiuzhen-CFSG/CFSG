module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Data

/-!
# Agreement of the packed tables with the published group words

Both tables are checked on all 100 letters. The packed maps thus compute
exactly the words in `CertificateData`, with the existing inverse-action
convention. The data has no independent mathematical authority.
Source: the retained ATLAS HSG1-p100B0 witnesses and `source/generate.py`.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
set_option maxRecDepth 100000
set_option Elab.async false

theorem normalMap_eq : ∀ i x,
    normalMap i x = (normalWord i : Equiv.Perm (Fin 100)) x := by
  apply OrderCertificate.allFin
  decide +kernel

theorem representativeMap_eq : ∀ i x,
    representativeMap i x = (representative i : Equiv.Perm (Fin 100)) x := by
  apply OrderCertificate.allFin
  decide +kernel

end Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
