import Theory.SpecificGroups.Tits.R1CosetCover

example : Subgroup.GeneratorCosetCover Tits.parrottR1DihedralSubgroup
    Tits.parrottR1Generator (Fin 1024) := Tits.parrottR1CosetCover

#print axioms Tits.parrottR1CosetCover
#print axioms Tits.R1WordCertificate.relator_exact
#print axioms Tits.R1WordCertificate.relatorIndex_surjective
#print axioms Tits.R1WordCertificate.literal_relators_eq_presentation
#print axioms Tits.R1WordCertificate.relator_ok
#print axioms Tits.R1WordCertificate.allowed_ok
#print axioms Tits.R1WordCertificate.valid
#print axioms Tits.R1WordCertificate.all_hold
#print axioms Tits.R1WordCertificate.hshape
#print axioms Tits.R1WordCertificate.hlt
