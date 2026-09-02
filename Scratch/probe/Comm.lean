import Stellmacher.SectionsOneToFourDefs
#check commutatorAction
#check commutatorAction₂
#check @commutatorAction₂
#print commutatorAction₂
#print commutatorSubgroup
#check Subgroup.subgroupOf
#check Subgroup.comap
#check Subgroup.map

variable {G V : Type} [Group G] [Group V] [MulDistribMulAction G V]
variable (S W : Subgroup G)
#check commutatorAction (A := W) (G := V)
#check commutatorAction₂ (A := S) (G := commutatorAction (A := W) (G := V))
#check commutatorSubgroup (A := S) (G := V)
#check commutatorSubgroup (A := S) (G := V)
example : Subgroup V :=
  commutatorSubgroup (A := S) (G := V)
    (commutatorSubgroup (A := S) (G := V)
      (commutatorAction (A := W) (G := V)))
