module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsA
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerWordsB
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationC
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationD
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationE
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationF
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationG
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationH
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationI
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationJ
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationK
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalLowerSeparationL

/-!
# Maximal subgroups of the lower 300 even descent nodes

For each original node numbered below 300, a smaller generating family is
certified by words in both directions. Every nonzero binary signature then
has a kernel-checked Schreier certificate: its closure lies in the core-character
kernel, has an explicit outside centralizer element, or equals an original
edge. Projected finite orbits certify nonmembership in the noncentric cases.
Maximal subgroups have relative index two, so their actual membership signatures
occur among these checks. All original node and edge numbers are preserved.

Source: Shinoda (1975), (2.3), pp. 81–82; the diagnostic input provenance is
recorded in `SmallEvenDescentEdgeData`. Diagnostics only select word and orbit
witnesses; the theorem depends solely on the checked Lean certificates.
-/

namespace ReeTwo.SylowModel
open SmallEvenMaximalBranches

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem classify_lower_fin (i : Fin 300) (H : Subgroup SylowModel)
    (hH : H ⋖ smallEvenDescentNode (i.castLE (by decide))) : Classified H := by
  fin_cases i
  · exact SmallEvenMaximalLower.Node0.classify H hH
  · exact SmallEvenMaximalLower.Node1.classify H hH
  · exact SmallEvenMaximalLower.Node2.classify H hH
  · exact SmallEvenMaximalLower.Node3.classify H hH
  · exact SmallEvenMaximalLower.Node4.classify H hH
  · exact SmallEvenMaximalLower.Node5.classify H hH
  · exact SmallEvenMaximalLower.Node6.classify H hH
  · exact SmallEvenMaximalLower.Node7.classify H hH
  · exact SmallEvenMaximalLower.Node8.classify H hH
  · exact SmallEvenMaximalLower.Node9.classify H hH
  · exact SmallEvenMaximalLower.Node10.classify H hH
  · exact SmallEvenMaximalLower.Node11.classify H hH
  · exact SmallEvenMaximalLower.Node12.classify H hH
  · exact SmallEvenMaximalLower.Node13.classify H hH
  · exact SmallEvenMaximalLower.Node14.classify H hH
  · exact SmallEvenMaximalLower.Node15.classify H hH
  · exact SmallEvenMaximalLower.Node16.classify H hH
  · exact SmallEvenMaximalLower.Node17.classify H hH
  · exact SmallEvenMaximalLower.Node18.classify H hH
  · exact SmallEvenMaximalLower.Node19.classify H hH
  · exact SmallEvenMaximalLower.Node20.classify H hH
  · exact SmallEvenMaximalLower.Node21.classify H hH
  · exact SmallEvenMaximalLower.Node22.classify H hH
  · exact SmallEvenMaximalLower.Node23.classify H hH
  · exact SmallEvenMaximalLower.Node24.classify H hH
  · exact SmallEvenMaximalLower.Node25.classify H hH
  · exact SmallEvenMaximalLower.Node26.classify H hH
  · exact SmallEvenMaximalLower.Node27.classify H hH
  · exact SmallEvenMaximalLower.Node28.classify H hH
  · exact SmallEvenMaximalLower.Node29.classify H hH
  · exact SmallEvenMaximalLower.Node30.classify H hH
  · exact SmallEvenMaximalLower.Node31.classify H hH
  · exact SmallEvenMaximalLower.Node32.classify H hH
  · exact SmallEvenMaximalLower.Node33.classify H hH
  · exact SmallEvenMaximalLower.Node34.classify H hH
  · exact SmallEvenMaximalLower.Node35.classify H hH
  · exact SmallEvenMaximalLower.Node36.classify H hH
  · exact SmallEvenMaximalLower.Node37.classify H hH
  · exact SmallEvenMaximalLower.Node38.classify H hH
  · exact SmallEvenMaximalLower.Node39.classify H hH
  · exact SmallEvenMaximalLower.Node40.classify H hH
  · exact SmallEvenMaximalLower.Node41.classify H hH
  · exact SmallEvenMaximalLower.Node42.classify H hH
  · exact SmallEvenMaximalLower.Node43.classify H hH
  · exact SmallEvenMaximalLower.Node44.classify H hH
  · exact SmallEvenMaximalLower.Node45.classify H hH
  · exact SmallEvenMaximalLower.Node46.classify H hH
  · exact SmallEvenMaximalLower.Node47.classify H hH
  · exact SmallEvenMaximalLower.Node48.classify H hH
  · exact SmallEvenMaximalLower.Node49.classify H hH
  · exact SmallEvenMaximalLower.Node50.classify H hH
  · exact SmallEvenMaximalLower.Node51.classify H hH
  · exact SmallEvenMaximalLower.Node52.classify H hH
  · exact SmallEvenMaximalLower.Node53.classify H hH
  · exact SmallEvenMaximalLower.Node54.classify H hH
  · exact SmallEvenMaximalLower.Node55.classify H hH
  · exact SmallEvenMaximalLower.Node56.classify H hH
  · exact SmallEvenMaximalLower.Node57.classify H hH
  · exact SmallEvenMaximalLower.Node58.classified H hH
  · exact SmallEvenMaximalLower.Node59.classified H hH
  · exact SmallEvenMaximalLower.Node60.classified H hH
  · exact SmallEvenMaximalLower.Node61.classified H hH
  · exact SmallEvenMaximalLower.Node62.classify H hH
  · exact SmallEvenMaximalLower.Node63.classified H hH
  · exact SmallEvenMaximalLower.Node64.classify H hH
  · exact SmallEvenMaximalLower.Node65.classify H hH
  · exact SmallEvenMaximalLower.Node66.classify H hH
  · exact SmallEvenMaximalLower.Node67.classify H hH
  · exact SmallEvenMaximalLower.Node68.classify H hH
  · exact SmallEvenMaximalLower.Node69.classify H hH
  · exact SmallEvenMaximalLower.Node70.classify H hH
  · exact SmallEvenMaximalLower.Node71.classify H hH
  · exact SmallEvenMaximalLower.Node72.classify H hH
  · exact SmallEvenMaximalLower.Node73.classify H hH
  · exact SmallEvenMaximalLower.Node74.classify H hH
  · exact SmallEvenMaximalLower.Node75.classify H hH
  · exact SmallEvenMaximalLower.Node76.classify H hH
  · exact SmallEvenMaximalLower.Node77.classify H hH
  · exact SmallEvenMaximalLower.Node78.classify H hH
  · exact SmallEvenMaximalLower.Node79.classify H hH
  · exact SmallEvenMaximalLower.Node80.classify H hH
  · exact SmallEvenMaximalLower.Node81.classified H hH
  · exact SmallEvenMaximalLower.Node82.classify H hH
  · exact SmallEvenMaximalLower.Node83.classified H hH
  · exact SmallEvenMaximalLower.Node84.classify H hH
  · exact SmallEvenMaximalLower.Node85.classify H hH
  · exact SmallEvenMaximalLower.Node86.classify H hH
  · exact SmallEvenMaximalLower.Node87.classify H hH
  · exact SmallEvenMaximalLower.Node88.classify H hH
  · exact SmallEvenMaximalLower.Node89.classify H hH
  · exact SmallEvenMaximalLower.Node90.classify H hH
  · exact SmallEvenMaximalLower.Node91.classify H hH
  · exact SmallEvenMaximalLower.Node92.classify H hH
  · exact SmallEvenMaximalLower.Node93.classify H hH
  · exact SmallEvenMaximalLower.Node94.classify H hH
  · exact SmallEvenMaximalLower.Node95.classified H hH
  · exact SmallEvenMaximalLower.Node96.classified H hH
  · exact SmallEvenMaximalLower.Node97.classify H hH
  · exact SmallEvenMaximalLower.Node98.classify H hH
  · exact SmallEvenMaximalLower.Node99.classified H hH
  · exact SmallEvenMaximalLower.Node100.classify H hH
  · exact SmallEvenMaximalLower.Node101.classify H hH
  · exact SmallEvenMaximalLower.Node102.classify H hH
  · exact SmallEvenMaximalLower.Node103.classify H hH
  · exact SmallEvenMaximalLower.Node104.classify H hH
  · exact SmallEvenMaximalLower.Node105.classified H hH
  · exact SmallEvenMaximalLower.Node106.classified H hH
  · exact SmallEvenMaximalLower.Node107.classified H hH
  · exact SmallEvenMaximalLower.Node108.classify H hH
  · exact SmallEvenMaximalLower.Node109.classified H hH
  · exact SmallEvenMaximalLower.Node110.classified H hH
  · exact SmallEvenMaximalLower.Node111.classify H hH
  · exact SmallEvenMaximalLower.Node112.classified H hH
  · exact SmallEvenMaximalLower.Node113.classify H hH
  · exact SmallEvenMaximalLower.Node114.classified H hH
  · exact SmallEvenMaximalLower.Node115.classify H hH
  · exact SmallEvenMaximalLower.Node116.classify H hH
  · exact SmallEvenMaximalLower.Node117.classify H hH
  · exact SmallEvenMaximalLower.Node118.classify H hH
  · exact SmallEvenMaximalLower.Node119.classified H hH
  · exact SmallEvenMaximalLower.Node120.classify H hH
  · exact SmallEvenMaximalLower.Node121.classify H hH
  · exact SmallEvenMaximalLower.Node122.classify H hH
  · exact SmallEvenMaximalLower.Node123.classify H hH
  · exact SmallEvenMaximalLower.Node124.classify H hH
  · exact SmallEvenMaximalLower.Node125.classify H hH
  · exact SmallEvenMaximalLower.Node126.classify H hH
  · exact SmallEvenMaximalLower.Node127.classify H hH
  · exact SmallEvenMaximalLower.Node128.classify H hH
  · exact SmallEvenMaximalLower.Node129.classify H hH
  · exact SmallEvenMaximalLower.Node130.classify H hH
  · exact SmallEvenMaximalLower.Node131.classified H hH
  · exact SmallEvenMaximalLower.Node132.classified H hH
  · exact SmallEvenMaximalLower.Node133.classify H hH
  · exact SmallEvenMaximalLower.Node134.classify H hH
  · exact SmallEvenMaximalLower.Node135.classify H hH
  · exact SmallEvenMaximalLower.Node136.classify H hH
  · exact SmallEvenMaximalLower.Node137.classify H hH
  · exact SmallEvenMaximalLower.Node138.classify H hH
  · exact SmallEvenMaximalLower.Node139.classify H hH
  · exact SmallEvenMaximalLower.Node140.classify H hH
  · exact SmallEvenMaximalLower.Node141.classified H hH
  · exact SmallEvenMaximalLower.Node142.classify H hH
  · exact SmallEvenMaximalLower.Node143.classified H hH
  · exact SmallEvenMaximalLower.Node144.classify H hH
  · exact SmallEvenMaximalLower.Node145.classify H hH
  · exact SmallEvenMaximalLower.Node146.classify H hH
  · exact SmallEvenMaximalLower.Node147.classify H hH
  · exact SmallEvenMaximalLower.Node148.classify H hH
  · exact SmallEvenMaximalLower.Node149.classified H hH
  · exact SmallEvenMaximalLower.Node150.classified H hH
  · exact SmallEvenMaximalLower.Node151.classified H hH
  · exact SmallEvenMaximalLower.Node152.classified H hH
  · exact SmallEvenMaximalLower.Node153.classified H hH
  · exact SmallEvenMaximalLower.Node154.classified H hH
  · exact SmallEvenMaximalLower.Node155.classify H hH
  · exact SmallEvenMaximalLower.Node156.classify H hH
  · exact SmallEvenMaximalLower.Node157.classify H hH
  · exact SmallEvenMaximalLower.Node158.classify H hH
  · exact SmallEvenMaximalLower.Node159.classified H hH
  · exact SmallEvenMaximalLower.Node160.classify H hH
  · exact SmallEvenMaximalLower.Node161.classified H hH
  · exact SmallEvenMaximalLower.Node162.classified H hH
  · exact SmallEvenMaximalLower.Node163.classified H hH
  · exact SmallEvenMaximalLower.Node164.classified H hH
  · exact SmallEvenMaximalLower.Node165.classified H hH
  · exact SmallEvenMaximalLower.Node166.classify H hH
  · exact SmallEvenMaximalLower.Node167.classify H hH
  · exact SmallEvenMaximalLower.Node168.classified H hH
  · exact SmallEvenMaximalLower.Node169.classified H hH
  · exact SmallEvenMaximalLower.Node170.classified H hH
  · exact SmallEvenMaximalLower.Node171.classified H hH
  · exact SmallEvenMaximalLower.Node172.classified H hH
  · exact SmallEvenMaximalLower.Node173.classified H hH
  · exact SmallEvenMaximalLower.Node174.classified H hH
  · exact SmallEvenMaximalLower.Node175.classified H hH
  · exact SmallEvenMaximalLower.Node176.classified H hH
  · exact SmallEvenMaximalLower.Node177.classified H hH
  · exact SmallEvenMaximalLower.Node178.classified H hH
  · exact SmallEvenMaximalLower.Node179.classified H hH
  · exact SmallEvenMaximalLower.Node180.classify H hH
  · exact SmallEvenMaximalLower.Node181.classify H hH
  · exact SmallEvenMaximalLower.Node182.classified H hH
  · exact SmallEvenMaximalLower.Node183.classified H hH
  · exact SmallEvenMaximalLower.Node184.classified H hH
  · exact SmallEvenMaximalLower.Node185.classified H hH
  · exact SmallEvenMaximalLower.Node186.classified H hH
  · exact SmallEvenMaximalLower.Node187.classified H hH
  · exact SmallEvenMaximalLower.Node188.classified H hH
  · exact SmallEvenMaximalLower.Node189.classified H hH
  · exact SmallEvenMaximalLower.Node190.classified H hH
  · exact SmallEvenMaximalLower.Node191.classified H hH
  · exact SmallEvenMaximalLower.Node192.classified H hH
  · exact SmallEvenMaximalLower.Node193.classified H hH
  · exact SmallEvenMaximalLower.Node194.classified H hH
  · exact SmallEvenMaximalLower.Node195.classified H hH
  · exact SmallEvenMaximalLower.Node196.classified H hH
  · exact SmallEvenMaximalLower.Node197.classified H hH
  · exact SmallEvenMaximalLower.Node198.classified H hH
  · exact SmallEvenMaximalLower.Node199.classified H hH
  · exact SmallEvenMaximalLower.Node200.classified H hH
  · exact SmallEvenMaximalLower.Node201.classified H hH
  · exact SmallEvenMaximalLower.Node202.classified H hH
  · exact SmallEvenMaximalLower.Node203.classified H hH
  · exact SmallEvenMaximalLower.Node204.classify H hH
  · exact SmallEvenMaximalLower.Node205.classified H hH
  · exact SmallEvenMaximalLower.Node206.classified H hH
  · exact SmallEvenMaximalLower.Node207.classify H hH
  · exact SmallEvenMaximalLower.Node208.classify H hH
  · exact SmallEvenMaximalLower.Node209.classify H hH
  · exact SmallEvenMaximalLower.Node210.classified H hH
  · exact SmallEvenMaximalLower.Node211.classified H hH
  · exact SmallEvenMaximalLower.Node212.classified H hH
  · exact SmallEvenMaximalLower.Node213.classified H hH
  · exact SmallEvenMaximalLower.Node214.classified H hH
  · exact SmallEvenMaximalLower.Node215.classified H hH
  · exact SmallEvenMaximalLower.Node216.classified H hH
  · exact SmallEvenMaximalLower.Node217.classified H hH
  · exact SmallEvenMaximalLower.Node218.classified H hH
  · exact SmallEvenMaximalLower.Node219.classified H hH
  · exact SmallEvenMaximalLower.Node220.classified H hH
  · exact SmallEvenMaximalLower.Node221.classified H hH
  · exact SmallEvenMaximalLower.Node222.classified H hH
  · exact SmallEvenMaximalLower.Node223.classified H hH
  · exact SmallEvenMaximalLower.Node224.classified H hH
  · exact SmallEvenMaximalLower.Node225.classified H hH
  · exact SmallEvenMaximalLower.Node226.classified H hH
  · exact SmallEvenMaximalLower.Node227.classified H hH
  · exact SmallEvenMaximalLower.Node228.classified H hH
  · exact SmallEvenMaximalLower.Node229.classified H hH
  · exact SmallEvenMaximalLower.Node230.classified H hH
  · exact SmallEvenMaximalLower.Node231.classified H hH
  · exact SmallEvenMaximalLower.Node232.classified H hH
  · exact SmallEvenMaximalLower.Node233.classified H hH
  · exact SmallEvenMaximalLower.Node234.classified H hH
  · exact SmallEvenMaximalLower.Node235.classified H hH
  · exact SmallEvenMaximalLower.Node236.classified H hH
  · exact SmallEvenMaximalLower.Node237.classify H hH
  · exact SmallEvenMaximalLower.Node238.classified H hH
  · exact SmallEvenMaximalLower.Node239.classified H hH
  · exact SmallEvenMaximalLower.Node240.classified H hH
  · exact SmallEvenMaximalLower.Node241.classified H hH
  · exact SmallEvenMaximalLower.Node242.classify H hH
  · exact SmallEvenMaximalLower.Node243.classified H hH
  · exact SmallEvenMaximalLower.Node244.classified H hH
  · exact SmallEvenMaximalLower.Node245.classified H hH
  · exact SmallEvenMaximalLower.Node246.classified H hH
  · exact SmallEvenMaximalLower.Node247.classify H hH
  · exact SmallEvenMaximalLower.Node248.classify H hH
  · exact SmallEvenMaximalLower.Node249.classified H hH
  · exact SmallEvenMaximalLower.Node250.classified H hH
  · exact SmallEvenMaximalLower.Node251.classify H hH
  · exact SmallEvenMaximalLower.Node252.classify H hH
  · exact SmallEvenMaximalLower.Node253.classify H hH
  · exact SmallEvenMaximalLower.Node254.classify H hH
  · exact SmallEvenMaximalLower.Node255.classify H hH
  · exact SmallEvenMaximalLower.Node256.classify H hH
  · exact SmallEvenMaximalLower.Node257.classify H hH
  · exact SmallEvenMaximalLower.Node258.classify H hH
  · exact SmallEvenMaximalLower.Node259.classify H hH
  · exact SmallEvenMaximalLower.Node260.classify H hH
  · exact SmallEvenMaximalLower.Node261.classified H hH
  · exact SmallEvenMaximalLower.Node262.classify H hH
  · exact SmallEvenMaximalLower.Node263.classify H hH
  · exact SmallEvenMaximalLower.Node264.classified H hH
  · exact SmallEvenMaximalLower.Node265.classify H hH
  · exact SmallEvenMaximalLower.Node266.classify H hH
  · exact SmallEvenMaximalLower.Node267.classified H hH
  · exact SmallEvenMaximalLower.Node268.classify H hH
  · exact SmallEvenMaximalLower.Node269.classified H hH
  · exact SmallEvenMaximalLower.Node270.classified H hH
  · exact SmallEvenMaximalLower.Node271.classify H hH
  · exact SmallEvenMaximalLower.Node272.classified H hH
  · exact SmallEvenMaximalLower.Node273.classified H hH
  · exact SmallEvenMaximalLower.Node274.classified H hH
  · exact SmallEvenMaximalLower.Node275.classified H hH
  · exact SmallEvenMaximalLower.Node276.classified H hH
  · exact SmallEvenMaximalLower.Node277.classify H hH
  · exact SmallEvenMaximalLower.Node278.classified H hH
  · exact SmallEvenMaximalLower.Node279.classify H hH
  · exact SmallEvenMaximalLower.Node280.classified H hH
  · exact SmallEvenMaximalLower.Node281.classify H hH
  · exact SmallEvenMaximalLower.Node282.classified H hH
  · exact SmallEvenMaximalLower.Node283.classified H hH
  · exact SmallEvenMaximalLower.Node284.classified H hH
  · exact SmallEvenMaximalLower.Node285.classified H hH
  · exact SmallEvenMaximalLower.Node286.classified H hH
  · exact SmallEvenMaximalLower.Node287.classified H hH
  · exact SmallEvenMaximalLower.Node288.classified H hH
  · exact SmallEvenMaximalLower.Node289.classified H hH
  · exact SmallEvenMaximalLower.Node290.classified H hH
  · exact SmallEvenMaximalLower.Node291.classify H hH
  · exact SmallEvenMaximalLower.Node292.classify H hH
  · exact SmallEvenMaximalLower.Node293.classified H hH
  · exact SmallEvenMaximalLower.Node294.classified H hH
  · exact SmallEvenMaximalLower.Node295.classified H hH
  · exact SmallEvenMaximalLower.Node296.classified H hH
  · exact SmallEvenMaximalLower.Node297.classify H hH
  · exact SmallEvenMaximalLower.Node298.classified H hH
  · exact SmallEvenMaximalLower.Node299.classified H hH

/-- The maximal-subgroup trichotomy for the original node rows zero through 299. -/
public theorem smallEvenMaximalClassification_lower (i : Fin 600) (hi : i.val < 300)
    (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode i) :
    H ≤ coreCharacter.ker ∨
      (∃ c, c ∈ Subgroup.centralizer (H : Set SylowModel) ∧ c ∉ H) ∨
      (∃ e : Fin 3617, H = SmallEvenDescentEdges.edge e) :=
  classify_lower_fin ⟨i.val, hi⟩ H hH

end ReeTwo.SylowModel
