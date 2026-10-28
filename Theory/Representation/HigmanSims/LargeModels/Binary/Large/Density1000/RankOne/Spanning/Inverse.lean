module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Inverse07

/-! The eight bounded blocks cover all rows of the candidate inverse. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

theorem all_inverse : On 0 1000 InverseCheck :=
  (((inverse00.append inverse01).append (inverse02.append inverse03)).append
    ((inverse04.append inverse05).append (inverse06.append inverse07)))

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
