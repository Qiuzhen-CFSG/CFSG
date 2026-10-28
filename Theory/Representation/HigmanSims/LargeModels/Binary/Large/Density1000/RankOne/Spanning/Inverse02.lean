module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Checks

/-! Bounded block 2 of the literal Krylov inverse certificate. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

theorem inverse02 : On 250 375 InverseCheck := by
  exact On.of_fin 250 125 (by decide +kernel)

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
