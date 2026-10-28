module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Checks

/-! Bounded block 4 of the literal Krylov inverse certificate. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

theorem inverse04 : On 500 625 InverseCheck := by
  exact On.of_fin 500 125 (by decide +kernel)

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
