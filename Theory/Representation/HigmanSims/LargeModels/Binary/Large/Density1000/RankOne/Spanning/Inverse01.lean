module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Checks

/-! Bounded block 1 of the literal Krylov inverse certificate. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

theorem inverse01 : On 125 250 InverseCheck := by
  exact On.of_fin 125 125 (by decide +kernel)

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
