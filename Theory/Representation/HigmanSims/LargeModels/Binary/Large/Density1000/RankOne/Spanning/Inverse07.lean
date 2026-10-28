module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Checks

/-! Bounded block 7 of the literal Krylov inverse certificate. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

theorem inverse07 : On 875 1000 InverseCheck := by
  exact On.of_fin 875 125 (by decide +kernel)

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
