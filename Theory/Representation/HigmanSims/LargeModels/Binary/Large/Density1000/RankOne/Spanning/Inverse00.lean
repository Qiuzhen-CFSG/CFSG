module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Spanning.Checks

/-! The first bounded block of the literal Krylov inverse certificate. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

theorem inverse00 : On 0 125 InverseCheck := by
  exact On.of_fin 0 125 (by decide +kernel)

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
