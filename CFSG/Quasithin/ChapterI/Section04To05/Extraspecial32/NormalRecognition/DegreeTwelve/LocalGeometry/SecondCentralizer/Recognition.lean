module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.Comparison
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.Transfer
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.FiveExtension

/-!
# Marked centralizer recognition from the local seed

The transfer-kernel contract implies A₄/A₅ recognition, including the actual
Sylow four-group and its cubic fusion. The A₄ branch gives its marked model
without further hypotheses. A compatible C₂ × S₅ extension completes the A₅
branch, and odd-index fusion supplies the full ambient marking.

Both transfers and the compatible A₅ extension are constructed by the imported
theorems. Thus `markedModels_of_localSeed` identifies the whole literal C_G(t)
with C₂ × S₄ or C₂ × S₅, preserving t and the complete ambient z-class.
The source assembly retains only the earlier construction of `LocalSeed`.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
variable {G : Type*} [Group G] [Finite G] {z t : G}

/-- Recognition and global marking from the transfer kernel and the remaining A₅ extension. -/
theorem markedModels_of_transferKernel (hz : orderOf z = 2)
    (s : LocalSeed z t) (d : TransferKernel s)
    (extend5 : (d.K ≃* alternatingGroup (Fin 5)) → Nonempty (LocalExtension s 5 (by decide))) :
    Nonempty (MarkedModel z t 4) ∨ Nonempty (MarkedModel z t 5) := by
  rcases d.alternating_four_or_five with h4 | h5
  · obtain ⟨e⟩ := h4
    exact Or.inl ⟨d.markedModel_four e⟩
  · obtain ⟨e⟩ := h5
    obtain ⟨c⟩ := extend5 e
    exact Or.inr ⟨c.markedModel hz⟩

/-- The local seed gives a marked model of the whole second centralizer.
The two transfers, A₄/A₅ recognition and compatible extension are all discharged. -/
theorem markedModels_of_localSeed (hz : orderOf z = 2) (_ht : orderOf t = 2)
    (_hnt : ¬ IsConj z t)
    (_hclasses : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x)
    (s : LocalSeed z t) :
    Nonempty (MarkedModel z t 4) ∨ Nonempty (MarkedModel z t 5) := by
  obtain ⟨d⟩ := nonempty_transferKernel s
  exact markedModels_of_transferKernel hz s d (FiveExtension.localExtension_of_marking d)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
