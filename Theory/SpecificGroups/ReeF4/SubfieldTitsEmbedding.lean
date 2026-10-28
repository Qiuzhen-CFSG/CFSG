module
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldMaps
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.MarkedModel

/-!
# A Tits subgroup in every concrete Ree group

The checked Parrott embedding lands in the binary exceptional fixed group.
The coefficient embedding from degree one commutes with the exceptional root
map, so the existing injective Ree subfield map carries it into every Model m.
This provides the actual subgroup embedding; no simplicity or order calculation
for Model m is needed.

Source: the subfield construction in Steinberg, Lectures on Chevalley Groups;
Parrott (1972), §5, p.683, for the checked presentation realization.
-/

public section
namespace ReeF4.Subfield

/-- The actual Parrott group embeds through the binary fixed matrices at every Ree parameter. -/
theorem exists_tits_embedding (m : ℕ) :
    ∃ f : Tits.ParrottGroup →* Model m, Function.Injective f := by
  obtain ⟨f⟩ := nonempty_coefficientHom (k := 0) (m := m) (by simp)
  let hdiv : (2 * 0 + 1) ∣ (2 * m + 1) := by simp
  exact ⟨(reeMap hdiv f).comp Tits.InvolutionRootGeometry.embedding,
    (reeMap_injective hdiv f).comp Tits.InvolutionRootGeometry.embedding_injective⟩

end ReeF4.Subfield
