module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.A6Source
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.SourceKernel

/-!
# The original A6 normalizer discharges the cubic-kernel section input

The actual elementary-plane normalizer supplies the A6 quotient used by
the order-nine exclusion. The independent reflected-actor producer retains
ownership of the only earlier binary-local witness in this consumer.
All quotient maps and the canonical odd kernel are those of the original
Sylow-three image in the involution centralizer.
Source: Aschbacher, Sporadic Groups (1994),45.6–45.7, pp.244–245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem reflected_kernel_of_source_binary_normalizers (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    IsElementaryAbelian 3 V ∧ Nat.card V=81 := by
  obtain ⟨M,f,hf⟩:=h.exists_A6_section
  exact h.reflected_kernel_from_A6_section P m M f hf
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
