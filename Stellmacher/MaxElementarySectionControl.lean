module
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Thompson control from a nonoffending invariant section

A maximum elementary subgroup acting nontrivially on a normal elementary
subgroup V is an offender on V. Fixed codimension cannot increase on an
invariant section. Consequently, when that section has no offenders in
the prescribed actor image, the elementary Thompson subgroup centralizes V.
The proof retains the full centralizer quotient and does not assume that
either invariant extension splits.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
B.2.4 and the orthogonal comparison after 13.6.23, printed pp.75–76, 933.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender
namespace Stellmacher
variable {G H N : Type*} [Group G] [Group H] [Finite G] [Finite H]
    [AddCommGroup N] [Module (ZMod 2) N]

/-- If an invariant section admits no offender in the image of S, then
every maximum elementary subgroup of S lies in the actual centralizer kernel.
The section need not split. -/
theorem maxJ_le_ker_of_nonoffending_section
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S : Subgroup G) (hVS : V ≤ S)
    (U W : Subrepresentation (Representation.NormalElementaryQuotient.representation V q hq hker))
    (σ : Representation (ZMod 2) H N)
    (e : (W.toSubmodule ⧸
      (sectionLower (Representation.NormalElementaryQuotient.representation V q hq hker) U W).toSubmodule)
      ≃ₗ[ZMod 2] N)
    (he : ∀ g w, e (sectionRepresentation
      (Representation.NormalElementaryQuotient.representation V q hq hker) U W g w) =
        σ g (e w))
    (hno : ∀ A ≤ S.map q, ¬ IsOffender σ A) :
    elementaryAbelianMaxJ S ≤ q.ker := by
  apply sSup_le
  intro A hA
  by_contra hn
  let ρ := Representation.NormalElementaryQuotient.representation V q hq hker
  have ho := Representation.NormalElementaryQuotient.maxElementary_isOffender V q hq hker S A hVS hA hn
  have hs : IsOffender (sectionRepresentation ρ U W) (A.map q) :=
    ⟨ho.1, (fixedCodim_section_le ρ U W (A.map q)).trans ho.2⟩
  have ht := hs.map_equivariant (sectionRepresentation ρ U W) σ
    (MonoidHom.id H) Function.injective_id e he
  rw [Subgroup.map_id] at ht
  exact hno (A.map q) (map_mono hA.1) ht

end Stellmacher
