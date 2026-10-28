module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Abelian.Outer
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Abelian.Elementary

/-!
# Small abelian centralizers in the actual second-transfer quotient

The elementary-point calculation gives C_Y(k)=F for k in F outside Z(Y).
The outside branch bounds the pair normalizer by order 32; its image in
Y/⟨v⟩ therefore has order at most 16. A central subgroup of order eight
makes that image abelian. All maps are the literal transfer inclusions and
the quotient by the supplied central involution.

The conditional adapters remain available, while `quotientLocalCentralizer_small`
discharges their elementary-point premise.

Source: Parrott (1972), Lemma 8, printed pp.682–683, observation (ii).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- The literal `hsmall` consumer, with only the two source calculations
left explicit. The elementary pair-normalizer equality is discharged here. -/
public theorem quotientLocalCentralizer_small_of_source_branches
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (helementary : ∀ k ∈ d.F, k ∉ t.sylowCenter →
      t.sylowImage ⊓ centralizer ({k} : Set G) ≤ d.F)
    (houter : ∀ k ∈ t.sylowImage, k ∉ d.F → k ^ 2 ∈ zpowers n.v →
      t.pairNormalizer k ≤ zpowers k ⊔ t.sylowCenter) :
    ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      IsMulCommutative (t.quotientLocalCentralizer x) ∧
        Nat.card (t.quotientLocalCentralizer x) ≤ 16 := by
  apply t.quotientLocalCentralizer_small_of_pair_normalizers ?_ houter
  intro k _hk hkZ hkF
  rw [t.pairNormalizer_eq_sylow_centralizer_of_mem_elementary h hlocal hkF hkZ]
  exact helementary k hkF hkZ

/-- The actual quotient local centralizers outside the central four-group
are abelian of order at most sixteen, with no remaining local premises. -/
public theorem quotientLocalCentralizer_small
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      IsMulCommutative (t.quotientLocalCentralizer x) ∧
        Nat.card (t.quotientLocalCentralizer x) ≤ 16 := by
  exact t.quotientLocalCentralizer_small_of_elementary_centralizers h hlocal
    (fun _ hkF hkZ => (t.sylowImage_elementary_point_centralizer h hlocal hkF hkZ).le)

end Stellmacher.Recognition.ParrottSecondTransferData
