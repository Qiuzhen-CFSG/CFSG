module

public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRoots
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.ScalarRigidity
public import Theory.SpecificGroups.Triality.Model.QTKEParameters

/-!
# The central kernel of genuine triality in characteristic two

The center here is the center of the elementary subgroup of graph-field fixed
points. The fixed root elements constructed in `FixedRoots` turn centrality
into explicit commutation equations in the split Geck matrices. Two independent
matrix calculations make that center trivial: `FixedRootCommutant` proves that
the commutant of these fixed roots is scalar, and `ScalarRigidity` proves that
the generated split group contains no nonidentity scalar matrix. This includes
the binary parameter q = 2.

Consequently the central kernel lies in the split Borel and is disjoint from
the elementary positive subgroup. The actual quotient map is injective,
preserves the positive subgroup's cardinality, and allows subgroup intersections
to descend. The earlier conditional reductions are retained; the unconditional
theorems discharge both matrix inputs using the actual fixed root elements.

Source: GLS3 Theorem 2.2.6 and the kernel paragraph in the proof of
Theorems 2.3.4–5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace Triality.Standard.ElementaryCentralKernel
open Parabolics
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
local instance : DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)) :=
  fun a b => instDecidableEqSum a b

/-- The genuine elementary positive subgroup before the central quotient. -/
abbrev elementaryPositive (P : Parameters) : Subgroup (ElementaryGroup P) :=
  (positiveSubgroup P).comap (elementaryInclusion P)

/-- Restriction of the actual central-quotient map to positive elements. -/
def positiveToCarrier (P : Parameters) : elementaryPositive P →* Carrier P :=
  (toCarrier P).comp (elementaryPositive P).subtype

private theorem restrict_injective_iff_disjoint_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (U : Subgroup G) :
    Function.Injective (f.comp U.subtype) ↔ Disjoint f.ker U := by
  rw [injective_iff_map_eq_one, disjoint_iff_inf_le]
  constructor
  · intro hi x hx
    have h : (f.comp U.subtype) ⟨x, hx.2⟩ = 1 := hx.1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hi ⟨x, hx.2⟩ h))
  · intro hd x hx
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hd ⟨hx, x.property⟩)

/-- The positive restriction is faithful exactly when the actual elementary
center is disjoint from the elementary positive subgroup. -/
theorem positiveToCarrier_injective_iff (P : Parameters) :
    Function.Injective (positiveToCarrier P) ↔
      Disjoint (Subgroup.center (ElementaryGroup P)) (elementaryPositive P) := by
  have hk : (toCarrier P).ker = Subgroup.center (ElementaryGroup P) := by
    ext x
    exact toCarrier_eq_one P x
  exact (restrict_injective_iff_disjoint_ker (toCarrier P) (elementaryPositive P)).trans
    (iff_of_eq (congrArg (fun K => Disjoint K (elementaryPositive P)) hk))

private theorem center_eq_bot_of_injective_of_le_comap {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (C : Subgroup H)
    (hc : Subgroup.center G ≤ C.comap f) (hC : C = ⊥) : Subgroup.center G = ⊥ := by
  apply bot_unique
  intro z hz
  have h : f z ∈ C := hc hz
  rw [hC, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (hf (h.trans f.map_one.symm))

private theorem kernel_control_of_center_eq_bot {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B : Subgroup H) (U : Subgroup G) (h : Subgroup.center G = ⊥) :
    (Subgroup.center G ≤ B.comap f) ∧ Disjoint (Subgroup.center G) U := by
  rw [h]
  exact ⟨bot_le, disjoint_bot_left⟩

/-- Matrix-centralizer comparison and split centerlessness imply elementary
centerlessness. Both matrix premises still have to be proved. -/
theorem center_eq_bot_of_fixedRootCentralizer_le_splitCenter
    (P : Parameters) (hp : P.prime = 2)
    (hcomparison : Subgroup.centralizer (fixedRootGenerators P) ≤
      Subgroup.center (SplitGroup P))
    (hsplit : Subgroup.center (SplitGroup P) = ⊥) :
    Subgroup.center (ElementaryGroup P) = ⊥ :=
  center_eq_bot_of_injective_of_le_comap (elementaryInclusion P)
    ((fixedSubgroup P).subtype_injective.comp (elementarySubgroup P).subtype_injective)
    (Subgroup.center (SplitGroup P))
    ((elementaryCenter_le_fixedRootCentralizer P hp).trans (Subgroup.comap_mono hcomparison))
    hsplit

/-- Conditional assembly of precisely the two central-kernel assertions used
by the parabolic geometry and positive cardinality consumers. -/
theorem kernel_control_of_fixedRootCentralizer_le_splitCenter
    (P : Parameters) (hp : P.prime = 2)
    (hcomparison : Subgroup.centralizer (fixedRootGenerators P) ≤
      Subgroup.center (SplitGroup P))
    (hsplit : Subgroup.center (SplitGroup P) = ⊥) :
    (Subgroup.center (ElementaryGroup P) ≤
      (splitBorel P).comap (elementaryInclusion P)) ∧
      Disjoint (Subgroup.center (ElementaryGroup P)) (elementaryPositive P) :=
  kernel_control_of_center_eq_bot (elementaryInclusion P) (splitBorel P) (elementaryPositive P)
    (center_eq_bot_of_fixedRootCentralizer_le_splitCenter P hp hcomparison hsplit)

/-- A scalar commutant calculation and scalar rigidity in the generated split
matrix group suffice. These independent matrix inputs do not assume elementary
centerlessness, and can be established without Bruhat or quotient geometry. -/
theorem center_eq_bot_of_fixedRoot_scalar
    (P : Parameters) (hp : P.prime = 2)
    (hscalar : ∀ g ∈ Subgroup.centralizer (fixedRootGenerators P),
      ∃ c : ExtensionField P, g.val.val = c • 1)
    (hrigid : ∀ (g : SplitGroup P) (c : ExtensionField P),
      g.val.val = c • 1 → g = 1) :
    Subgroup.center (ElementaryGroup P) = ⊥ := by
  apply center_eq_bot_of_injective_of_le_comap (elementaryInclusion P)
    ((fixedSubgroup P).subtype_injective.comp (elementarySubgroup P).subtype_injective)
    (Subgroup.centralizer (fixedRootGenerators P))
    (elementaryCenter_le_fixedRootCentralizer P hp)
  apply bot_unique
  intro g hg
  obtain ⟨c, hc⟩ := hscalar g hg
  exact Subgroup.mem_bot.mpr (hrigid g c hc)

/-- The central-kernel conclusions from the two concrete matrix inputs. -/
theorem kernel_control_of_fixedRoot_scalar
    (P : Parameters) (hp : P.prime = 2)
    (hscalar : ∀ g ∈ Subgroup.centralizer (fixedRootGenerators P),
      ∃ c : ExtensionField P, g.val.val = c • 1)
    (hrigid : ∀ (g : SplitGroup P) (c : ExtensionField P),
      g.val.val = c • 1 → g = 1) :
    (Subgroup.center (ElementaryGroup P) ≤
      (splitBorel P).comap (elementaryInclusion P)) ∧
      Disjoint (Subgroup.center (ElementaryGroup P)) (elementaryPositive P) :=
  kernel_control_of_center_eq_bot (elementaryInclusion P) (splitBorel P) (elementaryPositive P)
    (center_eq_bot_of_fixedRoot_scalar P hp hscalar hrigid)

/-- Once the central kernel is disjoint, the positive subgroup keeps its
cardinality under the actual quotient. -/
theorem card_unipotent_of_disjoint (P : Parameters)
    (h : Disjoint (Subgroup.center (ElementaryGroup P)) (elementaryPositive P)) :
    Nat.card (unipotent P) = Nat.card (elementaryPositive P) := by
  have hr : (positiveToCarrier P).range = unipotent P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact (congrArg (fun H : Subgroup (Carrier P) => Nat.card H) hr).symm.trans
    (Nat.card_congr
      (MonoidHom.ofInjective ((positiveToCarrier_injective_iff P).mpr h)).toEquiv.symm)

/-- The elementary subgroup of genuine graph-field fixed points has trivial
center in characteristic two, including q = 2. Centrality is tested on the
actual elementary fixed roots before applying the two Geck matrix calculations. -/
theorem center_eq_bot (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (ElementaryGroup P) = ⊥ :=
  center_eq_bot_of_fixedRoot_scalar P hp
    (fixedRootCentralizer_is_scalar P hp) (split_eq_one_of_scalar P hp)

/-- The actual central kernel is contained in the split Borel upstairs. -/
theorem center_le_splitBorel (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (ElementaryGroup P) ≤
      (splitBorel P).comap (elementaryInclusion P) :=
  (center_eq_bot P hp).le.trans bot_le

/-- No nonidentity elementary positive element is killed by the central quotient. -/
theorem center_disjoint_elementaryPositive (P : Parameters) (hp : P.prime = 2) :
    Disjoint (Subgroup.center (ElementaryGroup P)) (elementaryPositive P) :=
  disjoint_bot_left.mono_left (center_eq_bot P hp).le

/-- Both central-kernel assertions, without additional matrix or geometry premises. -/
theorem kernel_control (P : Parameters) (hp : P.prime = 2) :
    (Subgroup.center (ElementaryGroup P) ≤
      (splitBorel P).comap (elementaryInclusion P)) ∧
      Disjoint (Subgroup.center (ElementaryGroup P)) (elementaryPositive P) :=
  ⟨center_le_splitBorel P hp, center_disjoint_elementaryPositive P hp⟩

/-- The binary specialization of the two kernel assertions, for every positive
field exponent, including n = 1. -/
theorem binary_kernel_control (n : ℕ) (hn : 0 < n) :
    let P := binaryParameters n hn
    (Subgroup.center (ElementaryGroup P) ≤
      (splitBorel P).comap (elementaryInclusion P)) ∧
      Disjoint (Subgroup.center (ElementaryGroup P))
        ((positiveSubgroup P).comap (elementaryInclusion P)) :=
  kernel_control (binaryParameters n hn) rfl

/-- The canonical central quotient is faithful on the whole elementary group
in characteristic two. -/
theorem toCarrier_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (toCarrier P) := by
  have hk : (toCarrier P).ker = Subgroup.center (ElementaryGroup P) := by
    ext g
    exact toCarrier_eq_one P g
  exact (toCarrier P).ker_eq_bot_iff.mp (hk.trans (center_eq_bot P hp))

/-- The actual quotient map is faithful on the elementary positive subgroup. -/
theorem positiveToCarrier_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (positiveToCarrier P) :=
  (positiveToCarrier_injective_iff P).mpr (center_disjoint_elementaryPositive P hp)

/-- The positive subgroup keeps its cardinality in the actual central quotient. -/
theorem card_unipotent (P : Parameters) (hp : P.prime = 2) :
    Nat.card (unipotent P) = Nat.card (elementaryPositive P) :=
  card_unipotent_of_disjoint P (center_disjoint_elementaryPositive P hp)

/-- Restriction to elementary fixed points and descent preserve intersections
in characteristic two; the former central-kernel premises are now discharged. -/
theorem descendSubgroup_inf (P : Parameters) (hp : P.prime = 2)
    (H K : Subgroup (SplitGroup P)) :
    descendSubgroup P (H ⊓ K) = descendSubgroup P H ⊓ descendSubgroup P K :=
  descendSubgroup_inf_of_center_le P H K
    ((center_eq_bot P hp).le.trans bot_le) ((center_eq_bot P hp).le.trans bot_le)

end
end Triality.Standard.ElementaryCentralKernel
