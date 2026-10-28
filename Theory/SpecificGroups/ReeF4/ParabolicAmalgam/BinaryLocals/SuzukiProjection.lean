module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.SplitFactorization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.Radicals
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.GroupTheory.Complement

/-!
# The binary Ree Suzuki projection

The root-defined Levi and radical are both stable under the exceptional twist.
Unique split Levi–radical factorization forces each factor
of a fixed element to be fixed. Relative normality then gives a homomorphism
onto the fixed Levi with exactly the specified root radical as kernel. A
matrix identification of that Levi with Sz(2) yields the desired projection;
its section is inclusion of the identified fixed Levi.

The split root calculations prove complementarity and relative normality, and
the faithful four-dimensional action identifies the entire fixed Levi with
the concrete Suzuki matrix group. These discharge all premises of the retained
conditional construction and give the unconditional `projection`, its
surjectivity, exact kernel, and fixed-Levi section. Source:
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 (PDF pp.274–275) of
`refs/quasithin.pdf`. The ambient fixed group is the full ²F₄(2), and the
matrix target is Sz(2), not the D₁₀ quotient in the separate Tits-group case.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.BinarySuzuki
open LargeLocalSeeds Subgroup

/-- The radical inside the fixed seed is the exact inverse image of the split radical. -/
theorem radicalInSeed_eq_comap :
    radicalInSeed 0 .suzuki = splitRadicalInSeed.comap toSplitSeed := rfl

/-- Relative normality in the split seed descends to the fixed seed. -/
theorem radical_normal (h : splitRadicalInSeed.Normal) :
    (radicalInSeed 0 .suzuki).Normal := h.comap toSplitSeed

/-- Unique split factorization forces both factors of a fixed element to be fixed. -/
theorem fixed_complement
    (h : splitLeviInSeed.IsComplement' splitRadicalInSeed) :
    leviInSeed.IsComplement' (radicalInSeed 0 .suzuki) := by
  apply isComplement_iff_existsUnique.mpr
  intro x
  obtain ⟨⟨a, b⟩, hab, hu⟩ := h.existsUnique (toSplitSeed x)
  have hab' : a.val.val * b.val.val = toSplitGroup 0 x.val :=
    congrArg (fun y : splitSeed 0 .suzuki => y.val) hab
  let a' : splitLeviInSeed :=
    ⟨⟨reeTwist 0 a.val.val, splitLevi_le_seed (splitLevi_twist_mem a.property)⟩,
      splitLevi_twist_mem a.property⟩
  let b' : splitRadicalInSeed :=
    ⟨⟨reeTwist 0 b.val.val, (splitRadical_le_unipotent 0 .suzuki).trans
      (splitUnipotent_le_splitSeed 0 .suzuki) (splitRadical_twist_mem b.property)⟩,
      splitRadical_twist_mem b.property⟩
  have ht : a'.val * b'.val = toSplitSeed x := by
    apply Subtype.ext
    change reeTwist 0 a.val.val * reeTwist 0 b.val.val = toSplitGroup 0 x.val
    rw [← map_mul, hab', reeTwist_toSplitGroup]
  have he := hu (a', b') ht
  have ha : reeTwist 0 a.val.val = a.val.val :=
    congrArg (fun p : splitLeviInSeed × splitRadicalInSeed => p.1.val.val) he
  have hb : reeTwist 0 b.val.val = b.val.val :=
    congrArg (fun p : splitLeviInSeed × splitRadicalInSeed => p.2.val.val) he
  let af : leviInSeed :=
    ⟨⟨⟨a.val.val, (mem_fixedSubgroup 0 _).mpr ha⟩, by
      simpa only [seed, mem_comap, toSplitGroup_apply] using a.val.property⟩, by
      simpa only [SetLike.mem_coe, leviInSeed, levi, splitLeviInSeed, mem_subgroupOf, mem_comap,
        toSplitGroup_apply]
        using a.property⟩
  let bf : radicalInSeed 0 .suzuki :=
    ⟨⟨⟨b.val.val, (mem_fixedSubgroup 0 _).mpr hb⟩, by
      simpa only [seed, mem_comap, toSplitGroup_apply] using b.val.property⟩, by
      simpa only [SetLike.mem_coe, radicalInSeed, radical, splitRadicalInSeed, mem_subgroupOf, mem_comap,
        toSplitGroup_apply]
        using b.property⟩
  refine ⟨(af, bf), ?_, ?_⟩
  · apply Subtype.ext
    apply toSplitGroup_injective 0
    change toSplitGroup 0 (af.val.val * bf.val.val) = toSplitGroup 0 x.val
    rw [map_mul]
    simpa only [toSplitGroup_apply] using hab'
  · rintro ⟨c, d⟩ hcd
    let cs : splitLeviInSeed := ⟨toSplitSeed c.val, c.property⟩
    let ds : splitRadicalInSeed := ⟨toSplitSeed d.val, d.property⟩
    have hc : cs.val * ds.val = toSplitSeed x := by
      exact (map_mul toSplitSeed c.val d.val).symm.trans (congrArg toSplitSeed hcd)
    have hu' := hu (cs, ds) hc
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have he : toSplitGroup 0 c.val.val = a.val.val :=
        congrArg (fun p : splitLeviInSeed × splitRadicalInSeed => p.1.val.val) hu'
      simpa only [toSplitGroup_apply] using he
    · apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have he : toSplitGroup 0 d.val.val = b.val.val :=
        congrArg (fun p : splitLeviInSeed × splitRadicalInSeed => p.2.val.val) hu'
      simpa only [toSplitGroup_apply] using he

variable (h : splitLeviInSeed.IsComplement' splitRadicalInSeed)
    (hN : splitRadicalInSeed.Normal)
    (e : leviInSeed ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)

/-- The projection supplied by split factorization and a concrete fixed-Levi identification. -/
def projectionOfLeviFactorization : seed 0 .suzuki →*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 := by
  let := radical_normal hN
  exact e.toMonoidHom.comp
    ((fixed_complement h).QuotientMulEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (radicalInSeed 0 .suzuki)))

theorem projectionOfLeviFactorization_surjective :
    Function.Surjective (projectionOfLeviFactorization h hN e) := by
  let := radical_normal hN
  exact e.surjective.comp
    ((fixed_complement h).QuotientMulEquiv.surjective.comp
      (QuotientGroup.mk'_surjective (radicalInSeed 0 .suzuki)))

theorem projectionOfLeviFactorization_ker :
    (projectionOfLeviFactorization h hN e).ker = radicalInSeed 0 .suzuki := by
  let := radical_normal hN
  ext x
  change e ((fixed_complement h).QuotientMulEquiv
    (QuotientGroup.mk' (radicalInSeed 0 .suzuki) x)) = 1 ↔ x ∈ radicalInSeed 0 .suzuki
  rw [map_eq_one_iff _ e.injective,
    map_eq_one_iff _ (fixed_complement h).QuotientMulEquiv.injective]
  exact QuotientGroup.eq_one_iff x

theorem projectionOfLeviFactorization_levi (x : leviInSeed) :
    projectionOfLeviFactorization h hN e x.val = e x := by
  let := radical_normal hN
  change e ((fixed_complement h).QuotientMulEquiv
    (QuotientGroup.mk' (radicalInSeed 0 .suzuki) x.val)) = e x
  exact congrArg e ((fixed_complement h).QuotientMulEquiv.apply_symm_apply x)

/-- Include the fixed Levi after applying the inverse matrix identification. -/
def sectionOfLeviEquiv : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 →* seed 0 .suzuki :=
  leviInSeed.subtype.comp e.symm.toMonoidHom

theorem projectionOfLeviFactorization_section (x : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    projectionOfLeviFactorization h hN e (sectionOfLeviEquiv e x) = x := by
  rw [show sectionOfLeviEquiv e x = (e.symm x).val from rfl,
    projectionOfLeviFactorization_levi, e.apply_symm_apply]

/-- The binary Suzuki seed in the full Ree group projects onto the actual Sz(2) matrices. -/
def projection : seed 0 .suzuki →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  projectionOfLeviFactorization splitLeviInSeed_isComplement
    splitRadicalInSeed_normal leviMatrixEquiv

/-- Every Suzuki matrix lifts through the identified fixed middle-node Levi. -/
theorem projection_surjective : Function.Surjective projection :=
  projectionOfLeviFactorization_surjective splitLeviInSeed_isComplement
    splitRadicalInSeed_normal leviMatrixEquiv

/-- The kernel is exactly the specified positive-root radical inside the fixed seed. -/
theorem projection_ker : projection.ker = radicalInSeed 0 .suzuki :=
  projectionOfLeviFactorization_ker splitLeviInSeed_isComplement
    splitRadicalInSeed_normal leviMatrixEquiv

/-- On the fixed Levi, the projection is its concrete matrix identification. -/
@[simp] theorem projection_levi (x : leviInSeed) :
    projection x.val = leviMatrixEquiv x :=
  projectionOfLeviFactorization_levi splitLeviInSeed_isComplement
    splitRadicalInSeed_normal leviMatrixEquiv x

/-- Include the actual Suzuki matrices into the seed through the fixed Levi. -/
def leviSection : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 →* seed 0 .suzuki :=
  sectionOfLeviEquiv leviMatrixEquiv

/-- The fixed Levi provides a section of the binary Suzuki projection. -/
@[simp] theorem projection_leviSection (x : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    projection (leviSection x) = x :=
  projectionOfLeviFactorization_section splitLeviInSeed_isComplement
    splitRadicalInSeed_normal leviMatrixEquiv x

end ReeF4.Parabolics.BinarySuzuki
