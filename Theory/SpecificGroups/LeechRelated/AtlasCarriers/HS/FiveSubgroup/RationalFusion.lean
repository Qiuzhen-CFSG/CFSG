module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Theory.GroupTheory.PGroup.RationalExtraspecial

/-!
# The rational extraspecial five-subgroup of the actual HS carrier

The existing nonabelian subgroup of order 125 is extraspecial. Its explicit
commutator z is central and nonidentity. A word in the original ATLAS generators
conjugates z to z². Its powers therefore conjugate z to every nonidentity power.
Together these give the configuration forcing degree at least twenty in any
faithful characteristic-two representation.

All finite identities are checked in the kernel on the same degree-100 carrier.
The saved word is only a candidate certificate, not a computation oracle.
The internal `import all` continues the existing five-subgroup calculation,
allowing the proof to check its private packed tables without exposing them.
Sources: ATLAS HSG1-p100B0, with the generator provenance in the carrier module;
GLS3 Table 5.3m (the subgroup 5^(1+2)); Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, HS paragraph on author-preprint p.16.
-/

public section
namespace Sporadic.LeechRelated.HS.FiveSubgroup.RationalFusion
open Subgroup FiveSubgroup

private def cMap (i : Fin 100) : Fin 100 :=
  ⟨(891103430388409773674818334157872133642460663391504736617814914007585554474067132268434436570446794119792935388756596407452505334860125475873106449787753337480613895366495647163251223763392114795339258666870959 >>> (7 * i.val)) % 128 % 100,
    Nat.mod_lt _ (by decide)⟩

private def cInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3466462245086639293364110948314968447542832968709774062033075525825567994610524824769090212866710170477251020258355649826961880728433278592516577054858335698624240790722162855955337679544063352590268418884822938 >>> (7 * i.val)) % 128 % 100,
    Nat.mod_lt _ (by decide)⟩

private theorem cLeft : ∀ i, cInvMap (cMap i) = i := by
  apply allFin
  decide +kernel

private def cPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm cMap cInvMap cLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin cLeft)

private def conjugatorWord : Carrier :=
  b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 2) * a * b * a * b * a * (b ^ 2) * a * b⁻¹ * a * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2)

private theorem cPerm_eq_word : cPerm = (conjugatorWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def c : Carrier := ⟨cPerm, cPerm_eq_word.symm ▸ conjugatorWord.property⟩

private theorem conjugates_square : c * z * c⁻¹ = z ^ 2 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem x_commutes_z : x * z = z * x := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem y_commutes_z : y * z = z * y := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem z_pow_five : z ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem z_ne_one : z ≠ 1 := by
  intro h
  have he := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 0) h
  have hn : (z : Equiv.Perm (Fin 100)) 0 ≠ 0 := by decide +kernel
  exact hn he

private theorem z_mem_subgroup : z ∈ subgroup := by
  have hx : x ∈ subgroup := Subgroup.subset_closure (by simp)
  have hy : y ∈ subgroup := Subgroup.subset_closure (by simp)
  rw [z_eq_commutator]
  exact subgroup.mul_mem (subgroup.mul_mem
    (subgroup.mul_mem (subgroup.inv_mem hx) (subgroup.inv_mem hy)) hx) hy

private theorem z_mem_centralizer : z ∈ centralizer (subgroup : Set Carrier) := by
  change z ∈ centralizer (closure {x, y} : Set Carrier)
  rw [centralizer_closure]
  intro g hg
  rcases (show g = x ∨ g = y by simpa using hg) with rfl | rfl
  · exact x_commutes_z
  · exact y_commutes_z

private theorem conjugates_four : c ^ 2 * z * (c ^ 2)⁻¹ = z ^ 4 := by
  calc
    c ^ 2 * z * (c ^ 2)⁻¹ = c * (c * z * c⁻¹) * c⁻¹ := by
      simp only [pow_two, mul_inv_rev]
      group
    _ = c * z ^ 2 * c⁻¹ := by rw [conjugates_square]
    _ = (c * z * c⁻¹) ^ 2 := conj_pow.symm
    _ = z ^ 4 := by rw [conjugates_square, ← pow_mul]

private theorem conjugates_three : c ^ 3 * z * (c ^ 3)⁻¹ = z ^ 3 := by
  calc
    c ^ 3 * z * (c ^ 3)⁻¹ = c * (c ^ 2 * z * (c ^ 2)⁻¹) * c⁻¹ := by group
    _ = c * z ^ 4 * c⁻¹ := by rw [conjugates_four]
    _ = (c * z * c⁻¹) ^ 4 := conj_pow.symm
    _ = z ^ 8 := by rw [conjugates_square, ← pow_mul]
    _ = z ^ 3 := by
      rw [show (8 : ℕ) = 5 + 3 from rfl, pow_add, z_pow_five, one_mul]

/-- A nonidentity element of the center of the literal certified subgroup,
together with an ambient element conjugating it to its square. This preserves
the subgroup marking needed for fixed-space and multiplicity calculations. -/
theorem central_fusion :
    ∃ zP : subgroup, zP ∈ center subgroup ∧ zP ≠ 1 ∧
      ∃ g : Carrier, g * (zP : Carrier) * g⁻¹ = (zP : Carrier) ^ 2 := by
  refine ⟨⟨z, z_mem_subgroup⟩, ?_, ?_, c, conjugates_square⟩
  · apply Subgroup.mem_center_iff.mpr
    intro g
    exact Subtype.ext (z_mem_centralizer g g.property)
  · intro h
    exact z_ne_one (congrArg Subtype.val h)

/-- The literal order-125 subgroup and its rationally fused center, without
an assumed HS order, simplicity theorem, or alternative-model comparison. -/
theorem rational_five_subgroup : Theory.GroupTheory.HasRationalExtraspecialSubgroup Carrier 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let zP : subgroup := ⟨z, z_mem_subgroup⟩
  refine ⟨subgroup,
    IsExtraspecial.of_noncommutative_card_prime_cube card_subgroup subgroup_not_commutative,
    card_subgroup, zP, ?_, ?_, ?_⟩
  · apply Subgroup.mem_center_iff.mpr
    intro g
    exact Subtype.ext (z_mem_centralizer g g.property)
  · intro h
    exact z_ne_one (congrArg Subtype.val h)
  · intro i hi hip
    change ∃ g : Carrier, g * z * g⁻¹ = z ^ i
    interval_cases i
    · exact ⟨1, by simp⟩
    · exact ⟨c, conjugates_square⟩
    · exact ⟨c ^ 3, conjugates_three⟩
    · exact ⟨c ^ 2, conjugates_four⟩

end Sporadic.LeechRelated.HS.FiveSubgroup.RationalFusion
