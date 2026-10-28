module
public import Theory.SpecificGroups.SU3.OddInvolutionFixed
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank
import all Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import GorensteinWalter.SL2ProjectiveCover
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.SpecificGroups.PSL3.OddSylowCenter
/-!
# Outer unitary involutions cannot fix an SL₂ component

The fixed subgroup of an outer involution of odd-prime PSU₃ is the actual
ternary special orthogonal group. This group has the same order as SL₂(p),
but has a subgroup of index two. An injection from perfect SL₂(p), p>3,
would be surjective and make that index-two subgroup impossible. Thus no
outer involution fixes a genuine SL₂(p) component pointwise.

The adjoint subgroup is reused with its proved literal carrier and index;
no abstract orthogonal identification or rank table is assumed.
Source: Aschbacher–Smith A.3.21 and E.2.7, pp.55 and 219.
-/
public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
open OddPrimeSylow OddPrimeSylow.TernaryOrthogonal
variable {F:Type*} [Field F] [Finite F]
private theorem no_sl2_in_orthogonal {p:ℕ} [Fact p.Prime]
    (ho:Odd p) (hp:3<p) (hc:Nat.card F=p)
    (f:SL(2,ZMod p)→*(splitOrthogonalForm F).specialSubgroup) :
    ¬ Function.Injective f := by
  intro hf
  have h2: (2:F)≠0:=Field.two_ne_zero_of_odd_card F (hc ▸ ho)
  let : Group.IsPerfect SL(2,ZMod p):=GorensteinWalter.sl2_isPerfect_of_card_gt_three
    (ZMod p) (by simpa only [Nat.card_zmod] using hp)
  have hcard:Nat.card (splitOrthogonalForm F).specialSubgroup=Nat.card SL(2,ZMod p) := by
    rw [card_splitOrthogonal_specialSubgroup h2,hc,BenderSuzuki.External.huppert614_card_specialLinearGroup,Nat.card_zmod]
  have hsur:Function.Surjective f := hf.bijective_of_nat_card_le hcard.le |>.2
  let : Group.IsPerfect (splitOrthogonalForm F).specialSubgroup:=Group.IsPerfect.ofSurjective hsur
  let D:=(adjointHom h2).range
  have hD:D.index=2:=adjoint_range_index h2 (hc ▸ ho)
  have he:D=⊤:=top_unique (le_of_isPerfect_of_index_eq_two ⊤ D hD)
  rw [he,index_top] at hD
  omega

/-- No outer involution of the literal odd-prime PSU₃ model fixes a copy
of the actual SL₂(p) group pointwise. -/
theorem no_sl2_in_outer_fixed (J:HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hlarge:3<p)
    (hcard:Nat.card F=p^2) (hfixed:Nat.card {x:F // J.conj x=x}=p)
    (a:MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha:a^2=1) (houter:¬∃k,a=MulAut.conj k)
    (f:SL(2,ZMod p)→*a.fixedSubgroup) : ¬Function.Injective f := by
  let : Fact p.Prime:=⟨hp⟩
  obtain ⟨e⟩:=fixed_equiv_orthogonal J hp ho hcard hfixed a ha houter
  have hF:Nat.card (FixedBy.subfield F J.conj)=p := hfixed
  exact fun hf=>no_sl2_in_orthogonal ho hlarge hF (e.toMonoidHom.comp f) (e.injective.comp hf)
end BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
